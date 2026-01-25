/**
 * Checkpoint Implementation
 *
 * REQ-CP-001: Checkpoint Creation
 * REQ-CP-002: Checkpoint Verification
 * REQ-CP-003: Checkpoint Listing
 * REQ-CP-004: Checkpoint Restore
 * REQ-CP-005: Checkpoint Retention & Location
 *
 * @packageDocumentation
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import * as os from 'os';
import { exec } from 'child_process';
import { promisify } from 'util';
import {
  type CheckpointComparison,
  type CheckpointConfig,
  type CheckpointEntry,
  type CheckpointListEntry,
  type CheckpointManager,
  type CheckpointRestoreResult,
  type CheckpointStatus,
  DEFAULT_CHECKPOINT_CONFIG,
} from './types.js';

const execAsync = promisify(exec);

/**
 * Expand home directory in path
 */
function expandPath(filePath: string): string {
  if (filePath.startsWith('~')) {
    return path.join(os.homedir(), filePath.slice(1));
  }
  return filePath;
}

/**
 * Create checkpoint manager
 *
 * @param config - Configuration options
 * @param projectRoot - Project root directory
 * @returns CheckpointManager instance
 */
export function createCheckpointManager(
  config: Partial<CheckpointConfig> = {},
  projectRoot: string = '.'
): CheckpointManager {
  const fullConfig: CheckpointConfig = {
    ...DEFAULT_CHECKPOINT_CONFIG,
    ...config,
  };

  const checkpointsDir = expandPath(fullConfig.checkpointsDir);
  const logFile = expandPath(fullConfig.logFile);

  // In-memory cache
  const checkpoints = new Map<string, CheckpointEntry>();

  /**
   * Ensure directories exist
   */
  async function ensureDirectories(): Promise<void> {
    await fs.mkdir(checkpointsDir, { recursive: true });
  }

  /**
   * Load checkpoints from log file
   */
  async function loadCheckpoints(): Promise<void> {
    try {
      const content = await fs.readFile(logFile, 'utf-8');
      const lines = content.trim().split('\n').filter(Boolean);

      for (const line of lines) {
        // Format: YYYY-MM-DD-HH:MM | checkpoint_name | git_short_sha
        const [timestamp, name, sha] = line.split('|').map((s) => s.trim());
        if (timestamp && name && sha) {
          checkpoints.set(name, {
            name,
            timestamp: new Date(timestamp.replace(/-/g, ':')),
            gitSha: sha,
            gitShortSha: sha.slice(0, 7),
            verificationStatus: 'skipped',
            status: 'behind',
          });
        }
      }
    } catch {
      // File doesn't exist yet
    }
  }

  /**
   * Save checkpoint to log file
   */
  async function saveCheckpoint(entry: CheckpointEntry): Promise<void> {
    await ensureDirectories();

    const timestamp = entry.timestamp.toISOString().replace(/[T:]/g, '-').slice(0, 16);
    const line = `${timestamp} | ${entry.name} | ${entry.gitShortSha}\n`;

    await fs.appendFile(logFile, line);
    checkpoints.set(entry.name, entry);
  }

  /**
   * Get current git SHA
   */
  async function getCurrentSha(): Promise<{ full: string; short: string }> {
    try {
      const { stdout: full } = await execAsync('git rev-parse HEAD', {
        cwd: projectRoot,
      });
      const { stdout: short } = await execAsync('git rev-parse --short HEAD', {
        cwd: projectRoot,
      });
      return {
        full: full.trim(),
        short: short.trim(),
      };
    } catch {
      throw new Error('Git not available or not a git repository');
    }
  }

  /**
   * Check if there are uncommitted changes
   */
  async function hasUncommittedChanges(): Promise<boolean> {
    try {
      const { stdout } = await execAsync('git status --porcelain', {
        cwd: projectRoot,
      });
      return stdout.trim().length > 0;
    } catch {
      return false;
    }
  }

  /**
   * Run quick verification
   */
  async function runQuickVerification(): Promise<'passed' | 'failed'> {
    try {
      await execAsync('npm run typecheck 2>/dev/null || npx tsc --noEmit', {
        cwd: projectRoot,
        timeout: 60000,
      });
      return 'passed';
    } catch {
      return 'failed';
    }
  }

  /**
   * Get checkpoint status relative to current HEAD
   */
  async function getCheckpointStatus(
    checkpointSha: string
  ): Promise<CheckpointStatus> {
    try {
      const currentSha = await getCurrentSha();
      if (currentSha.full.startsWith(checkpointSha)) {
        return 'current';
      }

      const { stdout } = await execAsync(
        `git merge-base --is-ancestor ${checkpointSha} HEAD && echo "behind" || echo "ahead"`,
        { cwd: projectRoot }
      );
      return stdout.trim() === 'behind' ? 'behind' : 'ahead';
    } catch {
      return 'behind';
    }
  }

  // Initialize by loading existing checkpoints
  loadCheckpoints();

  return {
    async createCheckpoint(
      name: string,
      runVerification: boolean = true
    ): Promise<CheckpointEntry> {
      await ensureDirectories();

      // Check for uncommitted changes
      const hasChanges = await hasUncommittedChanges();
      if (hasChanges) {
        // Create a commit or stash
        try {
          await execAsync(`git stash push -m "checkpoint-${name}"`, {
            cwd: projectRoot,
          });
        } catch {
          // Stash might fail if nothing to stash
        }
      }

      // Run verification if requested
      let verificationStatus: 'passed' | 'failed' | 'skipped' = 'skipped';
      if (runVerification && fullConfig.autoVerify) {
        verificationStatus = await runQuickVerification();
      }

      // Get current SHA
      const sha = await getCurrentSha();

      const entry: CheckpointEntry = {
        name,
        timestamp: new Date(),
        gitSha: sha.full,
        gitShortSha: sha.short,
        verificationStatus,
        status: 'current',
        message: hasChanges ? 'Changes were stashed' : undefined,
      };

      await saveCheckpoint(entry);

      // Clean old checkpoints if needed
      await this.cleanOldCheckpoints();

      return entry;
    },

    async verifyCheckpoint(name: string): Promise<CheckpointComparison> {
      const checkpoint = checkpoints.get(name);
      if (!checkpoint) {
        throw new Error(`Checkpoint not found: ${name}`);
      }

      const currentSha = await getCurrentSha();

      try {
        const { stdout: diffStat } = await execAsync(
          `git diff --stat ${checkpoint.gitSha}..HEAD`,
          { cwd: projectRoot }
        );

        const lines = diffStat.trim().split('\n');
        const statsLine = lines[lines.length - 1] || '';

        const filesMatch = statsLine.match(/(\d+)\s*files?\s*changed/i);
        const addMatch = statsLine.match(/(\d+)\s*insertions?/i);
        const delMatch = statsLine.match(/(\d+)\s*deletions?/i);

        // Try to get test status
        let testsPassed: number | undefined;
        let testsTotal: number | undefined;
        let buildStatus: 'passing' | 'failing' | 'unknown' = 'unknown';

        try {
          const { stdout: testOutput } = await execAsync('npm test 2>&1', {
            cwd: projectRoot,
            timeout: 120000,
          });
          const passedMatch = testOutput.match(/(\d+)\s*(?:passed|passing)/i);
          const totalMatch = testOutput.match(/(\d+)\s*(?:tests?|specs?)/i);
          testsPassed = passedMatch ? parseInt(passedMatch[1], 10) : undefined;
          testsTotal = totalMatch ? parseInt(totalMatch[1], 10) : testsPassed;
          buildStatus = 'passing';
        } catch {
          buildStatus = 'failing';
        }

        return {
          checkpointName: name,
          checkpointSha: checkpoint.gitSha,
          currentSha: currentSha.full,
          filesChanged: filesMatch ? parseInt(filesMatch[1], 10) : 0,
          additions: addMatch ? parseInt(addMatch[1], 10) : 0,
          deletions: delMatch ? parseInt(delMatch[1], 10) : 0,
          testsPassed,
          testsTotal,
          buildStatus,
        };
      } catch {
        return {
          checkpointName: name,
          checkpointSha: checkpoint.gitSha,
          currentSha: currentSha.full,
          filesChanged: 0,
          additions: 0,
          deletions: 0,
          buildStatus: 'unknown',
        };
      }
    },

    async listCheckpoints(): Promise<CheckpointListEntry[]> {
      await loadCheckpoints();
      const currentSha = await getCurrentSha();

      const entries: CheckpointListEntry[] = [];

      for (const [name, checkpoint] of checkpoints) {
        const status = await getCheckpointStatus(checkpoint.gitSha);
        entries.push({
          name,
          timestamp: checkpoint.timestamp,
          gitShortSha: checkpoint.gitShortSha,
          status,
          isCurrent: currentSha.full === checkpoint.gitSha,
        });
      }

      // Sort by timestamp descending
      entries.sort((a, b) => b.timestamp.getTime() - a.timestamp.getTime());

      return entries;
    },

    async restoreCheckpoint(
      name: string,
      stashUncommitted: boolean = true
    ): Promise<CheckpointRestoreResult> {
      const checkpoint = checkpoints.get(name);
      if (!checkpoint) {
        return {
          success: false,
          checkpointName: name,
          previousSha: '',
          restoredSha: '',
          message: `Checkpoint not found: ${name}`,
        };
      }

      const currentSha = await getCurrentSha();
      let stashCreated: string | undefined;

      // Stash uncommitted changes if requested
      if (stashUncommitted && (await hasUncommittedChanges())) {
        try {
          const { stdout } = await execAsync(
            `git stash push -m "pre-restore-${name}"`,
            { cwd: projectRoot }
          );
          stashCreated = stdout.trim();
        } catch {
          return {
            success: false,
            checkpointName: name,
            previousSha: currentSha.full,
            restoredSha: '',
            message: 'Failed to stash uncommitted changes',
          };
        }
      }

      try {
        await execAsync(`git checkout ${checkpoint.gitSha}`, {
          cwd: projectRoot,
        });

        return {
          success: true,
          checkpointName: name,
          previousSha: currentSha.full,
          restoredSha: checkpoint.gitSha,
          stashCreated,
          message: `Restored to checkpoint ${name}. Run /verify quick to confirm.`,
        };
      } catch (error) {
        return {
          success: false,
          checkpointName: name,
          previousSha: currentSha.full,
          restoredSha: '',
          message: `Failed to restore: ${error instanceof Error ? error.message : String(error)}`,
        };
      }
    },

    async deleteCheckpoint(name: string): Promise<boolean> {
      if (!checkpoints.has(name)) {
        return false;
      }

      checkpoints.delete(name);

      // Rewrite log file without deleted checkpoint
      const entries = Array.from(checkpoints.values());
      const content = entries
        .map((e) => {
          const timestamp = e.timestamp.toISOString().replace(/[T:]/g, '-').slice(0, 16);
          return `${timestamp} | ${e.name} | ${e.gitShortSha}`;
        })
        .join('\n');

      await fs.writeFile(logFile, content + '\n');
      return true;
    },

    async getCheckpoint(name: string): Promise<CheckpointEntry | null> {
      await loadCheckpoints();
      return checkpoints.get(name) || null;
    },

    async cleanOldCheckpoints(): Promise<number> {
      await loadCheckpoints();

      if (checkpoints.size <= fullConfig.maxCheckpoints) {
        return 0;
      }

      // Sort by timestamp and remove oldest
      const sorted = Array.from(checkpoints.entries()).sort(
        (a, b) => b[1].timestamp.getTime() - a[1].timestamp.getTime()
      );

      const toRemove = sorted.slice(fullConfig.maxCheckpoints);
      let removed = 0;

      for (const [name] of toRemove) {
        if (await this.deleteCheckpoint(name)) {
          removed++;
        }
      }

      return removed;
    },

    getConfig(): CheckpointConfig {
      return fullConfig;
    },
  };
}

/**
 * Format checkpoint list as markdown
 *
 * @param checkpoints - Array of checkpoint list entries
 * @returns Markdown string
 */
export function formatCheckpointListMarkdown(
  checkpoints: CheckpointListEntry[]
): string {
  if (checkpoints.length === 0) {
    return 'チェックポイントがありません。\n`/checkpoint create <name>`で作成してください。';
  }

  const header = '| Name | Timestamp | SHA | Status |';
  const separator = '|------|-----------|-----|--------|';

  const rows = checkpoints.map((cp) => {
    const timestamp = cp.timestamp.toISOString().slice(0, 16).replace('T', ' ');
    const statusIcon = cp.isCurrent ? '📍' : cp.status === 'behind' ? '⬅️' : '➡️';
    return `| ${cp.name} | ${timestamp} | ${cp.gitShortSha} | ${statusIcon} ${cp.status} |`;
  });

  return [header, separator, ...rows].join('\n');
}

/**
 * Format checkpoint comparison as markdown
 *
 * @param comparison - Checkpoint comparison
 * @returns Markdown string
 */
export function formatCheckpointComparisonMarkdown(
  comparison: CheckpointComparison
): string {
  const testInfo =
    comparison.testsPassed !== undefined && comparison.testsTotal !== undefined
      ? `Tests: ${comparison.testsPassed}/${comparison.testsTotal} passed`
      : 'Tests: not available';

  return `Checkpoint Verification: ${comparison.checkpointName}
${'='.repeat(40)}

Checkpoint SHA: ${comparison.checkpointSha.slice(0, 7)}
Current SHA:    ${comparison.currentSha.slice(0, 7)}

Changes since checkpoint:
- Files changed: ${comparison.filesChanged}
- Additions: +${comparison.additions}
- Deletions: -${comparison.deletions}

${testInfo}
Build Status: ${comparison.buildStatus}`;
}
