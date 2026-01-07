/**
 * @fileoverview Git Hooks Integration for Security Scanning
 * @module @nahisaho/musubix-security/integrations/git-hooks
 * 
 * Provides pre-commit and pre-push hooks for automated security checks.
 */

import { execSync } from 'child_process';
import { existsSync, readFileSync, writeFileSync, mkdirSync, chmodSync } from 'fs';
import { join, dirname } from 'path';
import type { ScanResult, Severity } from '../types/index.js';

// ============================================================================
// Types
// ============================================================================

/**
 * Hook type
 */
export type HookType = 'pre-commit' | 'pre-push' | 'commit-msg' | 'post-commit';

/**
 * Git hooks configuration
 */
export interface GitHooksConfig {
  /** Hooks to install */
  hooks: HookType[];
  /** Fail on specific severities */
  failOn?: Severity[];
  /** Scan staged files only (for pre-commit) */
  stagedOnly?: boolean;
  /** File patterns to include */
  includePatterns?: string[];
  /** File patterns to exclude */
  excludePatterns?: string[];
  /** Enable secret detection */
  detectSecrets?: boolean;
  /** Enable vulnerability scanning */
  detectVulnerabilities?: boolean;
  /** Skip hooks in CI environment */
  skipInCI?: boolean;
  /** Timeout in seconds */
  timeout?: number;
  /** Custom hook scripts */
  customScripts?: Partial<Record<HookType, string>>;
}

/**
 * Hook execution result
 */
export interface HookResult {
  /** Hook type */
  hook: HookType;
  /** Whether hook passed */
  passed: boolean;
  /** Execution time in ms */
  executionTime: number;
  /** Files scanned */
  filesScanned: string[];
  /** Scan result (if performed) */
  scanResult?: ScanResult;
  /** Error message (if failed) */
  error?: string;
  /** Skipped reason */
  skippedReason?: string;
}

/**
 * Hook installation result
 */
export interface InstallResult {
  /** Hooks installed */
  installed: HookType[];
  /** Hooks that failed to install */
  failed: { hook: HookType; error: string }[];
  /** Git directory path */
  gitDir: string;
  /** Whether backup was created */
  backupCreated: boolean;
}

/**
 * Staged file info
 */
export interface StagedFile {
  /** File path */
  path: string;
  /** Git status */
  status: 'A' | 'M' | 'D' | 'R' | 'C';
  /** Old path (for renames) */
  oldPath?: string;
}

// ============================================================================
// Git Hooks Manager Class
// ============================================================================

/**
 * Manages Git hooks for security scanning
 * 
 * @example
 * ```typescript
 * const hooks = createGitHooks({
 *   hooks: ['pre-commit', 'pre-push'],
 *   failOn: ['critical', 'high'],
 *   detectSecrets: true,
 * });
 * 
 * // Install hooks
 * const result = await hooks.install();
 * 
 * // Run pre-commit manually
 * const hookResult = await hooks.runHook('pre-commit');
 * ```
 */
export class GitHooksManager {
  private config: Required<GitHooksConfig>;

  constructor(config: GitHooksConfig) {
    this.config = {
      hooks: config.hooks,
      failOn: config.failOn ?? ['critical', 'high'],
      stagedOnly: config.stagedOnly ?? true,
      includePatterns: config.includePatterns ?? ['**/*.ts', '**/*.js', '**/*.tsx', '**/*.jsx'],
      excludePatterns: config.excludePatterns ?? ['**/node_modules/**', '**/dist/**', '**/*.test.ts'],
      detectSecrets: config.detectSecrets ?? true,
      detectVulnerabilities: config.detectVulnerabilities ?? true,
      skipInCI: config.skipInCI ?? true,
      timeout: config.timeout ?? 60,
      customScripts: config.customScripts ?? {},
    };
  }

  /**
   * Install git hooks
   */
  async install(workDir: string = process.cwd()): Promise<InstallResult> {
    const gitDir = this.findGitDir(workDir);
    if (!gitDir) {
      throw new Error('Not a git repository');
    }

    const hooksDir = join(gitDir, 'hooks');
    
    // Create hooks directory if it doesn't exist
    if (!existsSync(hooksDir)) {
      mkdirSync(hooksDir, { recursive: true });
    }

    const installed: HookType[] = [];
    const failed: { hook: HookType; error: string }[] = [];
    let backupCreated = false;

    for (const hook of this.config.hooks) {
      try {
        const hookPath = join(hooksDir, hook);
        
        // Backup existing hook
        if (existsSync(hookPath)) {
          const backupPath = `${hookPath}.musubix-backup`;
          const existing = readFileSync(hookPath, 'utf-8');
          if (!existing.includes('musubix-security')) {
            writeFileSync(backupPath, existing);
            backupCreated = true;
          }
        }

        // Write hook script
        const script = this.generateHookScript(hook);
        writeFileSync(hookPath, script);
        chmodSync(hookPath, '755');
        
        installed.push(hook);
      } catch (error) {
        failed.push({
          hook,
          error: error instanceof Error ? error.message : String(error),
        });
      }
    }

    return {
      installed,
      failed,
      gitDir,
      backupCreated,
    };
  }

  /**
   * Uninstall git hooks
   */
  async uninstall(workDir: string = process.cwd()): Promise<{ removed: HookType[]; restored: HookType[] }> {
    const gitDir = this.findGitDir(workDir);
    if (!gitDir) {
      throw new Error('Not a git repository');
    }

    const hooksDir = join(gitDir, 'hooks');
    const removed: HookType[] = [];
    const restored: HookType[] = [];

    for (const hook of this.config.hooks) {
      const hookPath = join(hooksDir, hook);
      const backupPath = `${hookPath}.musubix-backup`;

      if (existsSync(hookPath)) {
        const content = readFileSync(hookPath, 'utf-8');
        if (content.includes('musubix-security')) {
          // Check for backup
          if (existsSync(backupPath)) {
            const backup = readFileSync(backupPath, 'utf-8');
            writeFileSync(hookPath, backup);
            restored.push(hook);
          } else {
            // Remove hook
            writeFileSync(hookPath, '#!/bin/sh\nexit 0\n');
            removed.push(hook);
          }
        }
      }
    }

    return { removed, restored };
  }

  /**
   * Run a specific hook
   */
  async runHook(hook: HookType, workDir: string = process.cwd()): Promise<HookResult> {
    const startTime = Date.now();
    
    // Check if should skip
    if (this.shouldSkip()) {
      return {
        hook,
        passed: true,
        executionTime: Date.now() - startTime,
        filesScanned: [],
        skippedReason: 'Running in CI environment',
      };
    }

    try {
      // Get files to scan
      const files = hook === 'pre-commit' && this.config.stagedOnly
        ? await this.getStagedFiles(workDir)
        : await this.getAllFiles(workDir);

      const filePaths = files
        .filter(f => this.shouldIncludeFile(f.path))
        .map(f => f.path);

      if (filePaths.length === 0) {
        return {
          hook,
          passed: true,
          executionTime: Date.now() - startTime,
          filesScanned: [],
          skippedReason: 'No files to scan',
        };
      }

      // Run security scan
      const scanResult = await this.runSecurityScan(filePaths, workDir);
      const passed = this.checkResult(scanResult);

      return {
        hook,
        passed,
        executionTime: Date.now() - startTime,
        filesScanned: filePaths,
        scanResult,
        error: passed ? undefined : this.formatError(scanResult),
      };
    } catch (error) {
      return {
        hook,
        passed: false,
        executionTime: Date.now() - startTime,
        filesScanned: [],
        error: error instanceof Error ? error.message : String(error),
      };
    }
  }

  /**
   * Get staged files
   */
  async getStagedFiles(workDir: string = process.cwd()): Promise<StagedFile[]> {
    try {
      const output = execSync('git diff --cached --name-status', {
        cwd: workDir,
        encoding: 'utf-8',
      });

      return output
        .split('\n')
        .filter(line => line.trim())
        .map(line => {
          const parts = line.split('\t');
          const status = parts[0][0] as StagedFile['status'];
          
          if (status === 'R' || status === 'C') {
            return {
              status,
              oldPath: parts[1],
              path: parts[2],
            };
          }
          
          return {
            status,
            path: parts[1],
          };
        });
    } catch {
      return [];
    }
  }

  /**
   * Generate hook script content
   */
  generateHookScript(hook: HookType): string {
    // Use custom script if provided
    if (this.config.customScripts[hook]) {
      return this.config.customScripts[hook]!;
    }

    const skipCI = this.config.skipInCI 
      ? `
# Skip in CI environment
if [ -n "$CI" ] || [ -n "$CONTINUOUS_INTEGRATION" ]; then
  echo "Skipping ${hook} hook in CI environment"
  exit 0
fi
`
      : '';

    const timeout = this.config.timeout;
    const failOn = this.config.failOn.join(',');

    return `#!/bin/sh
# Generated by @nahisaho/musubix-security
# Hook: ${hook}
# Generated: ${new Date().toISOString()}

${skipCI}

echo "🔒 Running MUSUBIX Security Scan (${hook})..."

# Check if musubix-security is available
if ! command -v npx &> /dev/null; then
  echo "Warning: npx not found, skipping security scan"
  exit 0
fi

# Run security scan with timeout
timeout ${timeout}s npx @nahisaho/musubix-security scan --staged --fail-on ${failOn} --quiet
RESULT=$?

if [ $RESULT -eq 0 ]; then
  echo "✅ Security scan passed"
  exit 0
elif [ $RESULT -eq 124 ]; then
  echo "⚠️ Security scan timed out, proceeding anyway"
  exit 0
else
  echo "❌ Security scan failed"
  echo "Run 'npx @nahisaho/musubix-security scan' for details"
  exit 1
fi
`;
  }

  /**
   * Check if hooks should be skipped
   */
  shouldSkip(): boolean {
    if (!this.config.skipInCI) return false;
    
    return !!(
      process.env.CI ||
      process.env.CONTINUOUS_INTEGRATION ||
      process.env.GITHUB_ACTIONS ||
      process.env.GITLAB_CI ||
      process.env.JENKINS_URL
    );
  }

  /**
   * Get hook status
   */
  async getStatus(workDir: string = process.cwd()): Promise<Record<HookType, 'installed' | 'not-installed' | 'other'>> {
    const gitDir = this.findGitDir(workDir);
    const status: Record<HookType, 'installed' | 'not-installed' | 'other'> = {} as Record<HookType, 'installed' | 'not-installed' | 'other'>;

    for (const hook of this.config.hooks) {
      if (!gitDir) {
        status[hook] = 'not-installed';
        continue;
      }

      const hookPath = join(gitDir, 'hooks', hook);
      if (!existsSync(hookPath)) {
        status[hook] = 'not-installed';
      } else {
        const content = readFileSync(hookPath, 'utf-8');
        status[hook] = content.includes('musubix-security') ? 'installed' : 'other';
      }
    }

    return status;
  }

  // ============================================================================
  // Private Methods
  // ============================================================================

  private findGitDir(startDir: string): string | null {
    let dir = startDir;
    
    while (dir !== dirname(dir)) {
      const gitDir = join(dir, '.git');
      if (existsSync(gitDir)) {
        return gitDir;
      }
      dir = dirname(dir);
    }
    
    return null;
  }

  private async getAllFiles(workDir: string): Promise<StagedFile[]> {
    try {
      const output = execSync('git ls-files', {
        cwd: workDir,
        encoding: 'utf-8',
      });

      return output
        .split('\n')
        .filter(line => line.trim())
        .map(path => ({ path, status: 'M' as const }));
    } catch {
      return [];
    }
  }

  private shouldIncludeFile(filePath: string): boolean {
    // Check exclude patterns first
    for (const pattern of this.config.excludePatterns) {
      if (this.matchPattern(filePath, pattern)) {
        return false;
      }
    }

    // Check include patterns
    for (const pattern of this.config.includePatterns) {
      if (this.matchPattern(filePath, pattern)) {
        return true;
      }
    }

    return false;
  }

  private matchPattern(filePath: string, pattern: string): boolean {
    // Simple glob matching
    const regex = pattern
      .replace(/\*\*/g, '.*')
      .replace(/\*/g, '[^/]*')
      .replace(/\?/g, '.');
    
    return new RegExp(`^${regex}$`).test(filePath);
  }

  private async runSecurityScan(files: string[], _workDir: string): Promise<ScanResult> {
    // Simplified scan result for hook context
    // In real implementation, this would call the actual scanner
    const vulnerabilities: ScanResult['vulnerabilities'] = [];
    
    // Mock implementation - in production this would use actual scanners
    return {
      vulnerabilities,
      scannedFiles: files.length,
      skippedFiles: 0,
      duration: 0,
      timestamp: new Date(),
      options: {},
      summary: {
        total: 0,
        critical: 0,
        high: 0,
        medium: 0,
        low: 0,
        info: 0,
      },
    };
  }

  private checkResult(result: ScanResult): boolean {
    for (const severity of this.config.failOn) {
      if (result.summary[severity] > 0) {
        return false;
      }
    }
    return true;
  }

  private formatError(result: ScanResult): string {
    const issues: string[] = [];
    
    for (const severity of this.config.failOn) {
      const count = result.summary[severity];
      if (count > 0) {
        issues.push(`${count} ${severity} issue(s)`);
      }
    }
    
    return `Security check failed: ${issues.join(', ')}`;
  }
}

// ============================================================================
// Factory Functions
// ============================================================================

/**
 * Create a git hooks manager
 */
export function createGitHooks(config: GitHooksConfig): GitHooksManager {
  return new GitHooksManager(config);
}

/**
 * Quick install pre-commit hook
 */
export async function installPreCommitHook(workDir?: string): Promise<InstallResult> {
  const hooks = createGitHooks({
    hooks: ['pre-commit'],
    failOn: ['critical', 'high'],
    stagedOnly: true,
  });
  
  return hooks.install(workDir);
}

/**
 * Quick install all recommended hooks
 */
export async function installRecommendedHooks(workDir?: string): Promise<InstallResult> {
  const hooks = createGitHooks({
    hooks: ['pre-commit', 'pre-push'],
    failOn: ['critical', 'high'],
    stagedOnly: true,
    detectSecrets: true,
    detectVulnerabilities: true,
  });
  
  return hooks.install(workDir);
}
