/**
 * Git Client - Git operations for team sharing
 *
 * Implements: TSK-TEAM-001, REQ-TEAM-001〜002, DES-TEAM-001
 */

import { spawn } from 'node:child_process';
import { join } from 'node:path';
import type {
  GitResult,
  CommitInfo,
  BranchInfo,
  RemoteInfo,
  FileStatus,
  PullResult,
  PushResult,
} from './types.js';

/**
 * Git client configuration
 */
export interface GitClientConfig {
  /** Repository path */
  repoPath: string;

  /** Git executable path (default: git) */
  gitPath?: string;

  /** Default remote name (default: origin) */
  defaultRemote?: string;

  /** Team branch name (default: musubix-team) */
  teamBranch?: string;
}

/**
 * Git Client class
 */
export class GitClient {
  private config: Required<GitClientConfig>;

  constructor(config: GitClientConfig) {
    this.config = {
      gitPath: 'git',
      defaultRemote: 'origin',
      teamBranch: 'musubix-team',
      ...config,
    };
  }

  /**
   * Execute git command
   */
  private async exec(args: string[]): Promise<{ stdout: string; stderr: string; exitCode: number }> {
    return new Promise((resolve) => {
      const child = spawn(this.config.gitPath, args, {
        cwd: this.config.repoPath,
        stdio: ['pipe', 'pipe', 'pipe'],
      });

      let stdout = '';
      let stderr = '';

      child.stdout?.on('data', (data) => {
        stdout += data.toString();
      });

      child.stderr?.on('data', (data) => {
        stderr += data.toString();
      });

      child.on('error', (error) => {
        resolve({ stdout: '', stderr: error.message, exitCode: -1 });
      });

      child.on('close', (code) => {
        resolve({ stdout, stderr, exitCode: code ?? 0 });
      });
    });
  }

  /**
   * Check if directory is a git repository
   */
  async isRepo(): Promise<boolean> {
    const result = await this.exec(['rev-parse', '--is-inside-work-tree']);
    return result.exitCode === 0 && result.stdout.trim() === 'true';
  }

  /**
   * Initialize a git repository
   */
  async init(): Promise<GitResult> {
    const result = await this.exec(['init']);
    return {
      success: result.exitCode === 0,
      message: result.exitCode === 0 ? 'Repository initialized' : 'Failed to initialize',
      output: result.stdout,
      error: result.exitCode !== 0 ? result.stderr : undefined,
    };
  }

  /**
   * Get current branch name
   */
  async getCurrentBranch(): Promise<string | null> {
    const result = await this.exec(['rev-parse', '--abbrev-ref', 'HEAD']);
    return result.exitCode === 0 ? result.stdout.trim() : null;
  }

  /**
   * List all branches
   */
  async listBranches(): Promise<BranchInfo[]> {
    const result = await this.exec([
      'branch',
      '-a',
      '--format=%(refname:short)|%(objectname:short)|%(upstream:short)|%(HEAD)',
    ]);

    if (result.exitCode !== 0) return [];

    const branches: BranchInfo[] = [];

    for (const line of result.stdout.trim().split('\n')) {
      if (!line) continue;
      const [name, commit, upstream, head] = line.split('|');
      branches.push({
        name,
        current: head === '*',
        latestCommit: commit,
        upstream: upstream || undefined,
      });
    }

    return branches;
  }

  /**
   * Create a new branch
   */
  async createBranch(name: string, startPoint?: string): Promise<GitResult> {
    const args = ['branch', name];
    if (startPoint) args.push(startPoint);

    const result = await this.exec(args);
    return {
      success: result.exitCode === 0,
      message: result.exitCode === 0 ? `Branch ${name} created` : 'Failed to create branch',
      error: result.exitCode !== 0 ? result.stderr : undefined,
    };
  }

  /**
   * Checkout a branch
   */
  async checkout(branch: string, create?: boolean): Promise<GitResult> {
    const args = create ? ['checkout', '-b', branch] : ['checkout', branch];
    const result = await this.exec(args);
    return {
      success: result.exitCode === 0,
      message: result.exitCode === 0 ? `Switched to ${branch}` : 'Failed to checkout',
      error: result.exitCode !== 0 ? result.stderr : undefined,
    };
  }

  /**
   * Get file status
   */
  async status(): Promise<FileStatus[]> {
    const result = await this.exec(['status', '--porcelain=v1']);
    if (result.exitCode !== 0) return [];

    const files: FileStatus[] = [];

    for (const line of result.stdout.trim().split('\n')) {
      if (!line) continue;
      const index = line[0] as FileStatus['index'];
      const workingTree = line[1] as FileStatus['workingTree'];
      const path = line.slice(3);

      files.push({ path, index, workingTree });
    }

    return files;
  }

  /**
   * Add files to staging
   */
  async add(paths: string[]): Promise<GitResult> {
    const result = await this.exec(['add', ...paths]);
    return {
      success: result.exitCode === 0,
      message: result.exitCode === 0 ? 'Files staged' : 'Failed to stage files',
      affectedFiles: paths,
      error: result.exitCode !== 0 ? result.stderr : undefined,
    };
  }

  /**
   * Commit staged changes
   */
  async commit(message: string): Promise<GitResult> {
    const result = await this.exec(['commit', '-m', message]);
    return {
      success: result.exitCode === 0,
      message: result.exitCode === 0 ? 'Committed' : 'Failed to commit',
      output: result.stdout,
      error: result.exitCode !== 0 ? result.stderr : undefined,
    };
  }

  /**
   * Get commit history
   */
  async log(limit = 10): Promise<CommitInfo[]> {
    const result = await this.exec([
      'log',
      `-${limit}`,
      '--format=%H|%h|%an|%ae|%aI|%s|%P',
    ]);

    if (result.exitCode !== 0) return [];

    const commits: CommitInfo[] = [];

    for (const line of result.stdout.trim().split('\n')) {
      if (!line) continue;
      const [hash, shortHash, authorName, authorEmail, date, message, parents] = line.split('|');
      commits.push({
        hash,
        shortHash,
        authorName,
        authorEmail,
        date: new Date(date),
        message,
        parents: parents ? parents.split(' ') : [],
      });
    }

    return commits;
  }

  /**
   * List remotes
   */
  async listRemotes(): Promise<RemoteInfo[]> {
    const result = await this.exec(['remote', '-v']);
    if (result.exitCode !== 0) return [];

    const remotes = new Map<string, { fetchUrl?: string; pushUrl?: string }>();

    for (const line of result.stdout.trim().split('\n')) {
      if (!line) continue;
      const match = line.match(/^(\S+)\s+(\S+)\s+\((fetch|push)\)$/);
      if (!match) continue;

      const [, name, url, type] = match;
      if (!remotes.has(name)) {
        remotes.set(name, {});
      }
      const remote = remotes.get(name)!;
      if (type === 'fetch') {
        remote.fetchUrl = url;
      } else {
        remote.pushUrl = url;
      }
    }

    return Array.from(remotes.entries()).map(([name, urls]) => ({
      name,
      fetchUrl: urls.fetchUrl ?? '',
      pushUrl: urls.pushUrl ?? urls.fetchUrl ?? '',
    }));
  }

  /**
   * Add remote
   */
  async addRemote(name: string, url: string): Promise<GitResult> {
    const result = await this.exec(['remote', 'add', name, url]);
    return {
      success: result.exitCode === 0,
      message: result.exitCode === 0 ? `Remote ${name} added` : 'Failed to add remote',
      error: result.exitCode !== 0 ? result.stderr : undefined,
    };
  }

  /**
   * Fetch from remote
   */
  async fetch(remote?: string): Promise<GitResult> {
    const result = await this.exec(['fetch', remote ?? this.config.defaultRemote]);
    return {
      success: result.exitCode === 0,
      message: result.exitCode === 0 ? 'Fetched' : 'Failed to fetch',
      output: result.stdout,
      error: result.exitCode !== 0 ? result.stderr : undefined,
    };
  }

  /**
   * Pull from remote
   */
  async pull(remote?: string, branch?: string): Promise<PullResult> {
    const args = ['pull', remote ?? this.config.defaultRemote];
    if (branch) args.push(branch);

    const result = await this.exec(args);

    if (result.exitCode !== 0) {
      return {
        success: false,
        commitCount: 0,
        changedFiles: [],
        insertions: 0,
        deletions: 0,
        conflicts: result.stderr.includes('CONFLICT') ? [result.stderr] : undefined,
      };
    }

    // Parse pull output
    const statsMatch = result.stdout.match(/(\d+) files? changed(?:, (\d+) insertions?\(\+\))?(?:, (\d+) deletions?\(-\))?/);

    return {
      success: true,
      commitCount: (result.stdout.match(/Updating/g) ?? []).length,
      changedFiles: [],
      insertions: statsMatch ? parseInt(statsMatch[2] ?? '0', 10) : 0,
      deletions: statsMatch ? parseInt(statsMatch[3] ?? '0', 10) : 0,
    };
  }

  /**
   * Push to remote
   */
  async push(remote?: string, branch?: string, setUpstream?: boolean): Promise<PushResult> {
    const args = ['push'];
    if (setUpstream) args.push('-u');
    args.push(remote ?? this.config.defaultRemote);
    if (branch) args.push(branch);

    const result = await this.exec(args);

    return {
      success: result.exitCode === 0,
      remote: remote ?? this.config.defaultRemote,
      branch: branch ?? (await this.getCurrentBranch()) ?? 'unknown',
      commitCount: 1, // Simplified
    };
  }

  /**
   * Ensure team branch exists
   */
  async ensureTeamBranch(): Promise<GitResult> {
    const branches = await this.listBranches();
    const teamBranch = this.config.teamBranch;

    // Check if team branch exists
    const exists = branches.some((b) => b.name === teamBranch || b.name === `remotes/${this.config.defaultRemote}/${teamBranch}`);

    if (!exists) {
      // Create team branch
      return this.createBranch(teamBranch);
    }

    return {
      success: true,
      message: `Team branch ${teamBranch} exists`,
    };
  }

  /**
   * Get team sharing directory path
   */
  getTeamDir(): string {
    return join(this.config.repoPath, '.musubix-team');
  }

  /**
   * Get patterns directory path
   */
  getPatternsDir(): string {
    return join(this.getTeamDir(), 'patterns');
  }

  /**
   * Get knowledge directory path
   */
  getKnowledgeDir(): string {
    return join(this.getTeamDir(), 'knowledge');
  }
}

/**
 * Create a Git client instance
 */
export function createGitClient(config: GitClientConfig): GitClient {
  return new GitClient(config);
}
