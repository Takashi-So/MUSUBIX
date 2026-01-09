/**
 * @nahisaho/musubix-codegraph - Git Operations
 *
 * Git operations wrapper using simple-git
 *
 * @packageDocumentation
 * @module @nahisaho/musubix-codegraph/pr
 *
 * @see REQ-CG-PR-003 - Git Branch Creation
 * @see REQ-CG-PR-004 - Auto Commit
 * @see DES-CG-PR-004 - Class Design
 */

import { execSync } from 'node:child_process';
import { existsSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import type {
  BranchInfo,
  CommitInfo,
  GitOperationOptions,
  CodeChange,
} from './types.js';

/**
 * Git operations wrapper
 *
 * Provides a safe interface for Git operations needed for PR creation.
 * Uses child_process to interact with Git directly.
 *
 * @see DES-CG-PR-004
 * @example
 * ```typescript
 * const git = new GitOperations('/path/to/repo');
 * await git.createBranch('refactor/extract-interface');
 * await git.commit('refactor(auth): extract IAuthService interface');
 * await git.push();
 * ```
 */
export class GitOperations {
  private readonly repoPath: string;
  private readonly remote: string;

  /**
   * Create a new GitOperations instance
   * @param options - Git operation options
   */
  constructor(options: GitOperationOptions) {
    this.repoPath = options.repoPath;
    this.remote = options.remote ?? 'origin';

    // Validate repository
    if (!this.isGitRepository()) {
      throw new Error(`Not a git repository: ${this.repoPath}`);
    }
  }

  // ============================================================================
  // Repository Information
  // ============================================================================

  /**
   * Check if path is a Git repository
   */
  isGitRepository(): boolean {
    try {
      this.git(['rev-parse', '--git-dir']);
      return true;
    } catch {
      return false;
    }
  }

  /**
   * Get repository root path
   */
  getRepoRoot(): string {
    return this.git(['rev-parse', '--show-toplevel']).trim();
  }

  /**
   * Get current branch name
   * @see REQ-CG-PR-003
   */
  getCurrentBranch(): string {
    return this.git(['rev-parse', '--abbrev-ref', 'HEAD']).trim();
  }

  /**
   * Get default branch name (main or master)
   */
  getDefaultBranch(): string {
    try {
      // Try to get from remote HEAD
      const remoteHead = this.git(['symbolic-ref', `refs/remotes/${this.remote}/HEAD`]);
      return remoteHead.replace(`refs/remotes/${this.remote}/`, '').trim();
    } catch {
      // Fallback: check if main exists, otherwise master
      try {
        this.git(['rev-parse', '--verify', 'main']);
        return 'main';
      } catch {
        return 'master';
      }
    }
  }

  /**
   * List all branches
   */
  listBranches(): BranchInfo[] {
    const output = this.git([
      'for-each-ref',
      '--format=%(refname:short)|%(HEAD)|%(upstream:short)|%(objectname:short)',
      'refs/heads',
    ]);

    return output
      .trim()
      .split('\n')
      .filter((line) => line.length > 0)
      .map((line) => {
        const [name, head, tracking, commit] = line.split('|');
        return {
          name,
          current: head === '*',
          tracking: tracking || undefined,
          commit,
        };
      });
  }

  /**
   * Check if branch exists
   */
  branchExists(branchName: string): boolean {
    try {
      this.git(['rev-parse', '--verify', branchName]);
      return true;
    } catch {
      return false;
    }
  }

  // ============================================================================
  // Branch Operations
  // ============================================================================

  /**
   * Create a new branch
   * @see REQ-CG-PR-003
   */
  createBranch(branchName: string, baseBranch?: string): void {
    const base = baseBranch ?? this.getCurrentBranch();

    if (this.branchExists(branchName)) {
      throw new Error(`Branch already exists: ${branchName}`);
    }

    this.git(['checkout', '-b', branchName, base]);
  }

  /**
   * Checkout an existing branch
   */
  checkout(branchName: string): void {
    if (!this.branchExists(branchName)) {
      throw new Error(`Branch does not exist: ${branchName}`);
    }

    this.git(['checkout', branchName]);
  }

  /**
   * Delete a branch
   */
  deleteBranch(branchName: string, force = false): void {
    const flag = force ? '-D' : '-d';
    this.git(['branch', flag, branchName]);
  }

  // ============================================================================
  // Working Tree Operations
  // ============================================================================

  /**
   * Check for uncommitted changes
   */
  hasUncommittedChanges(): boolean {
    const status = this.git(['status', '--porcelain']);
    return status.trim().length > 0;
  }

  /**
   * Get list of modified files
   */
  getModifiedFiles(): string[] {
    const status = this.git(['status', '--porcelain']);
    return status
      .trim()
      .split('\n')
      .filter((line) => line.length > 0)
      .map((line) => line.slice(3).trim());
  }

  /**
   * Stage files for commit
   */
  stageFiles(files: string[]): void {
    if (files.length === 0) return;
    this.git(['add', ...files]);
  }

  /**
   * Stage all changes
   */
  stageAll(): void {
    this.git(['add', '-A']);
  }

  /**
   * Unstage files
   */
  unstageFiles(files: string[]): void {
    if (files.length === 0) return;
    this.git(['reset', 'HEAD', ...files]);
  }

  /**
   * Discard changes in working tree
   */
  discardChanges(files: string[]): void {
    if (files.length === 0) return;
    this.git(['checkout', '--', ...files]);
  }

  /**
   * Stash changes
   */
  stash(message?: string): void {
    const args = ['stash', 'push'];
    if (message) {
      args.push('-m', message);
    }
    this.git(args);
  }

  /**
   * Pop stash
   */
  stashPop(): void {
    this.git(['stash', 'pop']);
  }

  // ============================================================================
  // Commit Operations
  // ============================================================================

  /**
   * Create a commit
   * @see REQ-CG-PR-004
   */
  commit(message: string, options?: { allowEmpty?: boolean }): CommitInfo {
    const args = ['commit', '-m', message];
    if (options?.allowEmpty) {
      args.push('--allow-empty');
    }

    this.git(args);

    // Get commit info
    return this.getLastCommit();
  }

  /**
   * Get last commit info
   */
  getLastCommit(): CommitInfo {
    const format = '%H|%s|%an|%ae|%aI';
    const output = this.git(['log', '-1', `--format=${format}`]).trim();
    const [hash, message, author, email, dateStr] = output.split('|');

    return {
      hash,
      message,
      author,
      email,
      date: new Date(dateStr),
    };
  }

  /**
   * Get commit history
   */
  getCommitHistory(count = 10): CommitInfo[] {
    const format = '%H|%s|%an|%ae|%aI';
    const output = this.git(['log', `-${count}`, `--format=${format}`]).trim();

    return output
      .split('\n')
      .filter((line) => line.length > 0)
      .map((line) => {
        const [hash, message, author, email, dateStr] = line.split('|');
        return {
          hash,
          message,
          author,
          email,
          date: new Date(dateStr),
        };
      });
  }

  // ============================================================================
  // Remote Operations
  // ============================================================================

  /**
   * Push branch to remote
   */
  push(options?: { setUpstream?: boolean; force?: boolean }): void {
    const args = ['push'];

    if (options?.setUpstream) {
      args.push('-u', this.remote, this.getCurrentBranch());
    }

    if (options?.force) {
      args.push('--force');
    }

    this.git(args);
  }

  /**
   * Fetch from remote
   */
  fetch(prune = false): void {
    const args = ['fetch', this.remote];
    if (prune) {
      args.push('--prune');
    }
    this.git(args);
  }

  /**
   * Pull from remote
   */
  pull(rebase = false): void {
    const args = ['pull', this.remote, this.getCurrentBranch()];
    if (rebase) {
      args.push('--rebase');
    }
    this.git(args);
  }

  /**
   * Get remote URL
   */
  getRemoteUrl(): string {
    return this.git(['remote', 'get-url', this.remote]).trim();
  }

  /**
   * Parse GitHub owner/repo from remote URL
   */
  parseRemoteUrl(): { owner: string; repo: string } | null {
    const url = this.getRemoteUrl();

    // SSH format: git@github.com:owner/repo.git
    const sshMatch = url.match(/git@github\.com:([^/]+)\/([^/.]+)(\.git)?$/);
    if (sshMatch) {
      return { owner: sshMatch[1], repo: sshMatch[2] };
    }

    // HTTPS format: https://github.com/owner/repo.git
    const httpsMatch = url.match(/https:\/\/github\.com\/([^/]+)\/([^/.]+)(\.git)?$/);
    if (httpsMatch) {
      return { owner: httpsMatch[1], repo: httpsMatch[2] };
    }

    return null;
  }

  // ============================================================================
  // Diff Operations
  // ============================================================================

  /**
   * Get diff for staged changes
   */
  getStagedDiff(): string {
    return this.git(['diff', '--cached']);
  }

  /**
   * Get diff for unstaged changes
   */
  getUnstagedDiff(): string {
    return this.git(['diff']);
  }

  /**
   * Get diff between branches
   */
  getDiffBetweenBranches(baseBranch: string, headBranch?: string): string {
    const head = headBranch ?? this.getCurrentBranch();
    return this.git(['diff', `${baseBranch}...${head}`]);
  }

  /**
   * Get diff stats
   */
  getDiffStats(baseBranch?: string): { additions: number; deletions: number; files: number } {
    const base = baseBranch ?? this.getDefaultBranch();
    const output = this.git(['diff', '--stat', `${base}...HEAD`]);

    const match = output.match(/(\d+) files? changed(?:, (\d+) insertions?\(\+\))?(?:, (\d+) deletions?\(-\))?/);
    if (!match) {
      return { additions: 0, deletions: 0, files: 0 };
    }

    return {
      files: parseInt(match[1], 10) || 0,
      additions: parseInt(match[2], 10) || 0,
      deletions: parseInt(match[3], 10) || 0,
    };
  }

  // ============================================================================
  // File Operations for Refactoring
  // ============================================================================

  /**
   * Apply code changes to files
   * @see REQ-CG-PR-002
   */
  applyCodeChanges(changes: CodeChange[]): string[] {
    const modifiedFiles: string[] = [];

    for (const change of changes) {
      const filePath = join(this.repoPath, change.filePath);

      // Ensure file exists
      if (!existsSync(filePath)) {
        throw new Error(`File not found: ${change.filePath}`);
      }

      // Read file content
      const content = readFileSync(filePath, 'utf-8');
      const lines = content.split('\n');

      // Validate line numbers
      if (change.startLine < 1 || change.endLine > lines.length) {
        throw new Error(
          `Invalid line range ${change.startLine}-${change.endLine} for file ${change.filePath} (has ${lines.length} lines)`
        );
      }

      // Apply change
      const beforeLines = lines.slice(0, change.startLine - 1);
      const afterLines = lines.slice(change.endLine);
      const newLines = change.newCode.split('\n');

      const newContent = [...beforeLines, ...newLines, ...afterLines].join('\n');

      // Write back
      writeFileSync(filePath, newContent, 'utf-8');
      modifiedFiles.push(change.filePath);
    }

    return [...new Set(modifiedFiles)];
  }

  /**
   * Revert changes to a file
   */
  revertFile(filePath: string): void {
    this.git(['checkout', 'HEAD', '--', filePath]);
  }

  // ============================================================================
  // Private Helpers
  // ============================================================================

  /**
   * Execute a git command synchronously
   */
  private git(args: string[]): string {
    try {
      return execSync(`git ${args.join(' ')}`, {
        cwd: this.repoPath,
        encoding: 'utf-8',
        stdio: ['pipe', 'pipe', 'pipe'],
      });
    } catch (error) {
      if (error instanceof Error && 'stderr' in error) {
        throw new Error(`Git command failed: git ${args.join(' ')}\n${(error as { stderr: string }).stderr}`);
      }
      throw error;
    }
  }
}

/**
 * Create a GitOperations instance
 */
export function createGitOperations(repoPath: string, remote?: string): GitOperations {
  return new GitOperations({ repoPath, remote });
}
