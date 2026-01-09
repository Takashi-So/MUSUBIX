/**
 * @nahisaho/musubix-codegraph - PR Creator
 *
 * Main orchestrator for creating PRs from refactoring suggestions
 *
 * @packageDocumentation
 * @module @nahisaho/musubix-codegraph/pr
 *
 * @see REQ-CG-PR-001 - GitHub Authentication
 * @see REQ-CG-PR-002 - Auto Apply Refactoring
 * @see REQ-CG-PR-003 - Git Branch Creation
 * @see REQ-CG-PR-004 - Auto Commit
 * @see REQ-CG-PR-005 - GitHub PR Creation
 * @see DES-CG-PR-001 - Component Design
 * @see DES-CG-PR-005 - Sequence Diagram
 */

import { EventEmitter } from 'node:events';
import { GitOperations } from './git-operations.js';
import { GitHubAdapter } from './github-adapter.js';
import { RefactoringApplier } from './refactoring-applier.js';
import { PRTemplateGenerator } from './pr-template.js';
import { PRCreatorError, PRErrorMessages } from './errors.js';
import type {
  RefactoringSuggestion,
  PRCreateOptions,
  PRCreateResult,
  PRPreview,
  PRCreatorEvents,
} from './types.js';
import {
  generateBranchName,
  generateCommitMessage,
} from './types.js';

/**
 * PRCreator state
 * @see DES-CG-v234-003
 */
export type PRCreatorState = 'uninitialized' | 'offline' | 'full';

/**
 * PR Creator configuration
 */
export interface PRCreatorConfig {
  /** Repository root path */
  repoPath: string;
  /** GitHub token (optional, will try env or gh CLI) */
  githubToken?: string;
  /** Remote name (default: origin) */
  remote?: string;
  /** Create backups before modifications */
  createBackups?: boolean;
}

/**
 * PR Creator
 *
 * Orchestrates the entire PR creation workflow:
 * 1. Authenticate with GitHub
 * 2. Create a new branch
 * 3. Apply refactoring changes
 * 4. Commit changes
 * 5. Push to remote
 * 6. Create PR on GitHub
 *
 * @see DES-CG-PR-001
 * @see DES-CG-PR-005
 * @example
 * ```typescript
 * const creator = new PRCreator({ repoPath: '/path/to/repo' });
 * await creator.initialize();
 *
 * const result = await creator.create({
 *   suggestion: refactoringSuggestion,
 *   baseBranch: 'main',
 *   labels: ['refactoring', 'auto-generated'],
 * });
 *
 * console.log(`PR created: ${result.pr?.url}`);
 * ```
 */
export class PRCreator extends EventEmitter {
  private readonly config: PRCreatorConfig;
  private git: GitOperations | null = null;
  private github: GitHubAdapter | null = null;
  private applier: RefactoringApplier | null = null;
  private templateGenerator: PRTemplateGenerator;
  private initialized = false;
  private originalBranch: string | null = null;
  private state: PRCreatorState = 'uninitialized';

  /**
   * Create a new PRCreator
   * @param config - Configuration options
   */
  constructor(config: PRCreatorConfig) {
    super();
    this.config = {
      remote: 'origin',
      createBackups: true,
      ...config,
    };
    this.templateGenerator = new PRTemplateGenerator();
  }

  // ============================================================================
  // Initialization
  // ============================================================================

  /**
   * Initialize for offline operations (preview only)
   * Does not require GitHub authentication
   *
   * @see REQ-CG-v234-001
   * @see DES-CG-v234-001
   */
  async initializeOffline(): Promise<{ success: boolean; error?: string }> {
    try {
      // Initialize Git operations (local only)
      this.git = new GitOperations({
        repoPath: this.config.repoPath,
        remote: this.config.remote,
      });

      // Initialize refactoring applier
      this.applier = new RefactoringApplier({
        repoPath: this.config.repoPath,
        createBackups: this.config.createBackups,
      });

      // Store current branch for potential rollback
      this.originalBranch = this.git.getCurrentBranch();

      this.state = 'offline';
      this.initialized = true;
      return { success: true };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : String(error),
      };
    }
  }

  /**
   * Initialize the PR creator with full GitHub authentication
   * Sets up Git operations and authenticates with GitHub
   */
  async initialize(): Promise<{ success: boolean; error?: string }> {
    try {
      // First do offline initialization if not already done
      if (this.state === 'uninitialized') {
        const offlineResult = await this.initializeOffline();
        if (!offlineResult.success) {
          return offlineResult;
        }
      }

      // Parse GitHub owner/repo from remote
      const remoteInfo = this.git!.parseRemoteUrl();
      if (!remoteInfo) {
        const err = PRErrorMessages.REMOTE_PARSE_FAILED;
        return {
          success: false,
          error: `${err.message}. ${err.suggestion}`,
        };
      }

      // Initialize GitHub adapter
      this.github = new GitHubAdapter({
        owner: remoteInfo.owner,
        repo: remoteInfo.repo,
        token: this.config.githubToken,
      });

      // Authenticate with GitHub
      const authResult = await this.github.authenticate();
      if (!authResult.authenticated) {
        const err = PRErrorMessages.AUTH_FAILED;
        return {
          success: false,
          error: `${err.message}: ${authResult.error}. ${err.suggestion}`,
        };
      }

      this.state = 'full';
      this.initialized = true;
      return { success: true };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : String(error),
      };
    }
  }

  /**
   * Check if initialized
   */
  isInitialized(): boolean {
    return this.initialized;
  }

  /**
   * Get current state
   * @see DES-CG-v234-003
   */
  getState(): PRCreatorState {
    return this.state;
  }

  // ============================================================================
  // Main Operations
  // ============================================================================

  /**
   * Generate PR preview without creating
   * Works in both offline and full modes
   *
   * @see REQ-CG-v234-001
   * @see DES-CG-v234-001
   */
  previewSuggestion(suggestion: RefactoringSuggestion): PRPreview {
    this.ensureState('offline', 'full');

    const branchName = generateBranchName(suggestion);
    const commitMessage = generateCommitMessage(suggestion);
    const title = this.templateGenerator.generateTitle(suggestion);
    const diffs = this.applier!.preview(suggestion);
    const body = this.templateGenerator.generate(suggestion, diffs);
    const baseBranch = this.git!.getDefaultBranch();

    return {
      branchName,
      baseBranch,
      title,
      body,
      diffs,
      commitMessage,
    };
  }

  /**
   * Create a PR from a refactoring suggestion
   * Requires full initialization (GitHub authentication)
   *
   * @see REQ-CG-PR-002, REQ-CG-PR-003, REQ-CG-PR-004, REQ-CG-PR-005
   */
  async create(options: PRCreateOptions): Promise<PRCreateResult> {
    this.ensureState('full');

    const { suggestion, dryRun } = options;
    const warnings: string[] = [];

    try {
      this.emit('pr:start', { suggestion });

      // Generate branch name
      const branchName = options.branchName ?? generateBranchName(suggestion);

      // Check for uncommitted changes
      if (this.git!.hasUncommittedChanges()) {
        warnings.push('Repository has uncommitted changes. They will be stashed.');
        this.git!.stash('musubix-pr-creator-auto-stash');
      }

      // Dry run mode - just preview
      if (dryRun) {
        return this.dryRun(options, branchName);
      }

      // Determine base branch
      const baseBranch = options.baseBranch ?? this.git!.getDefaultBranch();

      // Create and checkout new branch
      this.emit('pr:branch', { name: branchName });
      this.git!.createBranch(branchName, baseBranch);

      // Apply refactoring changes
      const diffs = this.applier!.preview(suggestion);
      for (const diff of diffs) {
        this.emit('pr:applying', { file: diff.filePath, changes: 1 });
      }

      const applyResult = this.applier!.apply(suggestion);
      if (!applyResult.success) {
        // Rollback branch
        this.git!.checkout(this.originalBranch!);
        this.git!.deleteBranch(branchName, true);
        return {
          success: false,
          branchName,
          filesChanged: [],
          linesAdded: 0,
          linesDeleted: 0,
          error: `Failed to apply changes: ${applyResult.error}`,
          warnings,
        };
      }

      // Stage all changes
      this.git!.stageAll();

      // Generate commit message
      const commitMessage = generateCommitMessage(suggestion);

      // Commit
      const commitInfo = this.git!.commit(commitMessage);
      this.emit('pr:commit', { hash: commitInfo.hash, message: commitMessage });

      // Push to remote
      this.emit('pr:push', { branch: branchName, remote: this.config.remote! });
      this.git!.push({ setUpstream: true });

      // Generate PR body
      const prTitle = options.title ?? this.templateGenerator.generateTitle(suggestion);
      const prBody = options.body ?? this.templateGenerator.generate(suggestion, diffs);

      // Create PR
      const pr = await this.github!.createPullRequest({
        title: prTitle,
        body: prBody,
        head: branchName,
        base: baseBranch,
        draft: options.draft,
      });

      this.emit('pr:created', { pr });

      // Add labels, assignees, reviewers
      if (options.labels && options.labels.length > 0) {
        await this.github!.addLabels(pr.number, options.labels);
      }
      if (options.assignees && options.assignees.length > 0) {
        await this.github!.addAssignees(pr.number, options.assignees);
      }
      if (options.reviewers && options.reviewers.length > 0) {
        await this.github!.addReviewers(pr.number, options.reviewers);
      }

      // Calculate stats
      const stats = this.git!.getDiffStats(baseBranch);

      const result: PRCreateResult = {
        success: true,
        pr,
        branchName,
        commitHash: commitInfo.hash,
        filesChanged: applyResult.filesModified,
        linesAdded: stats.additions,
        linesDeleted: stats.deletions,
        warnings: warnings.length > 0 ? warnings : undefined,
      };

      this.emit('pr:complete', { result });

      // Switch back to original branch
      this.git!.checkout(this.originalBranch!);

      return result;
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : String(error);
      this.emit('pr:error', { error: error as Error, stage: 'create' });

      // Attempt cleanup
      try {
        if (this.git && this.originalBranch) {
          const currentBranch = this.git.getCurrentBranch();
          if (currentBranch !== this.originalBranch) {
            this.git.checkout(this.originalBranch);
          }
        }
      } catch {
        // Ignore cleanup errors
      }

      return {
        success: false,
        branchName: options.branchName ?? generateBranchName(suggestion),
        filesChanged: [],
        linesAdded: 0,
        linesDeleted: 0,
        error: errorMessage,
        warnings: warnings.length > 0 ? warnings : undefined,
      };
    }
  }

  /**
   * Preview PR creation without actually creating
   * @see REQ-CG-PR-007
   */
  async preview(options: PRCreateOptions): Promise<PRPreview> {
    this.ensureInitialized();

    const { suggestion } = options;
    const branchName = options.branchName ?? generateBranchName(suggestion);
    const baseBranch = options.baseBranch ?? this.git!.getDefaultBranch();

    // Generate preview
    const diffs = this.applier!.preview(suggestion);
    const title = options.title ?? this.templateGenerator.generateTitle(suggestion);
    const body = options.body ?? this.templateGenerator.generate(suggestion, diffs);
    const commitMessage = generateCommitMessage(suggestion);

    return {
      branchName,
      baseBranch,
      title,
      body,
      diffs,
      commitMessage,
    };
  }

  /**
   * Validate a suggestion can be applied
   */
  validate(suggestion: RefactoringSuggestion): { valid: boolean; reason?: string } {
    this.ensureInitialized();
    const result = this.applier!.canApply(suggestion);
    return { valid: result.canApply, reason: result.reason };
  }

  // ============================================================================
  // Private Helpers
  // ============================================================================

  /**
   * Dry run implementation
   */
  private dryRun(options: PRCreateOptions, branchName: string): PRCreateResult {
    const { suggestion } = options;
    const baseBranch = options.baseBranch ?? this.git!.getDefaultBranch();

    // Generate preview
    const diffs = this.applier!.preview(suggestion);
    const title = options.title ?? this.templateGenerator.generateTitle(suggestion);
    const body = options.body ?? this.templateGenerator.generate(suggestion, diffs);
    const commitMessage = generateCommitMessage(suggestion);

    // Calculate stats from diffs
    let linesAdded = 0;
    let linesDeleted = 0;
    for (const diff of diffs) {
      linesAdded += diff.additions;
      linesDeleted += diff.deletions;
    }

    return {
      success: true,
      branchName,
      filesChanged: diffs.map(d => d.filePath),
      linesAdded,
      linesDeleted,
      preview: {
        branchName,
        baseBranch,
        title,
        body,
        diffs,
        commitMessage,
      },
    };
  }

  /**
   * Ensure initialized before operations (legacy)
   * @deprecated Use ensureState() instead
   */
  private ensureInitialized(): void {
    if (!this.initialized) {
      throw PRCreatorError.fromCode('NOT_INITIALIZED');
    }
  }

  /**
   * Ensure PRCreator is in one of the allowed states
   * @see DES-CG-v234-003
   */
  private ensureState(...allowed: PRCreatorState[]): void {
    if (!allowed.includes(this.state)) {
      if (this.state === 'uninitialized') {
        throw PRCreatorError.fromCode('NOT_INITIALIZED');
      } else if (this.state === 'offline' && allowed.includes('full')) {
        throw PRCreatorError.fromCode('OFFLINE_MODE');
      }
      throw PRCreatorError.fromCode('NOT_INITIALIZED');
    }
  }

  // ============================================================================
  // Event Typing
  // ============================================================================

  /**
   * Typed event emitter methods
   */
  override emit<K extends keyof PRCreatorEvents>(
    event: K,
    data: PRCreatorEvents[K]
  ): boolean {
    return super.emit(event, data);
  }

  override on<K extends keyof PRCreatorEvents>(
    event: K,
    listener: (data: PRCreatorEvents[K]) => void
  ): this {
    return super.on(event, listener);
  }

  override once<K extends keyof PRCreatorEvents>(
    event: K,
    listener: (data: PRCreatorEvents[K]) => void
  ): this {
    return super.once(event, listener);
  }
}

/**
 * Create a PRCreator instance
 */
export function createPRCreator(repoPath: string, options?: Partial<PRCreatorConfig>): PRCreator {
  return new PRCreator({
    repoPath,
    ...options,
  });
}

/**
 * Quick PR creation helper
 *
 * One-shot function to create a PR from a suggestion.
 *
 * @example
 * ```typescript
 * const result = await createRefactoringPR(
 *   '/path/to/repo',
 *   suggestion,
 *   { labels: ['refactoring'] }
 * );
 * ```
 */
export async function createRefactoringPR(
  repoPath: string,
  suggestion: RefactoringSuggestion,
  options?: Partial<PRCreateOptions>
): Promise<PRCreateResult> {
  const creator = createPRCreator(repoPath);
  const initResult = await creator.initialize();

  if (!initResult.success) {
    return {
      success: false,
      branchName: generateBranchName(suggestion),
      filesChanged: [],
      linesAdded: 0,
      linesDeleted: 0,
      error: initResult.error,
    };
  }

  return creator.create({
    suggestion,
    ...options,
  });
}
