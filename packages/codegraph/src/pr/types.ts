/**
 * @nahisaho/musubix-codegraph - PR Creation Type Definitions
 *
 * Types for automatic refactoring PR generation
 *
 * @packageDocumentation
 * @module @nahisaho/musubix-codegraph/pr
 *
 * @see REQ-CG-PR-001 - GitHub Authentication
 * @see REQ-CG-PR-002 - Auto Apply Refactoring
 * @see DES-CG-PR-003 - Type Definitions
 */

// ============================================================================
// Refactoring Types
// ============================================================================

/**
 * Types of refactoring operations
 * @see REQ-CG-PR-002
 */
export type RefactoringType =
  | 'extract_interface'
  | 'extract_method'
  | 'extract_class'
  | 'inline'
  | 'rename'
  | 'move'
  | 'security_fix'
  | 'performance'
  | 'simplify';

/**
 * Severity levels for refactoring suggestions
 */
export type RefactoringSeverity = 'critical' | 'high' | 'medium' | 'low' | 'info';

/**
 * A single code change within a file
 * @see DES-CG-PR-003
 */
export interface CodeChange {
  /** File path relative to repository root */
  filePath: string;
  /** Starting line number (1-based) */
  startLine: number;
  /** Ending line number (1-based, inclusive) */
  endLine: number;
  /** Starting column (0-based) */
  startColumn?: number;
  /** Ending column (0-based) */
  endColumn?: number;
  /** Original code to be replaced */
  originalCode: string;
  /** New code after refactoring */
  newCode: string;
  /** Description of the change */
  description: string;
}

/**
 * Refactoring suggestion from CodeGraph analysis
 * @see REQ-CG-PR-002
 * @see DES-CG-PR-003
 */
export interface RefactoringSuggestion {
  /** Unique identifier for the suggestion */
  id: string;
  /** Entity ID that this suggestion targets */
  entityId: string;
  /** Type of refactoring */
  type: RefactoringType;
  /** Human-readable title */
  title: string;
  /** Detailed description of the refactoring */
  description: string;
  /** Reason why this refactoring is suggested */
  reason: string;
  /** Severity/priority of the suggestion */
  severity: RefactoringSeverity;
  /** List of code changes to apply */
  changes: CodeChange[];
  /** Estimated impact (files affected) */
  impact: {
    filesAffected: number;
    linesChanged: number;
    dependencies: string[];
  };
  /** Related CWE if security-related */
  cwe?: string;
  /** Confidence score (0-1) */
  confidence: number;
  /** Timestamp when suggestion was generated */
  createdAt: Date;
}

// ============================================================================
// Git Operation Types
// ============================================================================

/**
 * Git branch information
 */
export interface BranchInfo {
  /** Branch name */
  name: string;
  /** Whether this is the current branch */
  current: boolean;
  /** Remote tracking branch if any */
  tracking?: string;
  /** Latest commit hash */
  commit: string;
}

/**
 * Git commit information
 */
export interface CommitInfo {
  /** Commit hash */
  hash: string;
  /** Commit message */
  message: string;
  /** Author name */
  author: string;
  /** Author email */
  email: string;
  /** Commit date */
  date: Date;
}

/**
 * Options for Git operations
 * @see REQ-CG-PR-003
 */
export interface GitOperationOptions {
  /** Repository root path */
  repoPath: string;
  /** Base branch to create from (default: current branch) */
  baseBranch?: string;
  /** Remote name (default: 'origin') */
  remote?: string;
  /** Whether to force push */
  force?: boolean;
}

// ============================================================================
// GitHub Types
// ============================================================================

/**
 * GitHub authentication configuration
 * @see REQ-CG-PR-001
 * @see DES-CG-PR-003
 */
export interface GitHubConfig {
  /** GitHub Personal Access Token */
  token?: string;
  /** Repository owner (user or organization) */
  owner: string;
  /** Repository name */
  repo: string;
  /** GitHub API base URL (for GitHub Enterprise) */
  baseUrl?: string;
}

/**
 * GitHub authentication method
 */
export type GitHubAuthMethod = 'token' | 'gh-cli' | 'none';

/**
 * GitHub authentication result
 */
export interface GitHubAuthResult {
  /** Whether authentication succeeded */
  authenticated: boolean;
  /** Authentication method used */
  method: GitHubAuthMethod;
  /** Authenticated username */
  username?: string;
  /** Error message if authentication failed */
  error?: string;
}

/**
 * Pull Request creation result
 * @see REQ-CG-PR-005
 */
export interface PRInfo {
  /** PR number */
  number: number;
  /** PR URL */
  url: string;
  /** PR title */
  title: string;
  /** PR state */
  state: 'open' | 'closed' | 'merged';
  /** Head branch */
  head: string;
  /** Base branch */
  base: string;
  /** Created timestamp */
  createdAt: Date;
}

// ============================================================================
// PR Creation Types
// ============================================================================

/**
 * Options for PR creation
 * @see REQ-CG-PR-005
 * @see REQ-CG-PR-007
 * @see DES-CG-PR-003
 */
export interface PRCreateOptions {
  /** Refactoring suggestion to apply */
  suggestion: RefactoringSuggestion;
  /** Custom branch name (default: auto-generated) */
  branchName?: string;
  /** Custom PR title (default: from suggestion) */
  title?: string;
  /** Custom PR body (default: auto-generated) */
  body?: string;
  /** Base branch for PR (default: main/master) */
  baseBranch?: string;
  /** Labels to add to PR */
  labels?: string[];
  /** Assignees for PR */
  assignees?: string[];
  /** Reviewers for PR */
  reviewers?: string[];
  /** Whether to create as draft PR */
  draft?: boolean;
  /** Dry run mode - preview without creating */
  dryRun?: boolean;
  /** Auto-merge settings */
  autoMerge?: {
    enabled: boolean;
    method: 'merge' | 'squash' | 'rebase';
  };
}

/**
 * Result of PR creation operation
 * @see DES-CG-PR-003
 */
export interface PRCreateResult {
  /** Whether operation succeeded */
  success: boolean;
  /** Created PR info (if not dry run) */
  pr?: PRInfo;
  /** Branch name created */
  branchName: string;
  /** Commit hash */
  commitHash?: string;
  /** Files changed */
  filesChanged: string[];
  /** Lines added */
  linesAdded: number;
  /** Lines deleted */
  linesDeleted: number;
  /** Preview of changes (for dry run) */
  preview?: PRPreview;
  /** Error message if failed */
  error?: string;
  /** Warnings during operation */
  warnings?: string[];
}

/**
 * Preview of PR changes (for dry run mode)
 * @see REQ-CG-PR-007
 */
export interface PRPreview {
  /** Branch that would be created */
  branchName: string;
  /** Base branch for the PR */
  baseBranch: string;
  /** PR title */
  title: string;
  /** PR body (Markdown) */
  body: string;
  /** File diffs */
  diffs: FileDiff[];
  /** Commit message */
  commitMessage: string;
}

/**
 * Diff for a single file
 */
export interface FileDiff {
  /** File path */
  filePath: string;
  /** Type of change */
  changeType: 'added' | 'modified' | 'deleted';
  /** Unified diff content */
  diff: string;
  /** Lines added */
  additions: number;
  /** Lines deleted */
  deletions: number;
}

// ============================================================================
// Batch Operation Types
// ============================================================================

/**
 * Options for batch refactoring
 * @see REQ-CG-PR-008
 */
export interface BatchRefactoringOptions {
  /** Multiple suggestions to apply */
  suggestions: RefactoringSuggestion[];
  /** Strategy for handling multiple suggestions */
  strategy: 'single-pr' | 'multiple-prs' | 'grouped';
  /** Grouping criteria (for 'grouped' strategy) */
  groupBy?: 'type' | 'file' | 'severity';
  /** Base branch */
  baseBranch?: string;
  /** Common labels for all PRs */
  labels?: string[];
  /** Dry run mode */
  dryRun?: boolean;
}

/**
 * Result of batch refactoring operation
 */
export interface BatchRefactoringResult {
  /** Overall success status */
  success: boolean;
  /** Total suggestions processed */
  totalSuggestions: number;
  /** Successfully applied suggestions */
  appliedSuggestions: number;
  /** Failed suggestions */
  failedSuggestions: number;
  /** PRs created */
  prs: PRCreateResult[];
  /** Errors encountered */
  errors: Array<{
    suggestionId: string;
    error: string;
  }>;
}

// ============================================================================
// Event Types
// ============================================================================

/**
 * Events emitted during PR creation
 */
export interface PRCreatorEvents {
  /** Emitted when starting PR creation */
  'pr:start': { suggestion: RefactoringSuggestion };
  /** Emitted when applying changes */
  'pr:applying': { file: string; changes: number };
  /** Emitted when creating branch */
  'pr:branch': { name: string };
  /** Emitted when committing */
  'pr:commit': { hash: string; message: string };
  /** Emitted when pushing */
  'pr:push': { branch: string; remote: string };
  /** Emitted when PR is created */
  'pr:created': { pr: PRInfo };
  /** Emitted on completion */
  'pr:complete': { result: PRCreateResult };
  /** Emitted on error */
  'pr:error': { error: Error; stage: string };
}

// ============================================================================
// Utility Types
// ============================================================================

/**
 * Conventional commit type
 * @see REQ-CG-PR-004
 */
export type ConventionalCommitType =
  | 'feat'
  | 'fix'
  | 'refactor'
  | 'perf'
  | 'security'
  | 'style'
  | 'docs'
  | 'test'
  | 'chore';

/**
 * Mapping from refactoring type to commit type
 */
export const REFACTORING_TO_COMMIT_TYPE: Record<RefactoringType, ConventionalCommitType> = {
  extract_interface: 'refactor',
  extract_method: 'refactor',
  extract_class: 'refactor',
  inline: 'refactor',
  rename: 'refactor',
  move: 'refactor',
  security_fix: 'security',
  performance: 'perf',
  simplify: 'refactor',
};

/**
 * Generate branch name from suggestion
 */
export function generateBranchName(suggestion: RefactoringSuggestion): string {
  const type = suggestion.type.replace(/_/g, '-');
  const entity = suggestion.entityId
    .replace(/[^a-zA-Z0-9]/g, '-')
    .toLowerCase()
    .slice(0, 30);
  const timestamp = Date.now().toString(36);
  return `refactor/${type}/${entity}-${timestamp}`;
}

/**
 * Generate conventional commit message
 * @see REQ-CG-PR-004
 */
export function generateCommitMessage(suggestion: RefactoringSuggestion): string {
  const commitType = REFACTORING_TO_COMMIT_TYPE[suggestion.type];
  const scope = suggestion.entityId.split('.')[0] || 'core';
  const subject = suggestion.title.toLowerCase().replace(/\.$/, '');

  let message = `${commitType}(${scope}): ${subject}`;

  // Add body with details
  if (suggestion.reason) {
    message += `\n\n${suggestion.reason}`;
  }

  // Add footer with metadata
  const footers: string[] = [];
  if (suggestion.cwe) {
    footers.push(`Fixes: ${suggestion.cwe}`);
  }
  footers.push(`Suggestion-ID: ${suggestion.id}`);

  if (footers.length > 0) {
    message += '\n\n' + footers.join('\n');
  }

  return message;
}
