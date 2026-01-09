/**
 * @nahisaho/musubix-codegraph/pr - Error Definitions
 *
 * Custom error classes for PR creation operations
 *
 * @packageDocumentation
 * @module @nahisaho/musubix-codegraph/pr
 *
 * @see REQ-CG-v234-004 - Error Message Improvement
 * @see DES-CG-v234-004 - Error Class Design
 */

// ============================================================================
// Error Codes
// ============================================================================

/**
 * Error codes for PRCreator operations
 * @see DES-CG-v234-004
 */
export type PRErrorCode =
  | 'NOT_INITIALIZED'
  | 'OFFLINE_MODE'
  | 'AUTH_FAILED'
  | 'REPO_NOT_FOUND'
  | 'REMOTE_PARSE_FAILED'
  | 'APPLY_FAILED'
  | 'BRANCH_EXISTS'
  | 'PUSH_FAILED'
  | 'PR_CREATE_FAILED';

// ============================================================================
// Error Messages with Suggestions
// ============================================================================

/**
 * Error message definitions with actionable suggestions
 * @see REQ-CG-v234-004
 */
export const PRErrorMessages: Record<PRErrorCode, { message: string; suggestion: string }> = {
  NOT_INITIALIZED: {
    message: 'PRCreator is not initialized',
    suggestion: 'Call initializeOffline() for preview or initialize() for full functionality',
  },
  OFFLINE_MODE: {
    message: 'Cannot perform this operation in offline mode',
    suggestion: 'Call initialize() to authenticate with GitHub',
  },
  AUTH_FAILED: {
    message: 'GitHub authentication failed',
    suggestion: "Run 'gh auth login' or set GITHUB_TOKEN environment variable. For preview-only, use initializeOffline() instead",
  },
  REPO_NOT_FOUND: {
    message: 'Git repository not found',
    suggestion: 'Ensure the path is a valid git repository (contains .git directory)',
  },
  REMOTE_PARSE_FAILED: {
    message: 'Could not parse GitHub owner/repo from remote URL',
    suggestion: 'Ensure the remote URL is a valid GitHub URL (e.g., git@github.com:owner/repo.git)',
  },
  APPLY_FAILED: {
    message: 'Failed to apply refactoring changes',
    suggestion: 'Check file permissions and ensure target files exist',
  },
  BRANCH_EXISTS: {
    message: 'Branch already exists',
    suggestion: 'Use a different branch name or delete the existing branch',
  },
  PUSH_FAILED: {
    message: 'Failed to push changes to remote',
    suggestion: 'Check your network connection and repository permissions',
  },
  PR_CREATE_FAILED: {
    message: 'Failed to create pull request on GitHub',
    suggestion: 'Verify your GitHub token has repo permissions and the base branch exists',
  },
};

// ============================================================================
// Error Class
// ============================================================================

/**
 * Custom error class for PRCreator operations
 *
 * Includes error code and actionable suggestion for resolution
 *
 * @example
 * ```typescript
 * throw new PRCreatorError(
 *   'PRCreator is not initialized',
 *   'NOT_INITIALIZED',
 *   'Call initializeOffline() for preview'
 * );
 * ```
 *
 * @see REQ-CG-v234-004
 * @see DES-CG-v234-004
 */
export class PRCreatorError extends Error {
  /**
   * Create a new PRCreatorError
   * @param message - Error message
   * @param code - Error code for programmatic handling
   * @param suggestion - Actionable suggestion for resolution
   */
  constructor(
    message: string,
    public readonly code: PRErrorCode,
    public readonly suggestion?: string
  ) {
    super(message);
    this.name = 'PRCreatorError';

    // Ensure proper prototype chain
    Object.setPrototypeOf(this, PRCreatorError.prototype);
  }

  /**
   * Get formatted error message with suggestion
   */
  getFullMessage(): string {
    if (this.suggestion) {
      return `${this.message}\n\n💡 Suggestion: ${this.suggestion}`;
    }
    return this.message;
  }

  /**
   * Create error from error code
   * @param code - Error code
   * @param additionalInfo - Optional additional context
   */
  static fromCode(code: PRErrorCode, additionalInfo?: string): PRCreatorError {
    const errorDef = PRErrorMessages[code];
    const message = additionalInfo
      ? `${errorDef.message}: ${additionalInfo}`
      : errorDef.message;
    return new PRCreatorError(message, code, errorDef.suggestion);
  }
}
