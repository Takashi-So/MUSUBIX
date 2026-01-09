/**
 * @nahisaho/musubix-codegraph/pr - PR Creation Module
 *
 * Automatic PR generation from refactoring suggestions
 *
 * @packageDocumentation
 * @module @nahisaho/musubix-codegraph/pr
 *
 * @see REQ-CG-PR-001 - REQ-CG-PR-009
 * @see DES-CG-PR-001 - DES-CG-PR-006
 */

// Main PR Creator
export {
  PRCreator,
  createPRCreator,
  createRefactoringPR,
  type PRCreatorConfig,
  type PRCreatorState,
} from './pr-creator.js';

// Error Handling (v2.3.4 NEW)
export {
  PRCreatorError,
  PRErrorMessages,
  type PRErrorCode,
} from './errors.js';

// Git Operations
export {
  GitOperations,
  createGitOperations,
} from './git-operations.js';

// GitHub Adapter
export {
  GitHubAdapter,
  createGitHubAdapter,
  type CreatePROptions,
  type UpdatePROptions,
  type PRLabel,
} from './github-adapter.js';

// Refactoring Applier
export {
  RefactoringApplier,
  createRefactoringApplier,
  type ApplyChangeResult,
  type ApplyResult,
  type ApplyOptions,
} from './refactoring-applier.js';

// PR Template Generator
export {
  PRTemplateGenerator,
  createPRTemplateGenerator,
  generateSimplePRBody,
  generatePRTitle,
  type PRTemplateOptions,
} from './pr-template.js';

// Types
export type {
  // Refactoring
  RefactoringType,
  RefactoringSeverity,
  CodeChange,
  RefactoringSuggestion,

  // Git
  BranchInfo,
  CommitInfo,
  GitOperationOptions,

  // GitHub
  GitHubConfig,
  GitHubAuthMethod,
  GitHubAuthResult,
  PRInfo,

  // PR Creation
  PRCreateOptions,
  PRCreateResult,
  PRPreview,
  FileDiff,

  // Batch
  BatchRefactoringOptions,
  BatchRefactoringResult,

  // Events
  PRCreatorEvents,

  // Utilities
  ConventionalCommitType,
} from './types.js';

// Utility Functions
export {
  REFACTORING_TO_COMMIT_TYPE,
  generateBranchName,
  generateCommitMessage,
} from './types.js';
