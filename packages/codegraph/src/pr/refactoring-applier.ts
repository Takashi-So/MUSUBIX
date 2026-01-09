/**
 * @nahisaho/musubix-codegraph - Refactoring Applier
 *
 * Applies refactoring suggestions to source files
 *
 * @packageDocumentation
 * @module @nahisaho/musubix-codegraph/pr
 *
 * @see REQ-CG-PR-002 - Auto Apply Refactoring
 * @see DES-CG-PR-004 - Class Design
 */

import { existsSync, readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join, dirname } from 'node:path';
import type {
  RefactoringSuggestion,
  CodeChange,
  FileDiff,
} from './types.js';

/**
 * Result of applying a single change
 */
export interface ApplyChangeResult {
  /** Whether the change was applied successfully */
  success: boolean;
  /** File path */
  filePath: string;
  /** Error message if failed */
  error?: string;
  /** Backup path if backup was created */
  backupPath?: string;
}

/**
 * Result of applying all changes in a suggestion
 */
export interface ApplyResult {
  /** Overall success status */
  success: boolean;
  /** Files modified */
  filesModified: string[];
  /** Files created */
  filesCreated: string[];
  /** Files deleted */
  filesDeleted: string[];
  /** Individual change results */
  changeResults: ApplyChangeResult[];
  /** Overall error if failed */
  error?: string;
}

/**
 * Options for applying refactoring
 */
export interface ApplyOptions {
  /** Repository root path */
  repoPath: string;
  /** Create backups before modifying */
  createBackups?: boolean;
  /** Backup directory (default: .musubix-backup) */
  backupDir?: string;
  /** Validate changes before applying */
  validate?: boolean;
  /** Dry run - don't actually modify files */
  dryRun?: boolean;
}

/**
 * Refactoring Applier
 *
 * Applies code changes from refactoring suggestions to source files.
 * Supports validation, backup, and rollback.
 *
 * @see DES-CG-PR-004
 * @example
 * ```typescript
 * const applier = new RefactoringApplier({ repoPath: '/path/to/repo' });
 * const result = await applier.apply(suggestion);
 * if (!result.success) {
 *   await applier.rollback();
 * }
 * ```
 */
export class RefactoringApplier {
  private readonly repoPath: string;
  private readonly createBackups: boolean;
  private readonly backupDir: string;
  private readonly validate: boolean;
  private appliedChanges: Map<string, string> = new Map(); // filePath -> originalContent

  /**
   * Create a new RefactoringApplier
   * @param options - Apply options
   */
  constructor(options: ApplyOptions) {
    this.repoPath = options.repoPath;
    this.createBackups = options.createBackups ?? true;
    this.backupDir = options.backupDir ?? '.musubix-backup';
    this.validate = options.validate ?? true;
  }

  // ============================================================================
  // Main Operations
  // ============================================================================

  /**
   * Apply a refactoring suggestion
   * @see REQ-CG-PR-002
   */
  apply(suggestion: RefactoringSuggestion): ApplyResult {
    const changeResults: ApplyChangeResult[] = [];
    const filesModified: string[] = [];
    const filesCreated: string[] = [];
    const filesDeleted: string[] = [];

    // Clear previous applied changes tracking
    this.appliedChanges.clear();

    try {
      // Validate all changes first
      if (this.validate) {
        const validationError = this.validateChanges(suggestion.changes);
        if (validationError) {
          return {
            success: false,
            filesModified: [],
            filesCreated: [],
            filesDeleted: [],
            changeResults: [],
            error: validationError,
          };
        }
      }

      // Group changes by file for efficient processing
      const changesByFile = this.groupChangesByFile(suggestion.changes);

      // Apply changes to each file
      for (const [filePath, changes] of changesByFile) {
        const result = this.applyChangesToFile(filePath, changes);
        changeResults.push(result);

        if (result.success) {
          filesModified.push(filePath);
        } else {
          // Rollback on failure
          this.rollback();
          return {
            success: false,
            filesModified: [],
            filesCreated: [],
            filesDeleted: [],
            changeResults,
            error: `Failed to apply changes to ${filePath}: ${result.error}`,
          };
        }
      }

      return {
        success: true,
        filesModified,
        filesCreated,
        filesDeleted,
        changeResults,
      };
    } catch (error) {
      // Rollback on any error
      this.rollback();
      return {
        success: false,
        filesModified: [],
        filesCreated: [],
        filesDeleted: [],
        changeResults,
        error: error instanceof Error ? error.message : String(error),
      };
    }
  }

  /**
   * Preview changes without applying
   * @see REQ-CG-PR-007
   */
  preview(suggestion: RefactoringSuggestion): FileDiff[] {
    const diffs: FileDiff[] = [];
    const changesByFile = this.groupChangesByFile(suggestion.changes);

    for (const [filePath, changes] of changesByFile) {
      const fullPath = join(this.repoPath, filePath);

      if (!existsSync(fullPath)) {
        // New file
        const newContent = changes.map(c => c.newCode).join('\n');
        diffs.push({
          filePath,
          changeType: 'added',
          diff: this.generateUnifiedDiff('', newContent, filePath),
          additions: newContent.split('\n').length,
          deletions: 0,
        });
        continue;
      }

      const originalContent = readFileSync(fullPath, 'utf-8');
      const newContent = this.applyChangesToContent(originalContent, changes);
      const diff = this.generateUnifiedDiff(originalContent, newContent, filePath);
      const stats = this.calculateDiffStats(originalContent, newContent);

      diffs.push({
        filePath,
        changeType: 'modified',
        diff,
        additions: stats.additions,
        deletions: stats.deletions,
      });
    }

    return diffs;
  }

  /**
   * Rollback applied changes
   */
  rollback(): void {
    for (const [filePath, originalContent] of this.appliedChanges) {
      const fullPath = join(this.repoPath, filePath);
      try {
        writeFileSync(fullPath, originalContent, 'utf-8');
      } catch {
        // Best effort rollback
        console.error(`Failed to rollback ${filePath}`);
      }
    }
    this.appliedChanges.clear();
  }

  // ============================================================================
  // Validation
  // ============================================================================

  /**
   * Validate changes can be applied
   */
  validateChanges(changes: CodeChange[]): string | null {
    for (const change of changes) {
      const fullPath = join(this.repoPath, change.filePath);

      // Check file exists (for modifications)
      if (!existsSync(fullPath)) {
        // Allow if this is a new file (originalCode is empty)
        if (change.originalCode.trim() !== '') {
          return `File not found: ${change.filePath}`;
        }
        continue;
      }

      // Validate line numbers
      const content = readFileSync(fullPath, 'utf-8');
      const lines = content.split('\n');

      if (change.startLine < 1) {
        return `Invalid start line ${change.startLine} in ${change.filePath}`;
      }

      if (change.endLine > lines.length) {
        return `End line ${change.endLine} exceeds file length ${lines.length} in ${change.filePath}`;
      }

      if (change.startLine > change.endLine) {
        return `Start line ${change.startLine} is after end line ${change.endLine} in ${change.filePath}`;
      }

      // Validate original code matches
      const actualLines = lines.slice(change.startLine - 1, change.endLine);
      const actualCode = actualLines.join('\n');
      const expectedCode = change.originalCode;

      if (this.normalizeWhitespace(actualCode) !== this.normalizeWhitespace(expectedCode)) {
        return `Original code mismatch in ${change.filePath}:${change.startLine}-${change.endLine}. ` +
          `Expected:\n${expectedCode}\n\nActual:\n${actualCode}`;
      }
    }

    return null;
  }

  /**
   * Check if a suggestion can be applied
   */
  canApply(suggestion: RefactoringSuggestion): { canApply: boolean; reason?: string } {
    const error = this.validateChanges(suggestion.changes);
    if (error) {
      return { canApply: false, reason: error };
    }
    return { canApply: true };
  }

  // ============================================================================
  // Private Helpers
  // ============================================================================

  /**
   * Group changes by file
   */
  private groupChangesByFile(changes: CodeChange[]): Map<string, CodeChange[]> {
    const byFile = new Map<string, CodeChange[]>();

    for (const change of changes) {
      const existing = byFile.get(change.filePath) ?? [];
      existing.push(change);
      byFile.set(change.filePath, existing);
    }

    // Sort changes within each file by line number (descending)
    // This allows applying changes from bottom to top without line number shifts
    for (const [_filePath, fileChanges] of byFile) {
      fileChanges.sort((a, b) => (b.startLine ?? 0) - (a.startLine ?? 0));
    }

    return byFile;
  }

  /**
   * Apply changes to a single file
   */
  private applyChangesToFile(filePath: string, changes: CodeChange[]): ApplyChangeResult {
    const fullPath = join(this.repoPath, filePath);

    try {
      // Read original content
      let content = '';
      if (existsSync(fullPath)) {
        content = readFileSync(fullPath, 'utf-8');
        // Store for potential rollback
        this.appliedChanges.set(filePath, content);
      }

      // Create backup if enabled
      if (this.createBackups && content) {
        const backupPath = this.createBackup(filePath, content);
        if (!backupPath) {
          return {
            success: false,
            filePath,
            error: 'Failed to create backup',
          };
        }
      }

      // Apply changes
      const newContent = this.applyChangesToContent(content, changes);

      // Ensure directory exists
      const dir = dirname(fullPath);
      if (!existsSync(dir)) {
        mkdirSync(dir, { recursive: true });
      }

      // Write new content
      writeFileSync(fullPath, newContent, 'utf-8');

      return {
        success: true,
        filePath,
      };
    } catch (error) {
      return {
        success: false,
        filePath,
        error: error instanceof Error ? error.message : String(error),
      };
    }
  }

  /**
   * Apply changes to content string
   */
  private applyChangesToContent(content: string, changes: CodeChange[]): string {
    const lines = content.split('\n');

    // Changes should already be sorted by line number descending
    for (const change of changes) {
      const beforeLines = lines.slice(0, change.startLine - 1);
      const afterLines = lines.slice(change.endLine);
      const newLines = change.newCode.split('\n');

      lines.length = 0;
      lines.push(...beforeLines, ...newLines, ...afterLines);
    }

    return lines.join('\n');
  }

  /**
   * Create a backup of a file
   */
  private createBackup(filePath: string, content: string): string | null {
    try {
      const backupPath = join(this.repoPath, this.backupDir, filePath);
      const backupDir = dirname(backupPath);

      if (!existsSync(backupDir)) {
        mkdirSync(backupDir, { recursive: true });
      }

      writeFileSync(backupPath, content, 'utf-8');
      return backupPath;
    } catch {
      return null;
    }
  }

  /**
   * Normalize whitespace for comparison
   */
  private normalizeWhitespace(str: string): string {
    return str
      .split('\n')
      .map(line => line.trimEnd())
      .join('\n')
      .trim();
  }

  /**
   * Generate unified diff format
   */
  private generateUnifiedDiff(original: string, modified: string, filePath: string): string {
    const originalLines = original.split('\n');
    const modifiedLines = modified.split('\n');

    const diff: string[] = [];
    diff.push(`--- a/${filePath}`);
    diff.push(`+++ b/${filePath}`);

    // Simple line-by-line diff
    const maxLen = Math.max(originalLines.length, modifiedLines.length);
    let contextStart = -1;
    const hunks: Array<{ start: number; lines: string[] }> = [];
    let currentHunk: string[] = [];

    for (let i = 0; i < maxLen; i++) {
      const origLine = originalLines[i] ?? '';
      const modLine = modifiedLines[i] ?? '';

      if (origLine !== modLine) {
        if (contextStart === -1) {
          contextStart = Math.max(0, i - 3);
          // Add context before
          for (let j = contextStart; j < i; j++) {
            currentHunk.push(` ${originalLines[j] ?? ''}`);
          }
        }
        if (i < originalLines.length) {
          currentHunk.push(`-${origLine}`);
        }
        if (i < modifiedLines.length) {
          currentHunk.push(`+${modLine}`);
        }
      } else if (contextStart !== -1) {
        currentHunk.push(` ${origLine}`);
        // Check if we should end the hunk (3 lines of context after changes)
        const recentChanges = currentHunk.slice(-4).some(l => l.startsWith('+') || l.startsWith('-'));
        if (!recentChanges) {
          hunks.push({ start: contextStart, lines: currentHunk });
          currentHunk = [];
          contextStart = -1;
        }
      }
    }

    if (currentHunk.length > 0) {
      hunks.push({ start: contextStart, lines: currentHunk });
    }

    // Format hunks
    for (const hunk of hunks) {
      const origCount = hunk.lines.filter(l => l.startsWith(' ') || l.startsWith('-')).length;
      const modCount = hunk.lines.filter(l => l.startsWith(' ') || l.startsWith('+')).length;
      diff.push(`@@ -${hunk.start + 1},${origCount} +${hunk.start + 1},${modCount} @@`);
      diff.push(...hunk.lines);
    }

    return diff.join('\n');
  }

  /**
   * Calculate diff statistics
   */
  private calculateDiffStats(original: string, modified: string): { additions: number; deletions: number } {
    const origLines = new Set(original.split('\n'));
    const modLines = new Set(modified.split('\n'));

    let additions = 0;
    let deletions = 0;

    for (const line of modLines) {
      if (!origLines.has(line)) {
        additions++;
      }
    }

    for (const line of origLines) {
      if (!modLines.has(line)) {
        deletions++;
      }
    }

    return { additions, deletions };
  }
}

/**
 * Create a RefactoringApplier instance
 */
export function createRefactoringApplier(repoPath: string, options?: Partial<ApplyOptions>): RefactoringApplier {
  return new RefactoringApplier({
    repoPath,
    ...options,
  });
}
