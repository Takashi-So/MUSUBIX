/**
 * @fileoverview Patch Generator for Security Fixes
 * @module @nahisaho/musubix-security/remediation/patch-generator
 * 
 * Generates unified diff patches for security fixes that can be
 * applied using standard patch tools.
 */

import type { Fix, CodeEdit } from '../types/index.js';

// ============================================================================
// Types
// ============================================================================

/**
 * Generated patch
 */
export interface Patch {
  /** Patch ID */
  id: string;
  /** Fix reference */
  fixId: string;
  /** Vulnerability reference */
  vulnerabilityId: string;
  /** Patch format */
  format: PatchFormat;
  /** Patch content */
  content: string;
  /** Files affected */
  files: PatchFile[];
  /** Patch metadata */
  metadata: PatchMetadata;
  /** Generated timestamp */
  generatedAt: Date;
}

/**
 * Patch format
 */
export type PatchFormat = 'unified' | 'context' | 'git' | 'json';

/**
 * Patch file entry
 */
export interface PatchFile {
  /** Original file path */
  originalPath: string;
  /** Modified file path */
  modifiedPath: string;
  /** Hunks in this file */
  hunks: PatchHunk[];
  /** File mode changes */
  mode?: { old: string; new: string };
}

/**
 * Patch hunk
 */
export interface PatchHunk {
  /** Original line start */
  originalStart: number;
  /** Original line count */
  originalCount: number;
  /** Modified line start */
  modifiedStart: number;
  /** Modified line count */
  modifiedCount: number;
  /** Hunk lines */
  lines: PatchLine[];
}

/**
 * Patch line
 */
export interface PatchLine {
  /** Line type */
  type: 'context' | 'addition' | 'deletion';
  /** Line content */
  content: string;
}

/**
 * Patch metadata
 */
export interface PatchMetadata {
  /** Author */
  author?: string;
  /** Date */
  date: Date;
  /** Description */
  description: string;
  /** Vulnerability severity */
  severity?: string;
  /** CWE references */
  cwes?: string[];
  /** OWASP references */
  owasp?: string[];
  /** Tags */
  tags?: string[];
}

/**
 * Patch generation options
 */
export interface PatchGenerationOptions {
  /** Patch format */
  format?: PatchFormat;
  /** Context lines */
  contextLines?: number;
  /** Include metadata header */
  includeMetadata?: boolean;
  /** Author name */
  author?: string;
  /** Base path for files */
  basePath?: string;
}

/**
 * Patch application result
 */
export interface PatchApplicationResult {
  /** Whether application succeeded */
  success: boolean;
  /** Files modified */
  filesModified: string[];
  /** Hunks applied */
  hunksApplied: number;
  /** Hunks failed */
  hunksFailed: number;
  /** Errors */
  errors: string[];
  /** Warnings */
  warnings: string[];
}

/**
 * Patch generator options
 */
export interface PatchGeneratorOptions {
  /** Default format */
  defaultFormat?: PatchFormat;
  /** Default context lines */
  defaultContextLines?: number;
  /** Include severity in patches */
  includeSeverity?: boolean;
  /** Include remediation info */
  includeRemediation?: boolean;
}

// ============================================================================
// PatchGenerator Class
// ============================================================================

/**
 * Generator for security fix patches
 * 
 * @example
 * ```typescript
 * const generator = createPatchGenerator();
 * const patch = generator.generatePatch(fix, fileContents);
 * console.log(patch.content); // Unified diff
 * ```
 */
export class PatchGenerator {
  private options: Required<PatchGeneratorOptions>;

  constructor(options: PatchGeneratorOptions = {}) {
    this.options = {
      defaultFormat: options.defaultFormat ?? 'unified',
      defaultContextLines: options.defaultContextLines ?? 3,
      includeSeverity: options.includeSeverity ?? true,
      includeRemediation: options.includeRemediation ?? true,
    };
  }

  /**
   * Generate a patch for a fix
   */
  generatePatch(
    fix: Fix,
    fileContents: Map<string, string>,
    options: PatchGenerationOptions = {}
  ): Patch {
    const format = options.format ?? this.options.defaultFormat;
    const contextLines = options.contextLines ?? this.options.defaultContextLines;

    // Group edits by file
    const editsByFile = this.groupEditsByFile(fix.edits);

    // Generate patch files
    const files: PatchFile[] = [];
    for (const [filePath, edits] of editsByFile) {
      const originalContent = fileContents.get(filePath) || '';
      const patchFile = this.generatePatchFile(
        filePath,
        originalContent,
        edits,
        contextLines,
        options.basePath
      );
      files.push(patchFile);
    }

    // Generate patch content based on format
    const content = this.formatPatch(files, fix, format, options);

    // Build metadata
    const metadata: PatchMetadata = {
      author: options.author,
      date: new Date(),
      description: fix.description,
      severity: undefined, // Would need vulnerability reference
      cwes: undefined,
      owasp: undefined,
      tags: ['security-fix', fix.strategy],
    };

    return {
      id: `PATCH-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`,
      fixId: fix.id,
      vulnerabilityId: fix.vulnerabilityId,
      format,
      content,
      files,
      metadata,
      generatedAt: new Date(),
    };
  }

  /**
   * Generate patches for multiple fixes
   */
  generateBatchPatches(
    fixes: Fix[],
    fileContents: Map<string, string>,
    options: PatchGenerationOptions = {}
  ): Patch[] {
    return fixes.map(fix => this.generatePatch(fix, fileContents, options));
  }

  /**
   * Generate a combined patch for all fixes
   */
  generateCombinedPatch(
    fixes: Fix[],
    fileContents: Map<string, string>,
    options: PatchGenerationOptions = {}
  ): Patch {
    // Combine all edits
    const allEdits: CodeEdit[] = [];
    const vulnerabilityIds: string[] = [];

    for (const fix of fixes) {
      allEdits.push(...fix.edits);
      if (!vulnerabilityIds.includes(fix.vulnerabilityId)) {
        vulnerabilityIds.push(fix.vulnerabilityId);
      }
    }

    // Create combined fix
    const combinedFix: Fix = {
      id: `COMBINED-${Date.now()}`,
      vulnerabilityId: vulnerabilityIds.join(','),
      strategy: 'combined',
      title: `Combined security fixes (${fixes.length} fixes)`,
      description: `Combined patch for ${fixes.length} security fixes`,
      confidence: Math.min(...fixes.map(f => f.confidence)),
      breakingChange: fixes.some(f => f.breakingChange),
      rationale: 'Combined multiple security fixes into single patch',
      edits: allEdits,
      imports: fixes.flatMap(f => f.imports || []),
      generatedAt: new Date(),
    };

    return this.generatePatch(combinedFix, fileContents, options);
  }

  /**
   * Parse a patch back into structured format
   */
  parsePatch(patchContent: string, format: PatchFormat = 'unified'): PatchFile[] {
    switch (format) {
      case 'unified':
        return this.parseUnifiedPatch(patchContent);
      case 'git':
        return this.parseGitPatch(patchContent);
      case 'json':
        return this.parseJsonPatch(patchContent);
      default:
        throw new Error(`Unsupported patch format: ${format}`);
    }
  }

  /**
   * Validate a patch can be applied
   */
  validatePatch(
    patch: Patch,
    fileContents: Map<string, string>
  ): { valid: boolean; errors: string[] } {
    const errors: string[] = [];

    for (const patchFile of patch.files) {
      const content = fileContents.get(patchFile.originalPath);
      
      if (content === undefined) {
        errors.push(`File not found: ${patchFile.originalPath}`);
        continue;
      }

      const lines = content.split('\n');

      for (const hunk of patchFile.hunks) {
        // Check if context lines match
        for (const line of hunk.lines) {
          if (line.type === 'context' || line.type === 'deletion') {
            const lineNum = hunk.originalStart + hunk.lines.indexOf(line);
            const actualLine = lines[lineNum - 1];
            
            if (actualLine !== line.content) {
              errors.push(
                `Context mismatch at ${patchFile.originalPath}:${lineNum}`
              );
            }
          }
        }
      }
    }

    return { valid: errors.length === 0, errors };
  }

  /**
   * Apply a patch to file contents
   */
  applyPatch(
    patch: Patch,
    fileContents: Map<string, string>
  ): PatchApplicationResult {
    const result: PatchApplicationResult = {
      success: true,
      filesModified: [],
      hunksApplied: 0,
      hunksFailed: 0,
      errors: [],
      warnings: [],
    };

    for (const patchFile of patch.files) {
      const content = fileContents.get(patchFile.originalPath);
      
      if (content === undefined) {
        result.errors.push(`File not found: ${patchFile.originalPath}`);
        result.success = false;
        continue;
      }

      const lines = content.split('\n');
      let offset = 0;

      for (const hunk of patchFile.hunks) {
        try {
          this.applyHunk(lines, hunk, offset);
          result.hunksApplied++;
          offset += (hunk.modifiedCount - hunk.originalCount);
        } catch (error) {
          result.hunksFailed++;
          result.errors.push(
            `Failed to apply hunk at ${patchFile.originalPath}:${hunk.originalStart}`
          );
        }
      }

      if (result.hunksFailed === 0) {
        fileContents.set(patchFile.originalPath, lines.join('\n'));
        result.filesModified.push(patchFile.originalPath);
      }
    }

    result.success = result.hunksFailed === 0 && result.errors.length === 0;
    return result;
  }

  /**
   * Generate reverse patch
   */
  generateReversePatch(patch: Patch): Patch {
    const reverseFiles: PatchFile[] = patch.files.map(file => ({
      originalPath: file.modifiedPath,
      modifiedPath: file.originalPath,
      hunks: file.hunks.map(hunk => ({
        originalStart: hunk.modifiedStart,
        originalCount: hunk.modifiedCount,
        modifiedStart: hunk.originalStart,
        modifiedCount: hunk.originalCount,
        lines: hunk.lines.map(line => ({
          type: line.type === 'addition' ? 'deletion' as const :
                line.type === 'deletion' ? 'addition' as const : 'context' as const,
          content: line.content,
        })),
      })),
    }));

    return {
      ...patch,
      id: `REVERSE-${patch.id}`,
      files: reverseFiles,
      content: this.formatPatch(reverseFiles, {
        id: `REVERSE-${patch.fixId}`,
        vulnerabilityId: patch.vulnerabilityId,
        strategy: 'revert',
        title: `Revert: ${patch.metadata.description}`,
        description: `Reverse patch for ${patch.id}`,
        confidence: 1.0,
        breakingChange: false,
        rationale: 'Revert security fix',
        edits: [],
        imports: [],
        generatedAt: new Date(),
      }, patch.format, {}),
      metadata: {
        ...patch.metadata,
        description: `Revert: ${patch.metadata.description}`,
        date: new Date(),
      },
      generatedAt: new Date(),
    };
  }

  // ============================================================================
  // Private Methods
  // ============================================================================

  private groupEditsByFile(edits: CodeEdit[]): Map<string, CodeEdit[]> {
    const grouped = new Map<string, CodeEdit[]>();

    for (const edit of edits) {
      const file = edit.location.file;
      const fileEdits = grouped.get(file) || [];
      fileEdits.push(edit);
      grouped.set(file, fileEdits);
    }

    // Sort edits by line number within each file
    for (const [file, fileEdits] of grouped) {
      fileEdits.sort((a, b) => a.location.startLine - b.location.startLine);
      grouped.set(file, fileEdits);
    }

    return grouped;
  }

  private generatePatchFile(
    filePath: string,
    originalContent: string,
    edits: CodeEdit[],
    contextLines: number,
    basePath?: string
  ): PatchFile {
    const originalLines = originalContent.split('\n');
    const modifiedLines = [...originalLines];

    // Apply edits in reverse order to maintain line numbers
    const sortedEdits = [...edits].sort(
      (a, b) => b.location.startLine - a.location.startLine
    );

    for (const edit of sortedEdits) {
      const { startLine, endLine } = edit.location;
      const newLines = edit.newCode.split('\n');
      modifiedLines.splice(startLine - 1, endLine - startLine + 1, ...newLines);
    }

    // Generate hunks
    const hunks = this.generateHunks(originalLines, modifiedLines, edits, contextLines);

    const path = basePath ? filePath.replace(basePath, '').replace(/^\//, '') : filePath;

    return {
      originalPath: `a/${path}`,
      modifiedPath: `b/${path}`,
      hunks,
    };
  }

  private generateHunks(
    originalLines: string[],
    _modifiedLines: string[],
    edits: CodeEdit[],
    contextLines: number
  ): PatchHunk[] {
    const hunks: PatchHunk[] = [];

    for (const edit of edits) {
      const { startLine, endLine } = edit.location;
      const newLines = edit.newCode.split('\n');

      // Calculate hunk boundaries with context
      const hunkStart = Math.max(1, startLine - contextLines);
      const hunkEnd = Math.min(
        originalLines.length,
        endLine + contextLines
      );

      const lines: PatchLine[] = [];

      // Add leading context
      for (let i = hunkStart; i < startLine; i++) {
        lines.push({ type: 'context', content: originalLines[i - 1] || '' });
      }

      // Add deletions
      for (let i = startLine; i <= endLine; i++) {
        lines.push({ type: 'deletion', content: originalLines[i - 1] || '' });
      }

      // Add additions
      for (const newLine of newLines) {
        lines.push({ type: 'addition', content: newLine });
      }

      // Add trailing context
      for (let i = endLine + 1; i <= hunkEnd; i++) {
        lines.push({ type: 'context', content: originalLines[i - 1] || '' });
      }

      const originalCount = endLine - startLine + 1 + (contextLines * 2);
      const modifiedCount = newLines.length + (contextLines * 2);

      hunks.push({
        originalStart: hunkStart,
        originalCount,
        modifiedStart: hunkStart, // Simplified - would need to track offset
        modifiedCount,
        lines,
      });
    }

    return hunks;
  }

  private formatPatch(
    files: PatchFile[],
    fix: Fix,
    format: PatchFormat,
    options: PatchGenerationOptions
  ): string {
    switch (format) {
      case 'unified':
        return this.formatUnifiedPatch(files, fix, options);
      case 'git':
        return this.formatGitPatch(files, fix, options);
      case 'json':
        return this.formatJsonPatch(files, fix);
      case 'context':
        return this.formatContextPatch(files, fix, options);
      default:
        return this.formatUnifiedPatch(files, fix, options);
    }
  }

  private formatUnifiedPatch(
    files: PatchFile[],
    fix: Fix,
    options: PatchGenerationOptions
  ): string {
    const lines: string[] = [];

    if (options.includeMetadata !== false) {
      lines.push(`# Security Fix: ${fix.title}`);
      lines.push(`# Fix ID: ${fix.id}`);
      lines.push(`# Vulnerability: ${fix.vulnerabilityId}`);
      lines.push(`# Strategy: ${fix.strategy}`);
      lines.push(`# Generated: ${new Date().toISOString()}`);
      lines.push('');
    }

    for (const file of files) {
      lines.push(`--- ${file.originalPath}`);
      lines.push(`+++ ${file.modifiedPath}`);

      for (const hunk of file.hunks) {
        lines.push(
          `@@ -${hunk.originalStart},${hunk.originalCount} ` +
          `+${hunk.modifiedStart},${hunk.modifiedCount} @@`
        );

        for (const line of hunk.lines) {
          const prefix = line.type === 'addition' ? '+' :
                        line.type === 'deletion' ? '-' : ' ';
          lines.push(`${prefix}${line.content}`);
        }
      }
    }

    return lines.join('\n');
  }

  private formatGitPatch(
    files: PatchFile[],
    fix: Fix,
    options: PatchGenerationOptions
  ): string {
    const lines: string[] = [];

    lines.push(`From: MUSUBIX Security <security@musubix.dev>`);
    lines.push(`Date: ${new Date().toUTCString()}`);
    lines.push(`Subject: [PATCH] Security Fix: ${fix.title}`);
    lines.push('');
    lines.push(fix.description);
    lines.push('');
    lines.push(`Fix-Id: ${fix.id}`);
    lines.push(`Vulnerability-Id: ${fix.vulnerabilityId}`);
    lines.push(`Strategy: ${fix.strategy}`);
    lines.push('---');

    // Add unified diff content
    lines.push(this.formatUnifiedPatch(files, fix, { ...options, includeMetadata: false }));

    lines.push('--');
    lines.push('MUSUBIX Security v1.8.0');

    return lines.join('\n');
  }

  private formatJsonPatch(files: PatchFile[], fix: Fix): string {
    const jsonPatch = {
      fix: {
        id: fix.id,
        vulnerabilityId: fix.vulnerabilityId,
        strategy: fix.strategy,
        title: fix.title,
        description: fix.description,
      },
      files: files.map(file => ({
        original: file.originalPath,
        modified: file.modifiedPath,
        hunks: file.hunks.map(hunk => ({
          range: {
            original: { start: hunk.originalStart, count: hunk.originalCount },
            modified: { start: hunk.modifiedStart, count: hunk.modifiedCount },
          },
          changes: hunk.lines.map(line => ({
            type: line.type,
            content: line.content,
          })),
        })),
      })),
      generatedAt: new Date().toISOString(),
    };

    return JSON.stringify(jsonPatch, null, 2);
  }

  private formatContextPatch(
    files: PatchFile[],
    fix: Fix,
    options: PatchGenerationOptions
  ): string {
    const lines: string[] = [];

    if (options.includeMetadata !== false) {
      lines.push(`*** Security Fix: ${fix.title}`);
      lines.push(`*** Generated: ${new Date().toISOString()}`);
      lines.push('');
    }

    for (const file of files) {
      lines.push(`*** ${file.originalPath}`);
      lines.push(`--- ${file.modifiedPath}`);

      for (const hunk of file.hunks) {
        lines.push(`***************`);
        lines.push(`*** ${hunk.originalStart},${hunk.originalStart + hunk.originalCount - 1} ****`);

        // Original context
        for (const line of hunk.lines) {
          if (line.type !== 'addition') {
            const prefix = line.type === 'deletion' ? '- ' : '  ';
            lines.push(`${prefix}${line.content}`);
          }
        }

        lines.push(`--- ${hunk.modifiedStart},${hunk.modifiedStart + hunk.modifiedCount - 1} ----`);

        // Modified context
        for (const line of hunk.lines) {
          if (line.type !== 'deletion') {
            const prefix = line.type === 'addition' ? '+ ' : '  ';
            lines.push(`${prefix}${line.content}`);
          }
        }
      }
    }

    return lines.join('\n');
  }

  private parseUnifiedPatch(content: string): PatchFile[] {
    const files: PatchFile[] = [];
    const lines = content.split('\n');
    
    let currentFile: PatchFile | null = null;
    let currentHunk: PatchHunk | null = null;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];

      if (line.startsWith('--- ')) {
        if (currentFile) files.push(currentFile);
        currentFile = {
          originalPath: line.substring(4),
          modifiedPath: '',
          hunks: [],
        };
      } else if (line.startsWith('+++ ') && currentFile) {
        currentFile.modifiedPath = line.substring(4);
      } else if (line.startsWith('@@ ') && currentFile) {
        const match = line.match(/@@ -(\d+),(\d+) \+(\d+),(\d+) @@/);
        if (match) {
          if (currentHunk) currentFile.hunks.push(currentHunk);
          currentHunk = {
            originalStart: parseInt(match[1]),
            originalCount: parseInt(match[2]),
            modifiedStart: parseInt(match[3]),
            modifiedCount: parseInt(match[4]),
            lines: [],
          };
        }
      } else if (currentHunk) {
        if (line.startsWith('+')) {
          currentHunk.lines.push({ type: 'addition', content: line.substring(1) });
        } else if (line.startsWith('-')) {
          currentHunk.lines.push({ type: 'deletion', content: line.substring(1) });
        } else if (line.startsWith(' ')) {
          currentHunk.lines.push({ type: 'context', content: line.substring(1) });
        }
      }
    }

    if (currentHunk && currentFile) currentFile.hunks.push(currentHunk);
    if (currentFile) files.push(currentFile);

    return files;
  }

  private parseGitPatch(content: string): PatchFile[] {
    // Extract the unified diff part from git format
    const diffStart = content.indexOf('---\n');
    if (diffStart === -1) {
      return this.parseUnifiedPatch(content);
    }
    return this.parseUnifiedPatch(content.substring(diffStart + 4));
  }

  private parseJsonPatch(content: string): PatchFile[] {
    const parsed = JSON.parse(content);
    return parsed.files.map((file: Record<string, unknown>) => ({
      originalPath: file.original as string,
      modifiedPath: file.modified as string,
      hunks: (file.hunks as Array<Record<string, unknown>>).map((hunk: Record<string, unknown>) => {
        const range = hunk.range as { original: { start: number; count: number }; modified: { start: number; count: number } };
        return {
          originalStart: range.original.start,
          originalCount: range.original.count,
          modifiedStart: range.modified.start,
          modifiedCount: range.modified.count,
          lines: (hunk.changes as Array<{ type: string; content: string }>).map((change: { type: string; content: string }) => ({
            type: change.type as 'context' | 'addition' | 'deletion',
            content: change.content,
          })),
        };
      }),
    }));
  }

  private applyHunk(lines: string[], hunk: PatchHunk, offset: number): void {
    const startIndex = hunk.originalStart - 1 + offset;
    
    // Verify context
    let deletionCount = 0;
    const additions: string[] = [];

    for (const line of hunk.lines) {
      if (line.type === 'deletion') {
        deletionCount++;
      } else if (line.type === 'addition') {
        additions.push(line.content);
      }
    }

    // Remove deletions and add additions
    lines.splice(startIndex, deletionCount, ...additions);
  }
}

// ============================================================================
// Factory Functions
// ============================================================================

/**
 * Create a patch generator
 */
export function createPatchGenerator(options?: PatchGeneratorOptions): PatchGenerator {
  return new PatchGenerator(options);
}

/**
 * Generate a quick patch for a fix
 */
export function generateQuickPatch(
  fix: Fix,
  fileContents: Map<string, string>
): string {
  const generator = createPatchGenerator();
  const patch = generator.generatePatch(fix, fileContents);
  return patch.content;
}
