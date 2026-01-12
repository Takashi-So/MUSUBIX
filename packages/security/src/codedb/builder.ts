/**
 * @fileoverview CodeDB Builder - STUB for v3.0.11
 * @module @nahisaho/musubix-security/codedb/builder
 * @trace TSK-014, REQ-SEC-CODEDB-003
 * 
 * NOTE: This module is temporarily disabled in v3.0.11 due to type system refactoring.
 * Full functionality will be restored in v3.1.0.
 */

import type { SupportedLanguage } from '../types/codedb.js';

/**
 * Builder options
 */
export interface BuilderOptions {
  /** Languages to extract */
  languages?: SupportedLanguage[];
  /** Include patterns */
  include?: string[];
  /** Exclude patterns */
  exclude?: string[];
  /** Progress callback */
  onProgress?: (progress: BuildProgress) => void;
  /** Enable parallel processing */
  parallel?: boolean;
}

/**
 * Build progress
 */
export interface BuildProgress {
  /** Total files */
  total: number;
  /** Processed files */
  processed: number;
  /** Current file */
  currentFile: string;
  /** Percentage */
  percentage: number;
  /** Phase */
  phase: string;
}

/**
 * Build error
 */
export interface BuildError {
  /** File path */
  file: string;
  /** Error message */
  message: string;
  /** Error type */
  type: 'parse' | 'extract' | 'unknown';
}

/**
 * Build result
 */
export interface BuildResult {
  /** Built database (stub) */
  database: null;
  /** Files processed */
  filesProcessed: number;
  /** Files with errors */
  filesWithErrors: number;
  /** Build duration (ms) */
  duration: number;
  /** Errors */
  errors: BuildError[];
}

/**
 * Source file info
 */
export interface SourceFile {
  /** File path */
  path: string;
  /** Language */
  language: SupportedLanguage;
  /** Content */
  content: string;
}

/**
 * CodeDB Builder (Stub)
 * @deprecated v3.0.11 - Use variant analysis instead. Will be restored in v3.1.0.
 */
export class CodeDBBuilder {
  constructor(_options?: BuilderOptions) {
    console.warn('[MUSUBIX] CodeDBBuilder is temporarily disabled in v3.0.11. Use variant analysis instead.');
  }

  async build(_targetPath: string): Promise<BuildResult> {
    throw new Error('CodeDBBuilder is temporarily disabled in v3.0.11. Use createScanner() from variant module instead.');
  }

  async addFile(_file: SourceFile): Promise<void> {
    throw new Error('CodeDBBuilder is temporarily disabled in v3.0.11');
  }
}

/**
 * Create CodeDB builder (stub)
 * @deprecated v3.0.11 - Use variant analysis instead. Will be restored in v3.1.0.
 */
export function createBuilder(_options?: BuilderOptions): CodeDBBuilder {
  return new CodeDBBuilder(_options);
}

/**
 * Alias for createBuilder
 * @deprecated v3.0.11 - Use variant analysis instead. Will be restored in v3.1.0.
 */
export const createCodeDBBuilder = createBuilder;

/**
 * Build CodeDB from path (stub)
 * @deprecated v3.0.11 - Use variant analysis instead. Will be restored in v3.1.0.
 */
export async function buildCodeDBFromPath(
  _targetPath: string,
  _options?: BuilderOptions,
): Promise<BuildResult> {
  throw new Error('buildCodeDBFromPath is temporarily disabled in v3.0.11. Use createScanner() from variant module instead.');
}

/**
 * Build CodeDB (stub)
 * @deprecated v3.0.11 - Use variant analysis instead. Will be restored in v3.1.0.
 */
export async function buildCodeDB(
  _files: SourceFile[],
  _options?: BuilderOptions,
): Promise<BuildResult> {
  throw new Error('buildCodeDB is temporarily disabled in v3.0.11. Use createScanner() from variant module instead.');
}
