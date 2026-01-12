/**
 * @fileoverview CodeDB Database - STUB for v3.0.11
 * @module @nahisaho/musubix-security/codedb/database
 * @trace TSK-013, REQ-SEC-CODEDB-001, REQ-SEC-CODEDB-002
 * 
 * NOTE: This module is temporarily disabled in v3.0.11 due to type system refactoring.
 * Full functionality will be restored in v3.1.0.
 */

import type { SupportedLanguage } from '../types/codedb.js';

/**
 * CodeDB options
 */
export interface CodeDBOptions {
  /** Primary language */
  primaryLanguage?: SupportedLanguage;
  /** Enable caching */
  enableCache?: boolean;
  /** Max cache size */
  maxCacheSize?: number;
}

/**
 * CodeDB class (Stub)
 * @deprecated v3.0.11 - Use variant analysis instead. Will be restored in v3.1.0.
 */
export class CodeDB {
  /** Files in database */
  readonly files: string[] = [];
  
  constructor(_options?: CodeDBOptions) {
    console.warn('[MUSUBIX] CodeDB is temporarily disabled in v3.0.11. Use variant analysis instead.');
  }

  /**
   * Add a file to the database (stub)
   */
  addFile(_filePath: string, _content: string): void {
    throw new Error('CodeDB is temporarily disabled in v3.0.11. Use createScanner() from variant module instead.');
  }

  /**
   * Query AST (stub)
   */
  queryAST(_selector: unknown): never[] {
    throw new Error('CodeDB is temporarily disabled in v3.0.11');
  }

  /**
   * Query data flow (stub)
   */
  queryDataFlow(_query: unknown): never[] {
    throw new Error('CodeDB is temporarily disabled in v3.0.11');
  }

  /**
   * Query control flow (stub)
   */
  queryControlFlow(_query: unknown): never[] {
    throw new Error('CodeDB is temporarily disabled in v3.0.11');
  }

  /**
   * Get call graph (stub)
   */
  getCallGraph(): { nodes: never[]; edges: never[] } {
    throw new Error('CodeDB is temporarily disabled in v3.0.11');
  }

  /**
   * Get symbol (stub)
   */
  getSymbol(_name: string): undefined {
    return undefined;
  }

  /**
   * Get all symbols (stub)
   */
  getAllSymbols(): never[] {
    return [];
  }

  /**
   * Get type hierarchy (stub)
   */
  getTypeHierarchy(_typeName: string): undefined {
    return undefined;
  }

  /**
   * Clear database (stub)
   */
  clear(): void {
    // No-op
  }
}

/**
 * Create CodeDB instance (stub)
 * @deprecated v3.0.11 - Use variant analysis instead. Will be restored in v3.1.0.
 */
export function createCodeDB(_options?: CodeDBOptions): CodeDB {
  return new CodeDB(_options);
}
