/**
 * @fileoverview CodeDB Module Entry Point
 * @module @nahisaho/musubix-security/codedb
 * @trace TSK-017, REQ-SEC-CODEDB-001
 * 
 * NOTE: v3.0.11 - CodeDB functionality temporarily disabled for refactoring
 * The database and builder components are being refactored for improved stability.
 */

// ============================================================================
// v3.0.11 NOTICE: CodeDB is temporarily disabled
// ============================================================================
// The following exports are disabled pending completion of type system refactoring:
// - CodeDB class
// - CodeDBBuilder class
// - buildCodeDB functions
// - CodeDBSerializer class
//
// Please use the variant analysis module for security scanning:
//   import { createScanner } from '@nahisaho/musubix-security/variant'
// ============================================================================

// Re-export from base-extractor
export type { SupportedLanguage } from '../extractors/base-extractor.js';

// Stub exports from database.ts
export { CodeDB, type CodeDBOptions } from './database.js';

// Stub exports from builder.ts
export {
  CodeDBBuilder,
  createBuilder,
  createCodeDBBuilder,
  buildCodeDB,
  buildCodeDBFromPath,
  type BuilderOptions,
  type BuildProgress,
  type BuildError,
  type BuildResult,
  type SourceFile,
} from './builder.js';

// Type-only exports for compatibility (from types/codedb)
export type {
  CallGraphNode,
  CallGraphEdge,
  TaintPath,
  TypeDefinition,
  TypeHierarchyInfo,
} from '../types/codedb.js';

