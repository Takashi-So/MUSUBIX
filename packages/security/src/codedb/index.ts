/**
 * @fileoverview CodeDB Module Entry Point
 * @module @nahisaho/musubix-security/codedb
 * @trace TSK-017, REQ-SEC-CODEDB-001
 */

// Database
export {
  CodeDB,
  createCodeDB,
  type CodeDBOptions,
} from './database.js';

// Builder
export {
  CodeDBBuilder,
  createBuilder,
  buildCodeDB,
  type BuilderOptions,
  type BuildProgress,
  type BuildError,
  type BuildResult,
  type SourceFile,
} from './builder.js';

// Serializer
export {
  CodeDBSerializer,
  createSerializer,
  serializeCodeDB,
  deserializeCodeDB,
  type SerializedCodeDB,
  type SerializedAST,
  type SerializedDFG,
  type SerializedCFG,
  type SerializedSymbolTable,
  type SerializeOptions,
  type DeserializeOptions,
} from './serializer.js';
