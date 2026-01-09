/**
 * @nahisaho/musubix-codegraph
 *
 * Code graph analysis library for MUSUBIX
 * Provides AST parsing, graph construction, and semantic search
 *
 * @packageDocumentation
 * @module @nahisaho/musubix-codegraph
 *
 * @see REQ-CG-API-001 - Library as standalone
 * @see REQ-CG-API-002 - Programmatic API
 * @see REQ-CG-API-005 - Comprehensive exports
 */

// Main Facade
export { CodeGraph, createCodeGraph } from './codegraph.js';

// Event System
export {
  TypedEventEmitter,
  CodeGraphEventEmitter,
} from './events/index.js';

// Types
export type {
  // Language
  Language,

  // Entity types
  EntityType,
  Entity,
  EntityInput,

  // Relation types
  RelationType,
  Relation,
  RelationInput,

  // Options
  CodeGraphOptions,
  ParserOptions,
  GraphOptions,
  IndexerOptions,
  GraphRAGOptions,

  // Storage
  StorageAdapter,
  StorageStats,

  // Events
  CodeGraphEvents,
  IndexProgress,

  // Results
  QueryResult,
  IndexResult,
  CallPath,
  ModuleAnalysis,
  CodeSnippet,
  FileStructure,
  SearchResult,
  Community,
  GraphStatistics,
  ParseResult,

  // Query types
  GraphQuery,
  DependencyOptions,
  LocalSearchOptions,
  GlobalSearchOptions,
} from './types.js';

// Constants
export {
  LANGUAGE_EXTENSIONS,
  DEFAULT_CODEGRAPH_OPTIONS,
  generateEntityId,
  generateRelationId,
  isSupportedLanguage,
  getLanguageFromExtension,
} from './types.js';
