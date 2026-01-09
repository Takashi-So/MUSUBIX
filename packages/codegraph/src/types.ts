/**
 * @nahisaho/musubix-codegraph - Type Definitions
 *
 * @packageDocumentation
 * @module @nahisaho/musubix-codegraph
 *
 * @see REQ-CG-API-004
 * @see DES-CG-010
 */

// ============================================================================
// Language Types
// ============================================================================

/**
 * Supported programming languages
 * @see REQ-CG-AST-001
 */
export type Language =
  | 'typescript'
  | 'javascript'
  | 'python'
  | 'rust'
  | 'go'
  | 'java'
  | 'php'
  | 'csharp'
  | 'c'
  | 'cpp'
  | 'ruby'
  | 'hcl'
  | 'kotlin'
  | 'swift'
  | 'scala'
  | 'lua';

/**
 * File extension to language mapping
 */
export const LANGUAGE_EXTENSIONS: Record<string, Language> = {
  '.ts': 'typescript',
  '.tsx': 'typescript',
  '.js': 'javascript',
  '.jsx': 'javascript',
  '.mjs': 'javascript',
  '.cjs': 'javascript',
  '.py': 'python',
  '.pyw': 'python',
  '.rs': 'rust',
  '.go': 'go',
  '.java': 'java',
  '.php': 'php',
  '.cs': 'csharp',
  '.c': 'c',
  '.h': 'c',
  '.cpp': 'cpp',
  '.hpp': 'cpp',
  '.cc': 'cpp',
  '.cxx': 'cpp',
  '.rb': 'ruby',
  '.tf': 'hcl',
  '.hcl': 'hcl',
  '.kt': 'kotlin',
  '.kts': 'kotlin',
  '.swift': 'swift',
  '.scala': 'scala',
  '.sc': 'scala',
  '.lua': 'lua',
};

// ============================================================================
// Entity Types
// ============================================================================

/**
 * Entity types in the code graph
 * @see REQ-CG-AST-003
 * @see REQ-CG-v2.3.2-001 (16-language support)
 */
export type EntityType =
  // Common types
  | 'file'
  | 'module'
  | 'class'
  | 'interface'
  | 'function'
  | 'method'
  | 'property'
  | 'variable'
  | 'constant'
  | 'type'
  | 'enum'
  | 'enum_member'
  | 'parameter'
  | 'import'
  | 'export'
  | 'namespace'
  | 'trait'
  | 'struct'
  | 'impl'
  // Go/Java/Kotlin/Scala types
  | 'package'
  // Java/C# types
  | 'constructor'
  | 'field'
  // C# types
  | 'record'
  // C/C++ types
  | 'union'
  | 'typedef'
  | 'macro'
  | 'template_class'
  | 'template_function'
  // Kotlin/Scala types
  | 'object'
  // Scala types
  | 'case_class'
  | 'val'
  | 'var'
  // Swift types
  | 'protocol'
  | 'extension'
  | 'initializer'
  // Lua types
  | 'table'
  // HCL/Terraform types (dynamic)
  | 'resource'
  | 'data'
  | 'provider'
  | 'locals'
  | 'output'
  | 'terraform'
  // Generic fallback
  | 'unknown';

/**
 * Code entity in the graph
 * @see REQ-CG-AST-003
 * @see DES-CG-010
 */
export interface Entity {
  /** Unique identifier */
  id: string;
  /** Entity type */
  type: EntityType;
  /** Entity name */
  name: string;
  /** Qualified name (namespace.name) */
  qualifiedName?: string;
  /** Namespace or module path */
  namespace?: string;
  /** Source file path */
  filePath?: string;
  /** Start line number (1-indexed) */
  startLine?: number;
  /** End line number (1-indexed) */
  endLine?: number;
  /** Function/method signature */
  signature?: string;
  /** Documentation string */
  docstring?: string;
  /** Source code content */
  sourceCode?: string;
  /** Community ID (for GraphRAG) */
  communityId?: string;
  /** Programming language */
  language?: Language;
  /** Additional metadata */
  metadata: Record<string, unknown>;
  /** Creation timestamp */
  createdAt?: Date;
  /** Last update timestamp */
  updatedAt?: Date;
}

/**
 * Input for creating an entity
 */
export interface EntityInput {
  type: EntityType;
  name: string;
  qualifiedName?: string;
  namespace?: string;
  filePath?: string;
  startLine?: number;
  endLine?: number;
  signature?: string;
  docstring?: string;
  sourceCode?: string;
  language?: Language;
  metadata?: Record<string, unknown>;
}

// ============================================================================
// Relation Types
// ============================================================================

/**
 * Relationship types between entities
 * @see REQ-CG-AST-004
 */
export type RelationType =
  | 'calls'
  | 'imports'
  | 'exports'
  | 'extends'
  | 'implements'
  | 'contains'
  | 'uses'
  | 'defines'
  | 'returns'
  | 'parameter_of'
  | 'member_of'
  | 'type_of'
  | 'inherits'
  | 'overrides'
  | 'references'
  | 'depends_on';

/**
 * Relationship between entities
 * @see REQ-CG-AST-004
 */
export interface Relation {
  /** Unique identifier */
  id: string;
  /** Source entity ID */
  sourceId: string;
  /** Target entity ID */
  targetId: string;
  /** Relationship type */
  type: RelationType;
  /** Relationship weight/strength (0-1) */
  weight: number;
  /** Additional metadata */
  metadata: Record<string, unknown>;
  /** Creation timestamp */
  createdAt?: Date;
}

/**
 * Input for creating a relation
 */
export interface RelationInput {
  sourceId: string;
  targetId: string;
  type: RelationType;
  weight?: number;
  metadata?: Record<string, unknown>;
}

// ============================================================================
// Options Types
// ============================================================================

/**
 * CodeGraph configuration options
 * @see REQ-CG-API-005
 */
export interface CodeGraphOptions {
  /** Storage backend */
  storage?: 'memory' | 'sqlite' | StorageAdapter;
  /** SQLite database path (when storage is 'sqlite') */
  sqlitePath?: string;
  /** Parser options */
  parser?: ParserOptions;
  /** Graph engine options */
  graph?: GraphOptions;
  /** Indexer options */
  indexer?: IndexerOptions;
  /** GraphRAG options */
  graphrag?: GraphRAGOptions;
}

/**
 * Default CodeGraph options
 */
export const DEFAULT_CODEGRAPH_OPTIONS: Required<Omit<CodeGraphOptions, 'storage' | 'sqlitePath'>> = {
  parser: {
    languages: ['typescript', 'javascript', 'python'],
    includeComments: true,
    extractDocstrings: true,
  },
  graph: {
    maxDepth: 10,
    enableCaching: true,
  },
  indexer: {
    ignorePatterns: ['node_modules', '.git', 'dist', 'build', '__pycache__', '.venv'],
    maxFileSize: 1024 * 1024, // 1MB
    parallelism: 4,
  },
  graphrag: {
    communityAlgorithm: 'louvain',
    minCommunitySize: 3,
  },
};

/**
 * Parser configuration
 */
export interface ParserOptions {
  /** Languages to parse */
  languages?: Language[];
  /** Include comments in AST */
  includeComments?: boolean;
  /** Extract docstrings */
  extractDocstrings?: boolean;
}

/**
 * Graph engine configuration
 */
export interface GraphOptions {
  /** Maximum traversal depth */
  maxDepth?: number;
  /** Enable query caching */
  enableCaching?: boolean;
}

/**
 * Indexer configuration
 */
export interface IndexerOptions {
  /** Glob patterns to ignore */
  ignorePatterns?: string[];
  /** Maximum file size to process (bytes) */
  maxFileSize?: number;
  /** Number of parallel file processors */
  parallelism?: number;
}

/**
 * GraphRAG configuration
 */
export interface GraphRAGOptions {
  /** Community detection algorithm */
  communityAlgorithm?: 'louvain' | 'label_propagation';
  /** Minimum community size */
  minCommunitySize?: number;
}

// ============================================================================
// Query Types
// ============================================================================

/**
 * Graph query specification
 * @see REQ-CG-GRF-003
 */
export interface GraphQuery {
  /** Entity type filter */
  entityTypes?: EntityType[];
  /** Name pattern (glob or regex) */
  namePattern?: string;
  /** Namespace filter */
  namespace?: string;
  /** File path filter */
  filePath?: string;
  /** Relation type filter */
  relationTypes?: RelationType[];
  /** Relation direction */
  relationDirection?: 'in' | 'out' | 'both';
  /** Full-text search query */
  textSearch?: string;
  /** Include relationships in result */
  includeRelations?: boolean;
  /** Maximum results */
  limit?: number;
  /** Result offset */
  offset?: number;
}

/**
 * Query options for dependency analysis
 */
export interface DependencyOptions {
  /** Maximum depth to traverse */
  depth?: number;
  /** Relation types to follow */
  relationTypes?: RelationType[];
  /** Include indirect dependencies */
  includeIndirect?: boolean;
}

/**
 * Local search options
 */
export interface LocalSearchOptions {
  /** Search radius (hops) */
  radius?: number;
  /** Maximum results */
  limit?: number;
  /** Include community context */
  includeCommunity?: boolean;
}

/**
 * Global search options
 */
export interface GlobalSearchOptions {
  /** Maximum results */
  limit?: number;
  /** Minimum relevance score */
  minScore?: number;
  /** Include community summaries */
  includeSummaries?: boolean;
}

// ============================================================================
// Result Types
// ============================================================================

/**
 * Query result
 * @see REQ-CG-API-004
 */
export interface QueryResult {
  /** Matched entities */
  entities: Entity[];
  /** Related relationships */
  relations: Relation[];
  /** Total count (before pagination) */
  totalCount: number;
  /** Whether more results exist */
  hasMore: boolean;
  /** Query execution time (ms) */
  queryTimeMs?: number;
}

/**
 * Index operation result
 * @see REQ-CG-IDX-001
 */
export interface IndexResult {
  /** Whether indexing succeeded */
  success: boolean;
  /** Number of entities indexed */
  entitiesIndexed: number;
  /** Number of relations indexed */
  relationsIndexed: number;
  /** Number of files processed */
  filesProcessed: number;
  /** Indexing duration (ms) */
  durationMs: number;
  /** Errors encountered */
  errors: IndexError[];
}

/**
 * Index error
 */
export interface IndexError {
  /** File path */
  filePath: string;
  /** Error message */
  message: string;
  /** Line number (if applicable) */
  line?: number;
}

/**
 * Parse result
 * @see REQ-CG-AST-003
 */
export interface ParseResult {
  /** Extracted entities */
  entities: Entity[];
  /** Extracted relations */
  relations: Relation[];
  /** Parse errors */
  errors: ParseError[];
  /** Statistics */
  stats: {
    linesOfCode: number;
    parseTimeMs: number;
  };
}

/**
 * Parse error
 */
export interface ParseError {
  /** Error message */
  message: string;
  /** Line number */
  line?: number;
  /** Column number */
  column?: number;
}

/**
 * Graph statistics
 * @see REQ-CG-API-004
 */
export interface GraphStatistics {
  /** Total entity count */
  entityCount: number;
  /** Total relation count */
  relationCount: number;
  /** Number of files */
  fileCount: number;
  /** Number of communities */
  communityCount: number;
  /** Entities by type */
  entitiesByType: Partial<Record<EntityType, number>>;
  /** Relations by type */
  relationsByType: Partial<Record<RelationType, number>>;
  /** Languages detected */
  languages: Language[];
  /** Index timestamp */
  indexedAt?: Date;
}

/**
 * Call path in call graph
 */
export interface CallPath {
  /** Source entity */
  from: Entity;
  /** Target entity */
  to: Entity;
  /** Path of entities */
  path: Entity[];
  /** Call site information */
  callSites: CallSite[];
}

/**
 * Call site information
 */
export interface CallSite {
  /** File path */
  filePath: string;
  /** Line number */
  line: number;
  /** Column number */
  column?: number;
}

/**
 * Module analysis result
 */
export interface ModuleAnalysis {
  /** File path */
  filePath: string;
  /** Module name */
  moduleName: string;
  /** Entities in module */
  entities: Entity[];
  /** Import statements */
  imports: Entity[];
  /** Export statements */
  exports: Entity[];
  /** Dependencies */
  dependencies: string[];
  /** Dependents */
  dependents: string[];
}

/**
 * Code snippet
 */
export interface CodeSnippet {
  /** Entity ID */
  entityId: string;
  /** Source code */
  code: string;
  /** Language */
  language: Language;
  /** File path */
  filePath: string;
  /** Start line */
  startLine: number;
  /** End line */
  endLine: number;
  /** Context (surrounding code) */
  context?: {
    before: string;
    after: string;
  };
}

/**
 * File structure
 */
export interface FileStructure {
  /** File path */
  filePath: string;
  /** Language */
  language: Language;
  /** Entities in file */
  entities: Entity[];
  /** Lines of code */
  linesOfCode: number;
  /** Import count */
  importCount: number;
  /** Export count */
  exportCount: number;
}

/**
 * Search result (GraphRAG)
 * @see REQ-CG-RAG-002
 */
export interface SearchResult {
  /** Matched entity */
  entity: Entity;
  /** Relevance score (0-1) */
  score: number;
  /** Context snippet */
  context: string;
  /** Community information */
  community?: Community;
}

/**
 * Code community (GraphRAG)
 * @see REQ-CG-RAG-001
 */
export interface Community {
  /** Community ID */
  id: string;
  /** Community name/label */
  name: string;
  /** Member count */
  memberCount: number;
  /** Community summary */
  summary?: string;
  /** Key entities */
  keyEntities: string[];
  /** Parent community ID */
  parentId?: string;
}

// ============================================================================
// Storage Adapter Interface
// ============================================================================

/**
 * Storage adapter interface
 * @see REQ-CG-API-005
 * @see DES-CG-006
 */
export interface StorageAdapter {
  // Entity operations
  saveEntity(entity: Entity): Promise<void>;
  getEntity(id: string): Promise<Entity | null>;
  queryEntities(query: GraphQuery): Promise<Entity[]>;
  deleteEntity(id: string): Promise<void>;
  
  // Relation operations
  saveRelation(relation: Relation): Promise<void>;
  getRelations(entityId: string, direction?: 'in' | 'out' | 'both'): Promise<Relation[]>;
  deleteRelation(id: string): Promise<void>;
  
  // Bulk operations
  bulkSave(entities: Entity[], relations: Relation[]): Promise<void>;
  clear(): Promise<void>;
  
  // Statistics
  getStats(): Promise<StorageStats>;
  
  // Lifecycle
  initialize(): Promise<void>;
  close(): Promise<void>;
}

/**
 * Storage statistics
 */
export interface StorageStats {
  entityCount: number;
  relationCount: number;
  fileCount: number;
}

// ============================================================================
// Event Types
// ============================================================================

/**
 * CodeGraph event types
 * @see REQ-CG-API-006
 */
export interface CodeGraphEvents extends Record<string, unknown> {
  'indexing:start': { path: string; timestamp: Date };
  'indexing:progress': { processed: number; total: number; currentFile: string };
  'indexing:complete': IndexResult;
  'indexing:error': { error: Error; file?: string };
  'query:start': { query: GraphQuery };
  'query:complete': { result: QueryResult; durationMs: number };
  'entity:added': { entity: Entity };
  'entity:updated': { entity: Entity };
  'entity:deleted': { entityId: string };
}

/**
 * Index progress information
 */
export interface IndexProgress {
  /** Files processed so far */
  processed: number;
  /** Total files to process */
  total: number;
  /** Current file being processed */
  currentFile: string;
  /** Progress percentage (0-100) */
  percentage: number;
  /** Estimated time remaining (ms) */
  estimatedRemainingMs?: number;
}

// ============================================================================
// Utility Types
// ============================================================================

/**
 * Generate entity ID
 */
export function generateEntityId(type: EntityType, name: string, filePath?: string): string {
  const base = filePath ? `${filePath}:${name}` : name;
  return `${type}:${base}`.replace(/[^a-zA-Z0-9:._-]/g, '_');
}

/**
 * Generate relation ID
 */
export function generateRelationId(sourceId: string, targetId: string, type: RelationType): string {
  return `${sourceId}-${type}-${targetId}`;
}

/**
 * Check if language is supported
 */
export function isSupportedLanguage(lang: string): lang is Language {
  const supported: Language[] = [
    'typescript', 'javascript', 'python', 'rust', 'go', 'java',
    'php', 'csharp', 'c', 'cpp', 'ruby', 'hcl', 'kotlin', 'swift', 'scala', 'lua'
  ];
  return supported.includes(lang as Language);
}

/**
 * Get language from file extension
 */
export function getLanguageFromExtension(filePath: string): Language | null {
  const ext = filePath.slice(filePath.lastIndexOf('.')).toLowerCase();
  return LANGUAGE_EXTENSIONS[ext] ?? null;
}
