/**
 * YATA Local - Type Definitions
 *
 * @packageDocumentation
 * @module @nahisaho/yata-local
 *
 * @see REQ-YATA-LOCAL-001
 */

/**
 * Entity in the knowledge graph
 * @see REQ-YL-STORE-003
 */
export interface Entity {
  /** Unique identifier */
  id: string;
  /** Entity type (class, function, variable, etc.) */
  type: EntityType;
  /** Entity name */
  name: string;
  /** Namespace or module path */
  namespace: string;
  /** Source file path */
  filePath?: string;
  /** Line number in source */
  line?: number;
  /** Entity description */
  description?: string;
  /** Additional metadata */
  metadata: Record<string, unknown>;
  /** Creation timestamp */
  createdAt: Date;
  /** Last update timestamp */
  updatedAt: Date;
}

/**
 * Entity types
 */
export type EntityType =
  | 'class'
  | 'interface'
  | 'function'
  | 'method'
  | 'variable'
  | 'constant'
  | 'type'
  | 'enum'
  | 'module'
  | 'package'
  | 'file'
  | 'parameter'
  | 'property'
  | 'import'
  | 'export'
  | 'unknown';

/**
 * Relationship between entities
 * @see REQ-YL-STORE-004
 */
export interface Relationship {
  /** Unique identifier */
  id: string;
  /** Source entity ID */
  sourceId: string;
  /** Target entity ID */
  targetId: string;
  /** Relationship type */
  type: RelationType;
  /** Relationship weight/strength */
  weight: number;
  /** Additional metadata */
  metadata: Record<string, unknown>;
  /** Creation timestamp */
  createdAt: Date;
}

/**
 * Relationship types
 */
export type RelationType =
  | 'calls'
  | 'imports'
  | 'exports'
  | 'extends'
  | 'inherits'
  | 'implements'
  | 'contains'
  | 'uses'
  | 'defines'
  | 'references'
  | 'depends-on'
  | 'transitively-depends-on'
  | 'type-compatible'
  | 'has-method'
  | 'overrides'
  | 'returns'
  | 'parameter_of'
  | 'member_of'
  | 'related-to'
  | 'defined-in-same-file'
  | 'unknown';

/**
 * Database configuration
 */
export interface DatabaseConfig {
  /** Database file path */
  path: string;
  /** Enable WAL mode for better performance */
  walMode: boolean;
  /** Enable memory mapping */
  mmapSize: number;
  /** Cache size in KB */
  cacheSize: number;
  /** Enable foreign keys */
  foreignKeys: boolean;
  /** Enable encryption (requires SQLCipher) */
  encryption?: {
    enabled: boolean;
    key: string;
  };
}

/**
 * Default database configuration
 */
export const DEFAULT_DB_CONFIG: DatabaseConfig = {
  path: '.yata/knowledge.db',
  walMode: true,
  mmapSize: 256 * 1024 * 1024, // 256MB
  cacheSize: 64 * 1024, // 64MB
  foreignKeys: true,
};

/**
 * Query options
 * @see REQ-YL-QUERY-001
 */
export interface QueryOptions {
  /** Maximum results to return */
  limit: number;
  /** Offset for pagination */
  offset: number;
  /** Sort field */
  sortBy?: keyof Entity;
  /** Sort direction */
  sortOrder: 'asc' | 'desc';
  /** Include relationships */
  includeRelationships: boolean;
  /** Relationship depth */
  relationshipDepth: number;
}

/**
 * Default query options
 */
export const DEFAULT_QUERY_OPTIONS: QueryOptions = {
  limit: 100,
  offset: 0,
  sortOrder: 'asc',
  includeRelationships: false,
  relationshipDepth: 1,
};

/**
 * Graph query specification
 */
export interface GraphQuery {
  /** Entity filters */
  entityFilters?: {
    types?: EntityType | EntityType[];
    name?: string;
    namespace?: string;
    namePattern?: string;
  };
  /** Relationship filters */
  relationshipFilters?: {
    types?: RelationType[];
    direction?: 'in' | 'out' | 'both';
  };
  /** Full-text search query */
  textSearch?: string;
  /** Include relationships in result */
  includeRelationships?: boolean;
}

/**
 * Query result
 */
export interface QueryResult {
  /** Matched entities */
  entities: Entity[];
  /** Related relationships */
  relationships: Relationship[];
  /** Total count (before pagination) */
  totalCount: number;
  /** Whether more results exist */
  hasMore: boolean;
  /** Query execution time in ms */
  executionTime: number;
}

/**
 * Path between entities
 * @see REQ-YL-QUERY-002
 */
export interface Path {
  /** Entities in the path */
  entities: Entity[];
  /** Relationships in the path */
  relationships: Relationship[];
  /** Path length (number of hops) */
  length: number;
}

/**
 * Path finding options
 */
export interface PathOptions {
  /** Maximum path length */
  maxLength: number;
  /** Maximum paths to return */
  maxPaths: number;
  /** Allowed relationship types */
  allowedRelations?: RelationType[];
  /** Use weighted shortest path */
  weighted: boolean;
}

/**
 * Default path options
 */
export const DEFAULT_PATH_OPTIONS: PathOptions = {
  maxLength: 10,
  maxPaths: 5,
  weighted: false,
};

/**
 * Subgraph extraction result
 * @see REQ-YL-QUERY-003
 */
export interface Subgraph {
  /** Root entity ID */
  rootId: string;
  /** Entities in subgraph */
  entities: Entity[];
  /** Relationships in subgraph */
  relationships: Relationship[];
}

/**
 * Graph pattern for matching
 * @see REQ-YL-QUERY-004
 */
export interface GraphPattern {
  /** Pattern nodes */
  nodes: PatternNode[];
  /** Pattern edges */
  edges: PatternEdge[];
}

/**
 * Pattern node specification
 */
export interface PatternNode {
  /** Variable name for binding */
  variable: string;
  /** Required entity type */
  type?: EntityType;
  /** Name pattern (regex) */
  namePattern?: string;
  /** Additional constraints */
  constraints?: Record<string, unknown>;
}

/**
 * Pattern edge specification
 */
export interface PatternEdge {
  /** Source node variable */
  sourceVar: string;
  /** Target node variable */
  targetVar: string;
  /** Required relationship type */
  type?: RelationType;
}

/**
 * Pattern match result
 */
export interface PatternMatch {
  /** Variable bindings (variable name -> entity ID) */
  bindings: Record<string, string>;
  /** Match confidence */
  confidence: number;
}

/**
 * Inference rule
 * @see REQ-YL-REASON-001
 */
export interface InferenceRule {
  /** Rule identifier */
  id: string;
  /** Rule name */
  name: string;
  /** Rule description */
  description: string;
  /** Pattern to match */
  pattern: GraphPattern;
  /** Inference to apply when pattern matches */
  inference: {
    sourceVar: string;
    targetVar: string;
    type: RelationType;
  };
  /** Rule confidence */
  confidence: number;
}

/**
 * Constraint definition
 * @see REQ-YL-REASON-003
 */
export interface Constraint {
  /** Constraint identifier */
  id: string;
  /** Constraint name */
  name: string;
  /** Constraint description */
  description: string;
  /** Constraint type */
  type: 'graph' | 'referential' | 'cardinality' | 'property';
  /** Check function */
  check: (db: YataDatabase) => Promise<ConstraintViolation[]>;
}

// Forward declaration for type reference
export type YataDatabase = import('./database.js').YataDatabase;

/**
 * Constraint violation
 */
export interface ConstraintViolation {
  /** Affected entity ID */
  entityId?: string;
  /** Affected relationship ID */
  relationshipId?: string;
  /** Violated constraint ID */
  constraintId: string;
  /** Violation message */
  message: string;
  /** Severity */
  severity: 'error' | 'warning' | 'info';
}

/**
 * Validation result
 */
export interface ValidationResult {
  /** Whether graph is valid (no errors) */
  valid: boolean;
  /** Violations found */
  violations: ConstraintViolation[];
  /** Summary counts */
  summary: {
    total: number;
    errors: number;
    warnings: number;
    info: number;
  };
}

/**
 * Delta for synchronization
 * @see REQ-YL-IO-004
 */
export interface Delta {
  /** Entities changes */
  entities: {
    added: Entity[];
    updated: Entity[];
    deleted: string[];
  };
  /** Relationships changes */
  relationships: {
    added: Relationship[];
    deleted: string[];
  };
  /** Delta timestamp */
  timestamp: Date;
}

/**
 * Merge result
 */
export interface MergeResult {
  /** Whether the operation succeeded */
  success: boolean;
  /** Number of entities added */
  entitiesAdded: number;
  /** Number of entities updated */
  entitiesUpdated: number;
  /** Number of entities skipped */
  entitiesSkipped: number;
  /** Number of relationships added */
  relationshipsAdded: number;
  /** Number of relationships skipped */
  relationshipsSkipped: number;
  /** Conflicts encountered */
  conflicts: MergeConflict[];
}

/**
 * Merge conflict
 */
export interface MergeConflict {
  /** Conflict type */
  type: 'entity' | 'relationship';
  /** Conflicting item ID */
  id: string;
  /** Reason for conflict */
  reason: string;
}

/**
 * Graph statistics
 */
export interface GraphStats {
  /** Total entity count */
  entityCount: number;
  /** Entities by type */
  entitiesByType: Record<EntityType, number>;
  /** Total relationship count */
  relationshipCount: number;
  /** Relationships by type */
  relationshipsByType: Record<RelationType, number>;
  /** Database file size in bytes */
  databaseSize: number;
  /** Last modified timestamp */
  lastModified: Date;
}

// ============================================================
// Pattern Types (TSK-NFR-003)
// @see REQ-WSL-003
// ============================================================

/**
 * Pattern category
 */
export type PatternCategory =
  | 'code'
  | 'design'
  | 'requirement'
  | 'test'
  | 'architecture';

/**
 * Learned pattern stored in knowledge graph
 * @see REQ-WSL-003
 */
export interface LearnedPattern {
  /** Unique identifier */
  id: string;
  /** Pattern name */
  name: string;
  /** Pattern category */
  category: PatternCategory;
  /** Pattern content (code snippet, template, etc.) */
  content: string;
  /** Abstract Syntax Tree representation */
  ast?: unknown;
  /** Confidence score (0.0 - 1.0) */
  confidence: number;
  /** Number of times pattern was observed */
  occurrences: number;
  /** Last time pattern was used */
  lastUsedAt?: Date;
  /** Number of times pattern was applied */
  usageCount: number;
  /** Source of pattern (file path, module, etc.) */
  source?: string;
  /** Additional metadata */
  metadata: Record<string, unknown>;
  /** Creation timestamp */
  createdAt: Date;
  /** Last update timestamp */
  updatedAt: Date;
}

/**
 * Pattern input for creation
 */
export interface PatternInput {
  name: string;
  category?: PatternCategory;
  content: string;
  ast?: unknown;
  confidence?: number;
  occurrences?: number;
  source?: string;
  metadata?: Record<string, unknown>;
}

/**
 * Pattern query options
 */
export interface PatternQueryOptions {
  category?: PatternCategory;
  minConfidence?: number;
  limit?: number;
  offset?: number;
  sortBy?: 'confidence' | 'occurrences' | 'lastUsedAt' | 'createdAt';
  sortOrder?: 'asc' | 'desc';
}

// ============================================================
// Learning Cycle Types (TSK-NFR-004)
// @see REQ-WSL-005
// ============================================================

/**
 * Learning cycle record
 * @see REQ-WSL-005
 */
export interface LearningCycle {
  /** Unique identifier */
  id: string;
  /** Number of patterns extracted in wake phase */
  wakeExtracted: number;
  /** Number of files observed in wake phase */
  wakeObservedFiles: number;
  /** Number of patterns clustered in sleep phase */
  sleepClustered: number;
  /** Number of patterns decayed/removed in sleep phase */
  sleepDecayed: number;
  /** Duration in milliseconds */
  durationMs: number;
  /** Additional metadata */
  metadata: Record<string, unknown>;
  /** Completion timestamp */
  completedAt: Date;
}

/**
 * Learning cycle input for logging
 */
export interface LearningCycleInput {
  wakeExtracted: number;
  wakeObservedFiles: number;
  sleepClustered: number;
  sleepDecayed: number;
  durationMs: number;
  metadata?: Record<string, unknown>;
}

/**
 * Learning statistics
 */
export interface LearningStats {
  /** Total patterns count */
  totalPatterns: number;
  /** Patterns by category */
  patternsByCategory: Record<PatternCategory, number>;
  /** Average confidence */
  averageConfidence: number;
  /** Total learning cycles */
  totalCycles: number;
  /** Last cycle timestamp */
  lastCycleAt?: Date;
}

// ============================================================
// KGPR Types (TSK-KGPR-004)
// @see REQ-KGPR-001
// ============================================================

/**
 * KGPR status
 */
export type KGPRStatusLocal =
  | 'draft'
  | 'open'
  | 'reviewing'
  | 'approved'
  | 'changes_requested'
  | 'merged'
  | 'closed';

/**
 * Privacy level for KGPR
 */
export type PrivacyLevel = 'strict' | 'moderate' | 'none';

/**
 * Local KGPR record (stored in YATA Local)
 * @see REQ-KGPR-001
 */
export interface LocalKGPR {
  /** Unique identifier */
  id: string;
  /** KGPR title */
  title: string;
  /** Description */
  description?: string;
  /** Current status */
  status: KGPRStatusLocal;
  /** Author identifier */
  author: string;
  /** Source namespace */
  namespace: string;
  /** Diff data as JSON */
  diffJson: string;
  /** Privacy level */
  privacyLevel: PrivacyLevel;
  /** Entity types JSON */
  entityTypesJson?: string;
  /** Creation timestamp */
  createdAt: Date;
  /** Updated timestamp */
  updatedAt: Date;
  /** Submission timestamp */
  submittedAt?: Date;
  /** Review timestamp */
  reviewedAt?: Date;
  /** Merge timestamp */
  mergedAt?: Date;
  /** Close timestamp */
  closedAt?: Date;
}

/**
 * Input for creating/inserting a local KGPR
 */
export interface LocalKGPRInput {
  /** Unique identifier */
  id: string;
  /** KGPR title */
  title: string;
  /** Description */
  description?: string;
  /** Current status */
  status: KGPRStatusLocal;
  /** Author identifier */
  author: string;
  /** Source namespace */
  namespace?: string;
  /** Diff data as JSON */
  diffJson: string;
  /** Privacy level */
  privacyLevel: PrivacyLevel;
  /** Entity types as JSON */
  entityTypesJson?: string;
  /** Creation timestamp */
  createdAt: string;
  /** Updated timestamp */
  updatedAt?: string;
  /** Submission timestamp */
  submittedAt?: string;
}

/**
 * KGPR review record
 */
export interface LocalKGPRReview {
  /** Unique identifier */
  id: string;
  /** Associated KGPR ID */
  kgprId: string;
  /** Reviewer identifier */
  reviewer: string;
  /** Review action */
  action: 'approve' | 'changes_requested' | 'commented';
  /** Review comment */
  comment?: string;
  /** Creation timestamp */
  createdAt: Date;
}

/**
 * Input for creating/inserting a KGPR review
 */
export interface LocalKGPRReviewInput {
  /** Unique identifier */
  id: string;
  /** Associated KGPR ID */
  kgprId: string;
  /** Reviewer identifier */
  reviewer: string;
  /** Review action (matches LocalKGPRReviewEntry.status) */
  action: 'approved' | 'changes_requested' | 'commented';
  /** Review comment */
  comment?: string | null;
  /** Creation timestamp */
  createdAt: string;
}
