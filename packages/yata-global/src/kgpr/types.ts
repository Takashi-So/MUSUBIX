/**
 * Knowledge Graph Pull Request (KGPR) - Type Definitions
 *
 * GitHub PR-like workflow for sharing knowledge graphs
 *
 * @packageDocumentation
 * @module @nahisaho/yata-global/kgpr
 *
 * @see REQ-KGPR-001
 */

/**
 * KGPR status
 */
export type KGPRStatus =
  | 'draft'
  | 'open'
  | 'reviewing'
  | 'approved'
  | 'changes_requested'
  | 'merged'
  | 'closed';

/**
 * Entity change type
 */
export type ChangeType = 'add' | 'update' | 'delete';

/**
 * Single entity change in a KGPR
 */
export interface EntityChange {
  /** Change type */
  changeType: ChangeType;
  /** Entity ID (local) */
  localId: string;
  /** Entity name */
  name: string;
  /** Entity type (class, function, interface, etc.) */
  entityType: string;
  /** Namespace */
  namespace: string;
  /** File path (sanitized) */
  filePath?: string;
  /** Line number */
  line?: number;
  /** Metadata */
  metadata?: Record<string, unknown>;
  /** Previous value (for updates) */
  previousValue?: Record<string, unknown>;
}

/**
 * Single relationship change in a KGPR
 */
export interface RelationshipChange {
  /** Change type */
  changeType: ChangeType;
  /** Relationship ID (local) */
  localId?: string;
  /** Source entity name */
  sourceName: string;
  /** Source namespace */
  sourceNamespace: string;
  /** Target entity name */
  targetName: string;
  /** Target namespace */
  targetNamespace: string;
  /** Relationship type (extends, implements, imports, etc.) */
  relationshipType: string;
  /** Metadata */
  metadata?: Record<string, unknown>;
}

/**
 * KGPR diff - all changes in a PR
 */
export interface KGPRDiff {
  /** Entity changes */
  entities: {
    added: EntityChange[];
    updated: EntityChange[];
    deleted: EntityChange[];
  };
  /** Relationship changes */
  relationships: {
    added: RelationshipChange[];
    updated: RelationshipChange[];
    deleted: RelationshipChange[];
  };
  /** Statistics */
  stats: {
    entitiesAdded: number;
    entitiesUpdated: number;
    entitiesDeleted: number;
    relationshipsAdded: number;
    relationshipsUpdated: number;
    relationshipsDeleted: number;
    totalChanges: number;
  };
}

/**
 * KGPR review comment
 */
export interface KGPRComment {
  /** Comment ID */
  id: string;
  /** Author ID */
  authorId: string;
  /** Author name */
  authorName: string;
  /** Comment body */
  body: string;
  /** Target (null = general, or specific entity/relationship ID) */
  targetId?: string;
  /** Target type */
  targetType?: 'entity' | 'relationship';
  /** Created timestamp */
  createdAt: Date;
  /** Updated timestamp */
  updatedAt?: Date;
}

/**
 * KGPR review
 */
export interface KGPRReview {
  /** Review ID */
  id: string;
  /** Reviewer ID */
  reviewerId: string;
  /** Reviewer name */
  reviewerName: string;
  /** Review status */
  status: 'approved' | 'changes_requested' | 'commented';
  /** Review body */
  body?: string;
  /** Comments */
  comments: KGPRComment[];
  /** Created timestamp */
  createdAt: Date;
}

/**
 * Knowledge Graph Pull Request
 */
export interface KGPR {
  /** KGPR ID */
  id: string;
  /** Title */
  title: string;
  /** Description */
  description: string;
  /** Author ID */
  authorId: string;
  /** Author name */
  authorName: string;
  /** Status */
  status: KGPRStatus;
  /** Source namespace (from local KG) */
  sourceNamespace: string;
  /** Target namespace (in global KG, optional) */
  targetNamespace?: string;
  /** Diff */
  diff: KGPRDiff;
  /** Labels/tags */
  labels: string[];
  /** Reviews */
  reviews: KGPRReview[];
  /** General comments */
  comments: KGPRComment[];
  /** Quality score (AI-generated) */
  qualityScore?: number;
  /** Duplicate warnings */
  duplicateWarnings?: DuplicateWarning[];
  /** Created timestamp */
  createdAt: Date;
  /** Updated timestamp */
  updatedAt: Date;
  /** Merged timestamp */
  mergedAt?: Date;
  /** Merged by */
  mergedBy?: string;
  /** Closed timestamp */
  closedAt?: Date;
  /** Closed by */
  closedBy?: string;
}

/**
 * Duplicate warning from auto-detection
 */
export interface DuplicateWarning {
  /** Local entity name */
  localEntityName: string;
  /** Similar global entity ID */
  globalEntityId: string;
  /** Similar global entity name */
  globalEntityName: string;
  /** Similarity score (0-1) */
  similarity: number;
  /** Suggestion */
  suggestion: 'merge' | 'rename' | 'skip' | 'keep_both';
}

/**
 * KGPR creation options
 */
export interface CreateKGPROptions {
  /** Title */
  title: string;
  /** Description */
  description?: string;
  /** Source namespace to include */
  sourceNamespace?: string;
  /** Labels */
  labels?: string[];
  /** Include only specific entity types */
  entityTypes?: string[];
  /** Privacy filter level */
  privacyLevel?: 'strict' | 'moderate' | 'none';
  /** Auto-submit after creation */
  autoSubmit?: boolean;
}

/**
 * KGPR submission result
 */
export interface KGPRSubmitResult {
  /** Success flag */
  success: boolean;
  /** KGPR ID (if successful) */
  kgprId?: string;
  /** KGPR URL (if successful) */
  kgprUrl?: string;
  /** Quality score */
  qualityScore?: number;
  /** Duplicate warnings */
  duplicateWarnings?: DuplicateWarning[];
  /** Error message (if failed) */
  error?: string;
}

/**
 * KGPR list query options
 */
export interface ListKGPROptions {
  /** Filter by status */
  status?: KGPRStatus | KGPRStatus[];
  /** Filter by author */
  authorId?: string;
  /** Filter by labels */
  labels?: string[];
  /** Search query */
  search?: string;
  /** Sort by */
  sortBy?: 'created' | 'updated' | 'quality' | 'changes';
  /** Sort order */
  sortOrder?: 'asc' | 'desc';
  /** Limit */
  limit?: number;
  /** Offset */
  offset?: number;
}

/**
 * KGPR merge options
 */
export interface MergeKGPROptions {
  /** Conflict resolution strategy */
  conflictResolution?: 'keep_local' | 'keep_global' | 'keep_both' | 'manual';
  /** Squash similar entities */
  squashSimilar?: boolean;
  /** Delete source after merge */
  deleteSourceAfterMerge?: boolean;
}

/**
 * KGPR merge result
 */
export interface MergeKGPRResult {
  /** Success flag */
  success: boolean;
  /** Entities merged */
  entitiesMerged: number;
  /** Relationships merged */
  relationshipsMerged: number;
  /** Conflicts resolved */
  conflictsResolved: number;
  /** Skipped (duplicates) */
  skipped: number;
  /** Error message (if failed) */
  error?: string;
}

/**
 * Privacy filter configuration
 */
export interface PrivacyFilterConfig {
  /** Remove file paths */
  removeFilePaths: boolean;
  /** Remove line numbers */
  removeLineNumbers: boolean;
  /** Remove metadata */
  removeMetadata: boolean;
  /** Namespace patterns to exclude */
  excludeNamespaces: string[];
  /** Entity name patterns to exclude (regex) */
  excludePatterns: string[];
  /** Replace sensitive strings */
  replacements: { pattern: string; replacement: string }[];
}

/**
 * Default privacy filter (strict)
 */
export const DEFAULT_PRIVACY_FILTER_STRICT: PrivacyFilterConfig = {
  removeFilePaths: true,
  removeLineNumbers: true,
  removeMetadata: true,
  excludeNamespaces: ['internal', 'private', 'secret', 'config'],
  excludePatterns: [
    'password',
    'secret',
    'token',
    'api[_-]?key',
    'credential',
    'auth',
  ],
  replacements: [],
};

/**
 * Default privacy filter (moderate)
 */
export const DEFAULT_PRIVACY_FILTER_MODERATE: PrivacyFilterConfig = {
  removeFilePaths: false,
  removeLineNumbers: false,
  removeMetadata: false,
  excludeNamespaces: ['secret', 'config'],
  excludePatterns: ['password', 'secret', 'token', 'api[_-]?key'],
  replacements: [],
};
