/**
 * YATA Local KGPR Types
 *
 * Type definitions for local Knowledge Graph Pull Requests
 *
 * @packageDocumentation
 * @module @nahisaho/yata-local/kgpr
 *
 * @see REQ-YL-EXT-KGPR-001
 */

import type { Entity, EntityType, RelationType, KGPRStatusLocal, PrivacyLevel as BasePrivacyLevel } from '../types.js';

// Re-export base types
export type { KGPRStatusLocal, PrivacyLevel } from '../types.js';

/**
 * Change type
 */
export type ChangeType = 'add' | 'update' | 'delete';

/**
 * Entity change in a KGPR diff
 */
export interface LocalEntityChange {
  /** Change type */
  changeType: ChangeType;
  /** Local entity ID */
  localId: string;
  /** Entity name */
  name: string;
  /** Entity type */
  entityType: EntityType;
  /** Namespace */
  namespace: string;
  /** File path (may be sanitized) */
  filePath?: string;
  /** Line number */
  line?: number;
  /** Metadata */
  metadata?: Record<string, unknown>;
  /** Previous value (for updates) */
  previousValue?: Partial<Entity>;
}

/**
 * Relationship change in a KGPR diff
 */
export interface LocalRelationshipChange {
  /** Change type */
  changeType: ChangeType;
  /** Local relationship ID */
  localId?: string;
  /** Source entity name */
  sourceName: string;
  /** Source namespace */
  sourceNamespace: string;
  /** Target entity name */
  targetName: string;
  /** Target namespace */
  targetNamespace: string;
  /** Relationship type */
  relationshipType: RelationType;
  /** Metadata */
  metadata?: Record<string, unknown>;
}

/**
 * KGPR diff - all changes
 */
export interface LocalKGPRDiff {
  /** Entity changes */
  entities: {
    added: LocalEntityChange[];
    updated: LocalEntityChange[];
    deleted: LocalEntityChange[];
  };
  /** Relationship changes */
  relationships: {
    added: LocalRelationshipChange[];
    updated: LocalRelationshipChange[];
    deleted: LocalRelationshipChange[];
  };
  /** Statistics */
  stats: LocalDiffStats;
}

/**
 * Diff statistics
 */
export interface LocalDiffStats {
  entitiesAdded: number;
  entitiesUpdated: number;
  entitiesDeleted: number;
  relationshipsAdded: number;
  relationshipsUpdated: number;
  relationshipsDeleted: number;
  totalChanges: number;
}

/**
 * KGPR review from local storage
 */
export interface LocalKGPRReviewEntry {
  /** Review ID */
  id: string;
  /** KGPR ID */
  kgprId: string;
  /** Reviewer ID */
  reviewerId: string;
  /** Review status */
  status: 'approved' | 'changes_requested' | 'commented';
  /** Review comment */
  comment?: string;
  /** Created timestamp */
  createdAt: Date;
}

/**
 * Local KGPR info (full object with parsed diff)
 */
export interface LocalKGPRInfo {
  /** KGPR ID */
  id: string;
  /** Title */
  title: string;
  /** Description */
  description: string;
  /** Status */
  status: KGPRStatusLocal;
  /** Source namespace */
  namespace: string;
  /** Diff (parsed) */
  diff: LocalKGPRDiff;
  /** Privacy level used */
  privacyLevel: BasePrivacyLevel;
  /** Entity types included */
  entityTypes: EntityType[];
  /** Reviews */
  reviews: LocalKGPRReviewEntry[];
  /** Created timestamp */
  createdAt: Date;
  /** Updated timestamp */
  updatedAt: Date;
  /** Submitted timestamp */
  submittedAt?: Date;
}

/**
 * Options for creating a KGPR
 */
export interface CreateLocalKGPROptions {
  /** Title */
  title: string;
  /** Description */
  description?: string;
  /** Author ID */
  author?: string;
  /** Source namespace to include (optional filter) */
  namespace?: string;
  /** Entity types to include (optional filter) */
  entityTypes?: EntityType[];
  /** Privacy level */
  privacyLevel?: BasePrivacyLevel;
  /** Baseline snapshot ID (for diff) */
  baselineId?: string;
}

/**
 * Options for listing KGPRs
 */
export interface ListLocalKGPROptions {
  /** Filter by status */
  status?: KGPRStatusLocal | KGPRStatusLocal[];
  /** Filter by namespace */
  namespace?: string;
  /** Search in title/description */
  search?: string;
  /** Sort by field */
  sortBy?: 'created' | 'updated' | 'title';
  /** Sort order */
  sortOrder?: 'asc' | 'desc';
  /** Limit results */
  limit?: number;
  /** Offset for pagination */
  offset?: number;
}

/**
 * Privacy filter configuration
 */
export interface LocalPrivacyFilterConfig {
  /** Remove file paths from output */
  removeFilePaths: boolean;
  /** Remove line numbers from output */
  removeLineNumbers: boolean;
  /** Remove metadata from output */
  removeMetadata: boolean;
  /** Namespace patterns to exclude */
  excludeNamespaces: string[];
  /** Entity name patterns to exclude (regex) */
  excludePatterns: string[];
  /** String replacements */
  replacements: { pattern: string; replacement: string }[];
}

/**
 * Default strict privacy filter
 */
export const DEFAULT_LOCAL_PRIVACY_STRICT: LocalPrivacyFilterConfig = {
  removeFilePaths: true,
  removeLineNumbers: true,
  removeMetadata: true,
  excludeNamespaces: ['internal', 'private', 'secret', 'config', 'test', '__tests__'],
  excludePatterns: [
    'password',
    'secret',
    'token',
    'api[_-]?key',
    'credential',
    'auth',
    'private',
    '\\$_',
    '_internal',
  ],
  replacements: [],
};

/**
 * Default moderate privacy filter
 */
export const DEFAULT_LOCAL_PRIVACY_MODERATE: LocalPrivacyFilterConfig = {
  removeFilePaths: false,
  removeLineNumbers: false,
  removeMetadata: false,
  excludeNamespaces: ['secret', 'config'],
  excludePatterns: ['password', 'secret', 'token', 'api[_-]?key'],
  replacements: [],
};

/**
 * Default no privacy filter
 */
export const DEFAULT_LOCAL_PRIVACY_NONE: LocalPrivacyFilterConfig = {
  removeFilePaths: false,
  removeLineNumbers: false,
  removeMetadata: false,
  excludeNamespaces: [],
  excludePatterns: [],
  replacements: [],
};

/**
 * Snapshot of the knowledge graph at a point in time
 */
export interface KGSnapshot {
  /** Snapshot ID */
  id: string;
  /** Snapshot timestamp */
  timestamp: Date;
  /** Entity hashes (id -> hash) */
  entityHashes: Map<string, string>;
  /** Relationship hashes (id -> hash) */
  relationshipHashes: Map<string, string>;
  /** Description */
  description?: string;
}

/**
 * Diff generation options
 */
export interface DiffOptions {
  /** Namespace filter */
  namespace?: string;
  /** Entity types filter */
  entityTypes?: EntityType[];
  /** Include deleted entities */
  includeDeleted?: boolean;
}
