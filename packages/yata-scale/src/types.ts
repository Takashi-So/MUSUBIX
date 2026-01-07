/**
 * @nahisaho/yata-scale - Type Definitions
 * 
 * Core types for distributed knowledge graph scaling
 */

import type { Result } from 'neverthrow';

// ============================================================================
// Entity Types
// ============================================================================

/**
 * Knowledge graph entity
 */
export interface Entity {
  readonly id: string;
  readonly type: string;
  readonly name: string;
  readonly namespace?: string;
  readonly properties: Record<string, unknown>;
  readonly metadata: EntityMetadata;
}

export interface EntityMetadata {
  readonly createdAt: Date;
  readonly updatedAt: Date;
  readonly version: number;
  readonly shardId?: string;
  readonly source?: string;
}

/**
 * Relationship between entities
 */
export interface Relationship {
  readonly id: string;
  readonly sourceId: string;
  readonly targetId: string;
  readonly type: string;
  readonly properties: Record<string, unknown>;
  readonly metadata: RelationshipMetadata;
}

export interface RelationshipMetadata {
  readonly createdAt: Date;
  readonly updatedAt: Date;
  readonly version: number;
  readonly weight?: number;
}

// ============================================================================
// Shard Types
// ============================================================================

/**
 * Shard configuration
 */
export interface ShardConfig {
  readonly count: number;
  readonly replicationFactor: number;
  readonly partitionStrategy: PartitionStrategyType;
  readonly maxEntityCount?: number;
  readonly maxSizeBytes?: number;
}

/**
 * Shard runtime information
 */
export interface ShardInfo {
  readonly id: string;
  readonly status: ShardStatus;
  readonly entityCount: number;
  readonly relationshipCount: number;
  readonly sizeBytes: number;
  readonly replicas: string[];
  readonly lastModified: Date;
  readonly health: ShardHealth;
}

export type ShardStatus = 'active' | 'inactive' | 'rebalancing' | 'draining' | 'offline';

export interface ShardHealth {
  readonly healthy: boolean;
  readonly latencyMs: number;
  readonly errorRate: number;
  readonly lastChecked: Date;
}

/**
 * Partition strategy type
 */
export type PartitionStrategyType = 'hash' | 'range' | 'graph';

/**
 * Partition strategy interface
 */
export interface PartitionStrategy {
  readonly type: PartitionStrategyType;
  getShardForEntity(entityId: string): string;
  getAllShards(): string[];
  addShard(shardId: string): void;
  removeShard(shardId: string): void;
}

/**
 * Rebalance plan
 */
export interface RebalancePlan {
  readonly migrations: Migration[];
  readonly estimatedDuration: number;
  readonly affectedEntities: number;
}

export interface Migration {
  readonly from: string;
  readonly to: string;
  readonly entityIds: string[];
}

// ============================================================================
// Index Types
// ============================================================================

/**
 * Index type
 */
export type IndexType = 'btree' | 'fulltext' | 'graph' | 'bloom';

/**
 * Index statistics
 */
export interface IndexStats {
  readonly name: string;
  readonly type: IndexType;
  readonly entryCount: number;
  readonly sizeBytes: number;
  readonly depth?: number;
  readonly hitRate: number;
  readonly lastUpdated: Date;
}

/**
 * Index document for full-text search
 */
export interface IndexDocument {
  readonly id: string;
  readonly text: string;
  readonly metadata?: Record<string, unknown>;
}

/**
 * Search result
 */
export interface SearchResult {
  readonly id: string;
  readonly score: number;
  readonly highlights?: string[];
}

/**
 * Compression type
 */
export type CompressionType = 'none' | 'lz4' | 'zstd' | 'gzip';

// ============================================================================
// Cache Types
// ============================================================================

/**
 * Cache configuration
 */
export interface CacheConfig {
  readonly l1MaxEntries: number;
  readonly l2MaxSize: number;
  readonly l3MaxEntries: number;
  readonly ttlMs: number;
}

/**
 * Cache tier
 */
export type CacheTier = 'l1' | 'l2' | 'l3';

/**
 * Cache statistics
 */
export interface CacheStats {
  readonly tier: CacheTier;
  readonly hits: number;
  readonly misses: number;
  readonly hitRate: number;
  readonly size: number;
  readonly maxSize: number;
  readonly evictions: number;
}

/**
 * Cache policy
 */
export type CachePolicy = 'lru' | 'lfu' | 'arc';

// ============================================================================
// Query Types
// ============================================================================

/**
 * Graph query types
 */
export type QueryType = 'lookup' | 'traverse' | 'pattern' | 'aggregate';

/**
 * Graph query
 */
export interface GraphQuery {
  readonly type: QueryType;
  readonly entityIds?: string[];
  readonly startEntityIds?: string[];
  readonly maxDepth?: number;
  readonly direction?: 'outgoing' | 'incoming' | 'both';
  readonly pattern?: QueryPattern;
  readonly filters?: QueryFilter[];
  readonly limit?: number;
  readonly offset?: number;
  readonly orderBy?: OrderByClause[];
  readonly timeout?: number;
  readonly options?: QueryOptions;
}

export interface QueryPattern {
  readonly subject: string;
  readonly predicate: string;
  readonly object: string;
}

export interface QueryFilter {
  readonly field: string;
  readonly operator: 'eq' | 'ne' | 'gt' | 'gte' | 'lt' | 'lte' | 'contains' | 'in';
  readonly value: unknown;
}

export interface OrderByClause {
  readonly field: string;
  readonly direction: 'asc' | 'desc';
}

/**
 * Query result
 */
export interface QueryResult {
  readonly entities: Entity[];
  readonly relationships: Relationship[];
  readonly totalCount: number;
  readonly hasMore: boolean;
  readonly cursor?: string;
  readonly executionTimeMs: number;
  readonly shardsQueried: string[];
}

/**
 * Query options
 */
export interface QueryOptions {
  readonly timeout?: number;
  readonly cacheTtl?: number;
  readonly useCache?: boolean;
  readonly shards?: string[];
  readonly parallel?: boolean;
}

/**
 * Query plan
 */
export interface QueryPlan {
  readonly query: GraphQuery;
  readonly steps: QueryStep[];
  readonly estimatedCost: number;
  readonly targetShards: string[];
  readonly parallelizable: boolean;
  readonly cacheKey?: string;
  readonly timeout?: number;
  readonly optimizations?: string[];
}

export interface QueryStep {
  readonly type: 'scan' | 'index' | 'filter' | 'join' | 'sort' | 'limit' | 'merge';
  readonly target: string;
  readonly cost: number;
  readonly details: Record<string, unknown>;
}

// ============================================================================
// Sync Types
// ============================================================================

/**
 * Conflict resolution strategy
 */
export type ConflictStrategy = 'lww' | 'fww' | 'merge' | 'custom';

/**
 * Sync session
 */
export interface SyncSession {
  readonly id: string;
  readonly peerId: string;
  readonly status: SyncStatus;
  readonly startTime: Date;
  readonly lastActivity: Date;
  readonly changesReceived: number;
  readonly changesSent: number;
}

export type SyncStatus = 'connecting' | 'syncing' | 'idle' | 'error' | 'closed';

/**
 * Sync delta
 */
export interface SyncDelta {
  readonly peerId: string;
  readonly fromSequence: number;
  readonly toSequence: number;
  readonly changes: SyncChange[];
}

export interface SyncChange {
  readonly sequence: number;
  readonly operation: 'create' | 'update' | 'delete';
  readonly timestamp: Date;
  readonly data: Record<string, unknown>;
}

/**
 * WAL entry
 */
export interface WALEntry {
  readonly sequence: number;
  readonly operation: string;
  readonly timestamp: Date;
  readonly data: Record<string, unknown>;
  readonly checksum: string;
}

// ============================================================================
// YataScale Manager Types
// ============================================================================

/**
 * YataScale configuration
 */
export interface YataScaleConfig {
  readonly shards: ShardConfig;
  readonly cache: CacheConfig;
  readonly query: {
    readonly defaultTimeout: number;
    readonly maxConcurrency: number;
    readonly maxResultSize: number;
  };
  readonly nodeId?: string;
}

/**
 * YataScale statistics
 */
export interface YataScaleStats {
  readonly entityCount: number;
  readonly relationshipCount: number;
  readonly shardCount: number;
  readonly cacheStats: CacheStats;
  readonly indexStats: IndexStats;
  readonly syncStats: {
    readonly nodeId: string;
    readonly activeSessions: number;
    readonly walSequence: number;
  };
}

/**
 * Batch write result
 */
export interface BatchWriteResult {
  readonly succeeded: string[];
  readonly failed: Array<{ id: string; error: string }>;
  readonly totalTime: number;
}

// ============================================================================
// Result Types (using neverthrow)
// ============================================================================

import type { YataScaleError } from './errors.js';

export type YataScaleResult<T> = Result<T, YataScaleError>;
