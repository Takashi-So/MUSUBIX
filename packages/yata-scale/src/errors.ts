/**
 * @nahisaho/yata-scale - Error Classes
 * 
 * Hierarchical error types for yata-scale operations
 */

/**
 * Base error class for all yata-scale errors
 */
export class YataScaleError extends Error {
  public readonly timestamp: Date;

  constructor(
    message: string,
    public readonly code: string,
    public readonly cause?: Error
  ) {
    super(message);
    this.name = 'YataScaleError';
    this.timestamp = new Date();

    // Maintain proper stack trace
    if (Error.captureStackTrace) {
      Error.captureStackTrace(this, this.constructor);
    }
  }

  toJSON(): Record<string, unknown> {
    return {
      name: this.name,
      message: this.message,
      code: this.code,
      timestamp: this.timestamp.toISOString(),
      cause: this.cause?.message,
    };
  }
}

// ============================================================================
// Shard Errors
// ============================================================================

/**
 * Shard-related error
 */
export class ShardError extends YataScaleError {
  constructor(
    message: string,
    public readonly shardId: string,
    cause?: Error
  ) {
    super(message, 'SHARD_ERROR', cause);
    this.name = 'ShardError';
  }

  override toJSON(): Record<string, unknown> {
    return {
      ...super.toJSON(),
      shardId: this.shardId,
    };
  }
}

/**
 * Shard not found error
 */
export class ShardNotFoundError extends ShardError {
  constructor(shardId: string) {
    super(`Shard not found: ${shardId}`, shardId);
    this.name = 'ShardNotFoundError';
  }
}

/**
 * Shard unavailable error
 */
export class ShardUnavailableError extends ShardError {
  constructor(shardId: string, cause?: Error) {
    super(`Shard unavailable: ${shardId}`, shardId, cause);
    this.name = 'ShardUnavailableError';
  }
}

/**
 * Shard capacity exceeded error
 */
export class ShardCapacityExceededError extends ShardError {
  constructor(
    shardId: string,
    public readonly currentSize: number,
    public readonly maxCapacity: number
  ) {
    super(
      `Shard capacity exceeded: ${shardId} (${currentSize}/${maxCapacity})`,
      shardId
    );
    this.name = 'ShardCapacityExceededError';
  }

  override toJSON(): Record<string, unknown> {
    return {
      ...super.toJSON(),
      currentSize: this.currentSize,
      maxCapacity: this.maxCapacity,
    };
  }
}

/**
 * Rebalance error
 */
export class RebalanceError extends YataScaleError {
  constructor(
    message: string,
    public readonly jobId: string,
    cause?: Error
  ) {
    super(message, 'REBALANCE_ERROR', cause);
    this.name = 'RebalanceError';
  }

  override toJSON(): Record<string, unknown> {
    return {
      ...super.toJSON(),
      jobId: this.jobId,
    };
  }
}

// ============================================================================
// Index Errors
// ============================================================================

/**
 * Index-related error
 */
export class IndexError extends YataScaleError {
  constructor(
    message: string,
    public readonly indexName: string,
    cause?: Error
  ) {
    super(message, 'INDEX_ERROR', cause);
    this.name = 'IndexError';
  }

  override toJSON(): Record<string, unknown> {
    return {
      ...super.toJSON(),
      indexName: this.indexName,
    };
  }
}

/**
 * Index not found error
 */
export class IndexNotFoundError extends IndexError {
  constructor(indexName: string) {
    super(`Index not found: ${indexName}`, indexName);
    this.name = 'IndexNotFoundError';
  }
}

/**
 * Index corrupted error
 */
export class IndexCorruptedError extends IndexError {
  constructor(indexName: string, details?: string) {
    super(
      `Index corrupted: ${indexName}${details ? ` - ${details}` : ''}`,
      indexName
    );
    this.name = 'IndexCorruptedError';
  }
}

/**
 * Duplicate key error
 */
export class DuplicateKeyError extends IndexError {
  constructor(
    indexName: string,
    public readonly key: string
  ) {
    super(`Duplicate key in index ${indexName}: ${key}`, indexName);
    this.name = 'DuplicateKeyError';
  }

  override toJSON(): Record<string, unknown> {
    return {
      ...super.toJSON(),
      key: this.key,
    };
  }
}

// ============================================================================
// Cache Errors
// ============================================================================

/**
 * Cache-related error
 */
export class CacheError extends YataScaleError {
  constructor(message: string, cause?: Error) {
    super(message, 'CACHE_ERROR', cause);
    this.name = 'CacheError';
  }
}

/**
 * Cache miss error (when strict mode requires hit)
 */
export class CacheMissError extends CacheError {
  constructor(public readonly key: string) {
    super(`Cache miss for key: ${key}`);
    this.name = 'CacheMissError';
  }

  override toJSON(): Record<string, unknown> {
    return {
      ...super.toJSON(),
      key: this.key,
    };
  }
}

/**
 * Cache full error
 */
export class CacheFullError extends CacheError {
  constructor(
    public readonly tier: string,
    public readonly currentSize: number,
    public readonly maxSize: number
  ) {
    super(`Cache tier ${tier} is full (${currentSize}/${maxSize})`);
    this.name = 'CacheFullError';
  }

  override toJSON(): Record<string, unknown> {
    return {
      ...super.toJSON(),
      tier: this.tier,
      currentSize: this.currentSize,
      maxSize: this.maxSize,
    };
  }
}

// ============================================================================
// Query Errors
// ============================================================================

/**
 * Query-related error
 */
export class QueryError extends YataScaleError {
  constructor(message: string, cause?: Error) {
    super(message, 'QUERY_ERROR', cause);
    this.name = 'QueryError';
  }
}

/**
 * Query timeout error
 */
export class QueryTimeoutError extends QueryError {
  constructor(public readonly timeoutMs: number) {
    super(`Query timed out after ${timeoutMs}ms`);
    this.name = 'QueryTimeoutError';
  }

  override toJSON(): Record<string, unknown> {
    return {
      ...super.toJSON(),
      timeoutMs: this.timeoutMs,
    };
  }
}

/**
 * Invalid query error
 */
export class InvalidQueryError extends QueryError {
  constructor(
    message: string,
    public readonly query: unknown
  ) {
    super(`Invalid query: ${message}`);
    this.name = 'InvalidQueryError';
  }

  override toJSON(): Record<string, unknown> {
    return {
      ...super.toJSON(),
      query: this.query,
    };
  }
}

/**
 * Query execution error
 */
export class QueryExecutionError extends QueryError {
  constructor(
    message: string,
    public readonly step: string,
    cause?: Error
  ) {
    super(`Query execution failed at step '${step}': ${message}`, cause);
    this.name = 'QueryExecutionError';
  }

  override toJSON(): Record<string, unknown> {
    return {
      ...super.toJSON(),
      step: this.step,
    };
  }
}

// ============================================================================
// Sync Errors
// ============================================================================

/**
 * Sync-related error
 */
export class SyncError extends YataScaleError {
  constructor(message: string, cause?: Error) {
    super(message, 'SYNC_ERROR', cause);
    this.name = 'SyncError';
  }
}

/**
 * Conflict error
 */
export class ConflictError extends SyncError {
  constructor(
    public readonly entityId: string,
    public readonly localVersion: number,
    public readonly remoteVersion: number
  ) {
    super(
      `Conflict detected for entity ${entityId}: local=${localVersion}, remote=${remoteVersion}`
    );
    this.name = 'ConflictError';
  }

  override toJSON(): Record<string, unknown> {
    return {
      ...super.toJSON(),
      entityId: this.entityId,
      localVersion: this.localVersion,
      remoteVersion: this.remoteVersion,
    };
  }
}

/**
 * Sync connection error
 */
export class SyncConnectionError extends SyncError {
  constructor(
    public readonly remote: string,
    cause?: Error
  ) {
    super(`Failed to connect to remote: ${remote}`, cause);
    this.name = 'SyncConnectionError';
  }

  override toJSON(): Record<string, unknown> {
    return {
      ...super.toJSON(),
      remote: this.remote,
    };
  }
}

/**
 * WAL error
 */
export class WALError extends SyncError {
  constructor(message: string, cause?: Error) {
    super(`WAL error: ${message}`, cause);
    this.name = 'WALError';
  }
}

// ============================================================================
// Storage Errors
// ============================================================================

/**
 * Storage-related error
 */
export class StorageError extends YataScaleError {
  constructor(message: string, cause?: Error) {
    super(message, 'STORAGE_ERROR', cause);
    this.name = 'StorageError';
  }
}

/**
 * Storage I/O error
 */
export class StorageIOError extends StorageError {
  constructor(
    public readonly path: string,
    public readonly operation: 'read' | 'write' | 'delete',
    cause?: Error
  ) {
    super(`Storage I/O error during ${operation} at ${path}`, cause);
    this.name = 'StorageIOError';
  }

  override toJSON(): Record<string, unknown> {
    return {
      ...super.toJSON(),
      path: this.path,
      operation: this.operation,
    };
  }
}

/**
 * Storage corruption error
 */
export class StorageCorruptionError extends StorageError {
  constructor(
    public readonly path: string,
    details?: string
  ) {
    super(`Storage corruption detected at ${path}${details ? `: ${details}` : ''}`);
    this.name = 'StorageCorruptionError';
  }

  override toJSON(): Record<string, unknown> {
    return {
      ...super.toJSON(),
      path: this.path,
    };
  }
}

/**
 * Compaction error
 */
export class CompactionError extends StorageError {
  constructor(message: string, cause?: Error) {
    super(`Compaction error: ${message}`, cause);
    this.name = 'CompactionError';
  }
}

// ============================================================================
// Entity Errors
// ============================================================================

/**
 * Entity-related error
 */
export class EntityError extends YataScaleError {
  constructor(
    message: string,
    public readonly entityId: string,
    cause?: Error
  ) {
    super(message, 'ENTITY_ERROR', cause);
    this.name = 'EntityError';
  }

  override toJSON(): Record<string, unknown> {
    return {
      ...super.toJSON(),
      entityId: this.entityId,
    };
  }
}

/**
 * Entity not found error
 */
export class EntityNotFoundError extends EntityError {
  constructor(entityId: string) {
    super(`Entity not found: ${entityId}`, entityId);
    this.name = 'EntityNotFoundError';
  }
}

/**
 * Entity already exists error
 */
export class EntityAlreadyExistsError extends EntityError {
  constructor(entityId: string) {
    super(`Entity already exists: ${entityId}`, entityId);
    this.name = 'EntityAlreadyExistsError';
  }
}

/**
 * Entity validation error
 */
export class EntityValidationError extends EntityError {
  constructor(
    entityId: string,
    public readonly violations: string[]
  ) {
    super(`Entity validation failed: ${violations.join(', ')}`, entityId);
    this.name = 'EntityValidationError';
  }

  override toJSON(): Record<string, unknown> {
    return {
      ...super.toJSON(),
      violations: this.violations,
    };
  }
}

// ============================================================================
// Configuration Errors
// ============================================================================

/**
 * Configuration error
 */
export class ConfigurationError extends YataScaleError {
  constructor(message: string) {
    super(message, 'CONFIGURATION_ERROR');
    this.name = 'ConfigurationError';
  }
}

/**
 * Invalid configuration error
 */
export class InvalidConfigurationError extends ConfigurationError {
  constructor(
    public readonly field: string,
    public readonly reason: string
  ) {
    super(`Invalid configuration for '${field}': ${reason}`);
    this.name = 'InvalidConfigurationError';
  }

  override toJSON(): Record<string, unknown> {
    return {
      ...super.toJSON(),
      field: this.field,
      reason: this.reason,
    };
  }
}

// ============================================================================
// Initialization Errors
// ============================================================================

/**
 * Initialization error
 */
export class InitializationError extends YataScaleError {
  constructor(message: string, cause?: Error) {
    super(message, 'INITIALIZATION_ERROR', cause);
    this.name = 'InitializationError';
  }
}

/**
 * Already initialized error
 */
export class AlreadyInitializedError extends InitializationError {
  constructor() {
    super('YataScale is already initialized');
    this.name = 'AlreadyInitializedError';
  }
}

/**
 * Not initialized error
 */
export class NotInitializedError extends InitializationError {
  constructor() {
    super('YataScale is not initialized. Call initialize() first.');
    this.name = 'NotInitializedError';
  }
}
