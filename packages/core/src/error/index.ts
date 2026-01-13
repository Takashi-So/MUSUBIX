/**
 * Error Recovery Module
 * 
 * Provides graceful degradation and data persistence
 * 
 * @packageDocumentation
 * @module error
 */

export {
  // Graceful Degradation
  GracefulDegradation,
  createGracefulDegradation,
  retryWithBackoff,
  CircuitBreaker,
  MemoryCacheProvider,
  MemoryQueueProvider,
  
  // Types
  type DegradationLevel,
  type ServiceStatus,
  type FallbackStrategy,
  type HealthCheckResult,
  type ServiceConfig,
  type FallbackAction,
  type DegradationEvent,
  type DegradedResult,
  type GracefulDegradationConfig,
  type CacheProvider,
  type QueueProvider,
  
  // Constants
  DEFAULT_DEGRADATION_CONFIG,
} from './graceful-degradation.js';

export {
  // Data Persistence
  DataPersistence,
  createDataPersistence,
  WriteAheadLog,
  MemoryStorageAdapter,
  FileStorageAdapter,
  
  // Types
  type StorageBackend,
  type DataState,
  type Checkpoint,
  type Transaction,
  type TransactionOperation,
  type RecoveryResult,
  type PersistenceStatistics,
  type DataPersistenceConfig,
  type StorageAdapter,
  
  // Constants
  DEFAULT_PERSISTENCE_CONFIG,
} from './data-persistence.js';

// Actionable Error System (v3.1.0 NEW!)
// @see TSK-NFR-001
export {
  ActionableError,
  ErrorFormatter,
  ErrorCodes,
  CommonErrors,
  type ErrorSeverity,
  type ErrorSuggestion,
  type ErrorContext,
  type ActionableErrorOptions,
  type ErrorCode,
} from './actionable-error.js';
