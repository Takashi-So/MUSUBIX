/**
 * Neural Search Package
 * @module @nahisaho/musubix-neural-search
 * @description Neural search engine with embedding-based scoring and learning-based pruning
 */

// Types
export * from './types.js';

// Errors
export * from './errors.js';

// Neural Scorer
export {
  EmbeddingModel,
  BranchScorer,
  ContextEncoder,
  createContextAwareScorer,
  DefaultContextAwareScorer,
} from './scorer/index.js';
export type {
  ScoreWeights,
  ContextAwareScorer,
  ContextAwareScorerConfig,
  ProjectContext,
  ScoreBreakdown,
  ScoringStatistics,
} from './scorer/index.js';

// Search Engine
export {
  PriorityQueue,
  BeamSearch,
  BestFirstSearch,
  PruningManager,
  AdaptiveBeamSearch,
} from './search/index.js';
export type {
  PruningConfig,
  AdaptiveBeamConfig,
  AdaptiveStatistics,
} from './search/index.js';

// Learning Module
export {
  TrajectoryLog,
  OnlineLearner,
  ModelUpdater,
} from './learning/index.js';
export type {
  OnlineLearnerConfig,
  ModelUpdaterConfig,
} from './learning/index.js';

// Pruning Module (v2.2.0 NEW!)
export { createLearnedPruningPolicy } from './pruning/index.js';
export type {
  LearnedPruningPolicy,
  PolicyConfig,
  PolicyUpdate,
  PolicyStatistics,
  ResetOptions,
} from './pruning/index.js';

// Cache Module (v2.2.0 NEW!)
export { createEmbeddingCache, DefaultEmbeddingCache } from './cache/index.js';
export type {
  EmbeddingCache,
  EmbeddingCacheConfig,
  CacheStatistics,
} from './cache/index.js';

// Fusion Module (v2.2.0 NEW!)
export { createModalFusion, DefaultModalFusion } from './fusion/index.js';
export type {
  ModalFusion,
  ModalFusionConfig,
  FusionStrategy,
  EmbeddingPair,
} from './fusion/index.js';

// Logging Module (v2.2.0 NEW!)
export { createTrajectoryLogger, DefaultTrajectoryLogger } from './logging/index.js';
export type {
  TrajectoryLogger,
  BranchRecord,
  TrajectoryData,
  TrajectoryExportFormat,
  ParquetSchema,
  ParquetExport,
} from './logging/index.js';

// Enhanced Neural Search Manager (v2.2.0 NEW!)
export {
  createEnhancedNeuralSearchManager,
  DefaultEnhancedNeuralSearchManager,
} from './EnhancedNeuralSearchManager.js';
export type {
  EnhancedNeuralSearchManager,
  EnhancedNeuralSearchManagerConfig,
  SearchCandidate,
  SearchRequest,
  SearchResult,
  BeamSearchRequest,
  BeamSearchResult,
  CombinedSearchRequest,
  SearchFeedback,
  LearningStats,
  SearchHistoryEntry,
  EnhancedSearchStats,
} from './EnhancedNeuralSearchManager.js';
