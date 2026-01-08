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
} from './scorer/index.js';
export type { ScoreWeights } from './scorer/index.js';

// Search Engine
export {
  PriorityQueue,
  BeamSearch,
  BestFirstSearch,
  PruningManager,
} from './search/index.js';
export type { PruningConfig } from './search/index.js';

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
