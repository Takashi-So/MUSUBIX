/**
 * Neural Scorer Module
 * @module @nahisaho/musubix-neural-search/scorer
 */

export { EmbeddingModel } from './EmbeddingModel.js';
export { BranchScorer } from './BranchScorer.js';
export type { ScoreWeights } from './BranchScorer.js';
export { ContextEncoder } from './ContextEncoder.js';

// v2.2.0 NEW!
export {
  createContextAwareScorer,
  DefaultContextAwareScorer,
} from './ContextAwareScorer.js';
export type {
  ContextAwareScorer,
  ContextAwareScorerConfig,
  ProjectContext,
  ScoreBreakdown,
  ScoringStatistics,
} from './ContextAwareScorer.js';
