/**
 * Meta Module
 * @module @nahisaho/musubix-synthesis
 * @description Meta-learning components for synthesis optimization
 * Traces to: DES-SY-103
 */

export {
  createMetaLearningEngine,
} from './MetaLearningEngine.js';

export type {
  MetaLearningEngine,
  MetaLearningConfig,
  MetaLearningStatistics,
  TaskFeatures,
  SynthesisStrategy,
  SynthesisTask,
  RecordedTask,
  SimilarTaskResult,
} from './MetaLearningEngine.js';
