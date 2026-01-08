/**
 * Learning Module
 * @module @nahisaho/musubix-neural-search/learning
 */

export { TrajectoryLog } from './TrajectoryLog.js';
export { OnlineLearner } from './OnlineLearner.js';
export type { OnlineLearnerConfig } from './OnlineLearner.js';
export { ModelUpdater } from './ModelUpdater.js';
export type { ModelUpdaterConfig } from './ModelUpdater.js';

// OnlineModelUpdater (v2.2.0 NEW!)
export {
  createOnlineModelUpdater,
  DefaultOnlineModelUpdater,
} from './OnlineModelUpdater.js';
export type {
  OnlineModelUpdater,
  OnlineModelUpdaterConfig,
  FeedbackType,
  FeedbackRecord,
  FeedbackResult,
  UpdateResult,
  ModelWeights,
  UpdateStatistics,
} from './OnlineModelUpdater.js';
