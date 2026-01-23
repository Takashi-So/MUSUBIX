/**
 * @fileoverview Learning module exports
 * @traceability TSK-WAKE-002
 */

export {
  WakeSleepCycle,
  type WakeSleepConfig,
  type WakeObservation,
  type SleepResult,
  type LearningStats,
} from './wake-sleep.js';

export type {
  PatternStatus,
  LearningSource,
  LearnedPattern,
  LearnedPatternInput,
  PatternQuery,
  PatternLearningStats,
  PatternLearningDBConfig,
} from './db-types.js';

export {
  createLearnedPattern,
  resetPatternIdCounter,
  calculatePatternStats,
  DEFAULT_PATTERN_LEARNING_CONFIG,
} from './db-types.js';

export type { IPatternLearningDB } from './PatternLearningDB.js';

export { PatternLearningDB, createPatternLearningDB } from './PatternLearningDB.js';
