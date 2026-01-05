/**
 * Learning Module - Self-Learning System
 *
 * Provides self-learning capabilities through feedback collection,
 * pattern extraction, and adaptive reasoning.
 *
 * @see REQ-LEARN-001 - Feedback Collection
 * @see REQ-LEARN-002 - Pattern Extraction
 * @see REQ-LEARN-003 - Adaptive Reasoning
 * @see REQ-LEARN-010 - Real-time Pattern Learning (v1.5.0)
 * @module @musubix/core/learning
 */

// Export types (with Learning prefix to avoid conflicts)
export type {
  FeedbackType,
  PatternSource,
  PatternActionType,
  FeedbackContext,
  Feedback,
  PatternTrigger,
  PatternAction,
  LearnedPattern,
  LearningStats,
  PatternMatch,
  LearningConfig,
} from './types.js';

export { DEFAULT_LEARNING_CONFIG } from './types.js';

// Re-export with Learning prefix for disambiguated access
export type { ArtifactType as LearningArtifactType } from './types.js';
export type { PatternCategory as LearningPatternCategory } from './types.js';

// Export feedback collector
export { FeedbackCollector, type FeedbackInput, type FeedbackQuery } from './feedback-collector.js';

// Export pattern extractor
export { PatternExtractor } from './pattern-extractor.js';

// Export learning engine
export { LearningEngine, type InferenceContext } from './learning-engine.js';

// Export best practices
export {
  type BestPractice,
  LEARNED_BEST_PRACTICES,
  getBestPracticesByCategory,
  getBestPracticesByAction,
  getPreferredPatterns,
  getAntiPatterns,
  getHighConfidencePatterns,
  formatBestPractice,
  generateBestPracticesReport,
} from './best-practices.js';

// Export real-time learning module (v1.5.0)
export {
  // Main engine
  RealtimeLearningEngine,
  type RealtimeLearningConfig,
  // Components
  FileWatcher,
  StreamProcessor,
  FeedbackQueue,
  EventStream,
  IncrementalUpdater,
  // Factory functions
  createFeedback,
  createPatternEvent,
  createUpdate,
  // Types
  type FileChangeEvent,
  type FileChangeType,
  type ProcessResult,
  type RealtimeDetectedPattern,
  type RealtimeFeedback,
  type PatternEvent,
  type PatternEventType,
  type Subscription,
  type IncrementalUpdate,
  type RealtimeMetrics,
  type FileWatcherConfig,
  type StreamProcessorConfig,
  type FeedbackQueueConfig,
  type EventStreamConfig,
  // Default configs
  DEFAULT_FILE_WATCHER_CONFIG,
  DEFAULT_STREAM_PROCESSOR_CONFIG,
  DEFAULT_FEEDBACK_QUEUE_CONFIG,
  DEFAULT_EVENT_STREAM_CONFIG,
} from './realtime/index.js';
