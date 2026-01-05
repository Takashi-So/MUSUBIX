/**
 * @fileoverview Wake-Sleep Learning Module for YATA Local
 * @module @nahisaho/yata-local/wake-sleep
 * @version 0.1.0
 * @license MIT
 * 
 * Trace: REQ-WSL-001, REQ-WSL-002, REQ-WSL-003, REQ-WSL-005
 */

// Type exports
export type {
  LocalPatternCandidate,
  LocalPatternType,
  LocalPatternCluster,
  LocalConsolidatedPattern,
  WakeObserveOptions,
  WakeObserveResult,
  SleepClusterOptions,
  SleepClusterResult,
  CompressOptions,
  LocalLearningCycleResult,
  LocalLearningCycleMetadata,
  LearningCycleStatus,
  SimilarityMethod,
  WakeSleepConfig,
} from './types.js';

// Constants
export { DEFAULT_WAKE_SLEEP_CONFIG } from './types.js';

// Wake Phase
export { LocalWakePhase, createLocalWakePhase } from './wake-phase.js';

// Sleep Phase
export { LocalSleepPhase, createLocalSleepPhase } from './sleep-phase.js';

// Pattern Compressor
export { LocalPatternCompressor, createLocalPatternCompressor } from './pattern-compressor.js';

// Cycle Manager
export { LocalWakeSleepCycle, createLocalWakeSleepCycle } from './cycle-manager.js';
