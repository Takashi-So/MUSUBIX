/**
 * Updater module - Incremental update functionality
 * @module @nahisaho/musubix-library-learner/updater
 */

export {
  createIncrementalUpdater,
  DefaultIncrementalUpdater,
} from './IncrementalUpdater.js';

export type {
  IncrementalUpdater,
  UpdaterConfig,
  FileChange,
  ChangeType,
  UpdateResult,
  UpdateStatistics,
} from './IncrementalUpdater.js';
