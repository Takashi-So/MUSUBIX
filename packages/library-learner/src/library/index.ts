/**
 * Library Manager exports
 */

export type { LibraryStore } from './LibraryStore.js';
export { createLibraryStore } from './LibraryStore.js';
export type { Consolidator } from './Consolidator.js';
export { createConsolidator } from './Consolidator.js';
export type { Pruner } from './Pruner.js';
export { createPruner } from './Pruner.js';

// IterativeCompressor (v2.2.0 NEW!)
export {
  createIterativeCompressor,
  DefaultIterativeCompressor,
} from './IterativeCompressor.js';
export type {
  IterativeCompressor,
  IterativeCompressorConfig,
  CompressionReport,
  MergedGroup,
  CompressionStatistics,
} from './IterativeCompressor.js';

// PatternVersionManager (v2.2.0 NEW!)
export {
  createPatternVersionManager,
  DefaultPatternVersionManager,
} from './PatternVersionManager.js';
export type {
  PatternVersionManager,
  PatternVersionManagerConfig,
  VersionMetadata,
  VersionEntry,
  VersionDiff,
  VersionChange,
  VersionStatistics,
} from './PatternVersionManager.js';
