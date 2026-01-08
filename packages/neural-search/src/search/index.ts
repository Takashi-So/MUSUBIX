/**
 * Search Engine Module
 * @module @nahisaho/musubix-neural-search/search
 */

export { PriorityQueue } from './PriorityQueue.js';
export { BeamSearch } from './BeamSearch.js';
export { BestFirstSearch } from './BestFirstSearch.js';
export { PruningManager } from './PruningManager.js';
export type { PruningConfig } from './PruningManager.js';

// Adaptive Search (v2.2.0 NEW!)
export { AdaptiveBeamSearch } from './AdaptiveBeamSearch.js';
export type {
  AdaptiveBeamConfig,
  AdaptiveStatistics,
} from './AdaptiveBeamSearch.js';
