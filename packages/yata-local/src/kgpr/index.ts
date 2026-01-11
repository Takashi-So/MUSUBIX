/**
 * YATA Local KGPR Module - Knowledge Graph Pull Request for Local KG
 *
 * Provides Privacy-aware KGPR creation from local knowledge graphs
 *
 * @packageDocumentation
 * @module @nahisaho/yata-local/kgpr
 *
 * @see REQ-YL-EXT-KGPR-001
 */

export { LocalKGPRManager, createLocalKGPRManager } from './kgpr-manager.js';
export { LocalPrivacyFilter, createLocalPrivacyFilter } from './privacy-filter.js';
export { LocalDiffEngine, createLocalDiffEngine } from './diff-engine.js';
export { KGPRSyncManager, createKGPRSyncManager } from './sync-manager.js';
export type { GlobalServerConfig, PushResult } from './sync-manager.js';
export type {
  LocalKGPRInfo,
  LocalKGPRDiff,
  LocalKGPRReviewEntry,
  LocalEntityChange,
  LocalRelationshipChange,
  LocalDiffStats,
  CreateLocalKGPROptions,
  ListLocalKGPROptions,
  LocalPrivacyFilterConfig,
  KGSnapshot,
  DiffOptions,
  ChangeType,
} from './types.js';
// Re-export base types
export type { KGPRStatusLocal, PrivacyLevel } from '../types.js';
