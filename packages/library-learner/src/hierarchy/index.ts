/**
 * Hierarchy Module - Hierarchical Pattern Abstraction
 *
 * @module @nahisaho/musubix-library-learner/hierarchy
 * @see TSK-LL-101
 */

export type {
  HierarchyManager,
  AbstractionLevel,
  PromotionRecord,
  HierarchyMetrics,
  HierarchyResult,
  HierarchyManagerConfig,
  HierarchyPattern,
} from './HierarchyManager.js';

export { createHierarchyManager, DefaultHierarchyManager } from './HierarchyManager.js';
