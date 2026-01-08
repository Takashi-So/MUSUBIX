/**
 * @nahisaho/musubix-library-learner
 *
 * DreamCoder-style hierarchical abstraction and library learning for MUSUBIX.
 * Provides pattern mining, abstraction, type-directed search, and E-graph optimization.
 *
 * @packageDocumentation
 * @module @nahisaho/musubix-library-learner
 *
 * @example
 * ```typescript
 * import { LibraryLearner, createLibraryLearner } from '@nahisaho/musubix-library-learner';
 *
 * const learner = createLibraryLearner({
 *   abstractionLevels: 3,
 *   minOccurrences: 2,
 * });
 *
 * // Learn from code corpus
 * await learner.learnFromCorpus(corpus);
 *
 * // Use library for synthesis
 * const result = await learner.synthesize(spec);
 * ```
 */

// Types
export * from './types.js';

// Errors
export * from './errors.js';

// Abstraction Engine
export type { PatternMiner } from './abstraction/PatternMiner.js';
export { createPatternMiner } from './abstraction/PatternMiner.js';
export type { Abstractor } from './abstraction/Abstractor.js';
export { createAbstractor } from './abstraction/Abstractor.js';
export type { TypeAnalyzer } from './abstraction/TypeAnalyzer.js';
export { createTypeAnalyzer } from './abstraction/TypeAnalyzer.js';

// Library Manager
export type { LibraryStore } from './library/LibraryStore.js';
export { createLibraryStore } from './library/LibraryStore.js';
export type { Consolidator } from './library/Consolidator.js';
export { createConsolidator } from './library/Consolidator.js';
export type { Pruner } from './library/Pruner.js';
export { createPruner } from './library/Pruner.js';

// E-Graph Optimizer
export type { EGraph } from './egraph/EGraph.js';
export { createEGraph } from './egraph/EGraph.js';
export type { EGraphBuilder } from './egraph/EGraphBuilder.js';
export { createEGraphBuilder } from './egraph/EGraphBuilder.js';
export type { Extractor } from './egraph/Extractor.js';
export { createExtractor } from './egraph/Extractor.js';

// Hierarchy Manager (v2.2.0 NEW!)
export type {
  HierarchyManager,
  AbstractionLevel,
  PromotionRecord,
  HierarchyMetrics,
  HierarchyResult,
  HierarchyManagerConfig,
  HierarchyPattern,
} from './hierarchy/HierarchyManager.js';
export { createHierarchyManager, DefaultHierarchyManager } from './hierarchy/HierarchyManager.js';

// Type-Directed Search (v2.2.0 NEW!)
export type {
  TypeDirectedPruner,
  TypeSignature,
  PruneCandidate,
  PruneResult,
  TypeDirectedPrunerConfig,
} from './search/TypeDirectedPruner.js';
export { createTypeDirectedPruner, DefaultTypeDirectedPruner } from './search/TypeDirectedPruner.js';

// Rewrite Rules (v2.2.0 NEW!)
export type {
  RewriteRuleSet,
  RewriteRule,
  RewriteResult,
  RewriteRuleSetConfig,
  Pattern,
} from './rewrite/RewriteRuleSet.js';
export { createRewriteRuleSet, DefaultRewriteRuleSet } from './rewrite/RewriteRuleSet.js';

// Incremental Updater (v2.2.0 NEW!)
export type {
  IncrementalUpdater,
  UpdaterConfig,
  FileChange,
  ChangeType,
  UpdateResult,
  UpdateStatistics,
} from './updater/IncrementalUpdater.js';
export { createIncrementalUpdater, DefaultIncrementalUpdater } from './updater/IncrementalUpdater.js';

// IterativeCompressor (v2.2.0 NEW!)
export {
  createIterativeCompressor,
  DefaultIterativeCompressor,
} from './library/IterativeCompressor.js';
export type {
  IterativeCompressor,
  IterativeCompressorConfig,
  CompressionReport,
  MergedGroup,
  CompressionStatistics,
} from './library/IterativeCompressor.js';

// PatternVersionManager (v2.2.0 NEW!)
export {
  createPatternVersionManager,
  DefaultPatternVersionManager,
} from './library/PatternVersionManager.js';
export type {
  PatternVersionManager,
  PatternVersionManagerConfig,
  VersionMetadata,
  VersionEntry,
  VersionDiff,
  VersionChange,
  VersionStatistics,
} from './library/PatternVersionManager.js';

// DomainAwareAbstractor (v2.2.0 NEW!)
export {
  createDomainAwareAbstractor,
  DefaultDomainAwareAbstractor,
} from './domain/DomainAwareAbstractor.js';
export type {
  DomainAwareAbstractor,
  DomainAwareAbstractorConfig,
  DomainOntology,
  DomainConcept,
  ConceptRelation,
  DomainConstraint,
  DomainAbstractionResult,
  ConceptHierarchy,
  OntologyLoadResult,
  AbstractionStatistics as DomainAbstractionStatistics,
} from './domain/DomainAwareAbstractor.js';

// MetricsExporter (v2.2.0 NEW!)
export {
  createMetricsExporter,
  DefaultMetricsExporter,
} from './metrics/MetricsExporter.js';
export type {
  MetricsExporter,
  LibraryMetrics,
  FormattedMetrics,
  MetricsSummary,
  LibraryState,
  PatternUsageInfo,
  ExportFormat,
} from './metrics/MetricsExporter.js';

// Enhanced Library Learner (v2.2.0 NEW!)
export type {
  EnhancedLibraryLearner,
  EnhancedLibraryLearnerConfig,
  TypedSpecification,
  TypedSynthesisResult,
  OptimizationResult,
  EnhancedStats,
  SearchStats,
} from './EnhancedLibraryLearner.js';
export { createEnhancedLibraryLearner, DefaultEnhancedLibraryLearner } from './EnhancedLibraryLearner.js';

// High-level API
export type { LibraryLearner } from './LibraryLearner.js';
export { createLibraryLearner } from './LibraryLearner.js';
