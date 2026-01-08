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

// High-level API
export type { LibraryLearner } from './LibraryLearner.js';
export { createLibraryLearner } from './LibraryLearner.js';
