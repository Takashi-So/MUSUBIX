/**
 * EnhancedLibraryLearner - v2.2.0 Integrated Library Learning
 * @module @nahisaho/musubix-library-learner
 * @see TSK-LL-109
 * @see DES-LL-109
 *
 * v2.2.0コンポーネントを統合した拡張LibraryLearner
 * - HierarchyManager: 階層的パターン管理
 * - TypeDirectedPruner: 型指向プルーニング
 * - RewriteRuleSet: 書き換えルール最適化
 * - IncrementalUpdater: 高速インクリメンタル更新
 */

import type {
  CodeCorpus,
  LearnResult,
  Specification,
  SynthesizeOptions,
  SynthesisResult,
  LibraryStats,
  LibraryLearnerConfig,
  LearnedPattern,
  ASTNode,
} from './types.js';

import { createLibraryLearner, type LibraryLearner } from './LibraryLearner.js';
import {
  createHierarchyManager,
  type HierarchyManager,
  type HierarchyMetrics,
} from './hierarchy/HierarchyManager.js';
import {
  createTypeDirectedPruner,
  type TypeDirectedPruner,
  type TypeSignature,
} from './search/TypeDirectedPruner.js';
import {
  createRewriteRuleSet,
  type RewriteRuleSet,
} from './rewrite/RewriteRuleSet.js';
import {
  createIncrementalUpdater,
  type IncrementalUpdater,
  type FileChange,
  type UpdateResult,
} from './updater/IncrementalUpdater.js';

// =============================================================================
// Types
// =============================================================================

/**
 * Enhanced configuration with v2.2.0 options
 */
export interface EnhancedLibraryLearnerConfig extends LibraryLearnerConfig {
  /** Enable hierarchy management (default: true) */
  enableHierarchyManagement?: boolean;
  /** Enable type-directed search (default: true) */
  enableTypedSearch?: boolean;
  /** Enable rewrite rules (default: true) */
  enableRewriteRules?: boolean;
  /** Enable incremental updates (default: true) */
  enableIncrementalUpdate?: boolean;
}

/**
 * Type-constrained synthesis specification
 */
export interface TypedSpecification {
  /** Description of desired function */
  description: string;
  /** Input types */
  inputTypes: string[];
  /** Output type */
  outputType: string;
  /** Optional examples */
  examples?: Array<{ input: unknown[]; output: unknown }>;
}

/**
 * Search statistics
 */
export interface SearchStats {
  /** Candidates examined */
  candidatesExamined: number;
  /** Candidates pruned */
  candidatesPruned: number;
  /** Search time in ms */
  searchTimeMs: number;
}

/**
 * Type-directed synthesis result
 */
export interface TypedSynthesisResult extends SynthesisResult {
  /** Search statistics */
  searchStats: SearchStats;
}

/**
 * Optimization result
 */
export interface OptimizationResult {
  /** Original program */
  original: string;
  /** Optimized program */
  optimized: string;
  /** Number of rewrites applied */
  rewritesApplied: number;
  /** Optimization time in ms */
  optimizationTimeMs: number;
}

/**
 * Enhanced statistics
 */
export interface EnhancedStats {
  /** Basic library stats */
  basic: LibraryStats;
  /** Hierarchy metrics */
  hierarchy: HierarchyMetrics;
  /** Rewrite rule stats */
  rewrite: { ruleCount: number; totalApplications: number };
  /** Incremental update stats */
  incremental: { totalChanges: number; averageTimeMs: number };
}

/**
 * EnhancedLibraryLearner interface
 */
export interface EnhancedLibraryLearner {
  // Base functionality
  learnFromCorpus(corpus: CodeCorpus): Promise<LearnResult>;
  learnIncremental(code: string): Promise<void>;
  synthesize(spec: Specification, options?: SynthesizeOptions): Promise<SynthesisResult>;
  getStats(): Promise<LibraryStats>;
  exportLibrary(): Promise<LearnedPattern[]>;
  importLibrary(patterns: LearnedPattern[]): Promise<void>;

  // v2.2.0 enhanced methods
  learnFromCode(code: string): Promise<LearnResult>;
  synthesizeWithTypes(spec: TypedSpecification): Promise<TypedSynthesisResult>;
  optimizeWithRewrites(program: string): Promise<OptimizationResult>;
  processFileChange(change: FileChange): Promise<UpdateResult>;

  // Component access
  getHierarchyManager(): HierarchyManager;
  getTypePruner(): TypeDirectedPruner;
  getRewriteRules(): RewriteRuleSet;
  getIncrementalUpdater(): IncrementalUpdater;

  // Enhanced stats
  getHierarchyMetrics(): HierarchyMetrics;
  getEnhancedStats(): Promise<EnhancedStats>;

  // Serialization
  toJSON(): string;
  fromJSON(json: string): void;
}

// =============================================================================
// Default Implementation
// =============================================================================

/**
 * Default implementation of EnhancedLibraryLearner
 */
class DefaultEnhancedLibraryLearner implements EnhancedLibraryLearner {
  private config: Required<EnhancedLibraryLearnerConfig>;
  private baseLearner: LibraryLearner;
  private hierarchyManager: HierarchyManager;
  private typePruner: TypeDirectedPruner;
  private rewriteRules: RewriteRuleSet;
  private incrementalUpdater: IncrementalUpdater;

  private rewriteApplications = 0;
  private lastHierarchyMetrics: HierarchyMetrics = {
    extractionTimeMs: 0,
    patternsPerLevel: [],
    compressionRatio: 1.0,
    totalPatternsRaw: 0,
    totalPatternsAbstracted: 0,
  };

  constructor(config: EnhancedLibraryLearnerConfig = {}) {
    this.config = {
      abstractionLevels: config.abstractionLevels ?? 3,
      minOccurrences: config.minOccurrences ?? 2,
      decayRate: config.decayRate ?? 0.95,
      pruneThreshold: config.pruneThreshold ?? 0.1,
      useEGraph: config.useEGraph ?? true,
      storagePath: config.storagePath ?? '.musubix/library',
      enableHierarchyManagement: config.enableHierarchyManagement ?? true,
      enableTypedSearch: config.enableTypedSearch ?? true,
      enableRewriteRules: config.enableRewriteRules ?? true,
      enableIncrementalUpdate: config.enableIncrementalUpdate ?? true,
    };

    // Initialize base learner
    this.baseLearner = createLibraryLearner({
      abstractionLevels: this.config.abstractionLevels,
      minOccurrences: this.config.minOccurrences,
      decayRate: this.config.decayRate,
      pruneThreshold: this.config.pruneThreshold,
      useEGraph: this.config.useEGraph,
      storagePath: this.config.storagePath,
    });

    // Initialize v2.2.0 components
    this.hierarchyManager = createHierarchyManager({
      maxLevels: this.config.abstractionLevels,
      promotionThreshold: 10,
    });

    this.typePruner = createTypeDirectedPruner({
      maxCandidates: 100,
      enableGenerics: true,
    });

    this.rewriteRules = createRewriteRuleSet({
      maxIterations: 10,
      enableBuiltinRules: true,
    });

    this.incrementalUpdater = createIncrementalUpdater({
      enableParallelProcessing: true,
      maxCacheSize: 1000,
    });
  }

  // =========================================================================
  // Base Functionality
  // =========================================================================

  async learnFromCorpus(corpus: CodeCorpus): Promise<LearnResult> {
    return this.baseLearner.learnFromCorpus(corpus);
  }

  async learnIncremental(code: string): Promise<void> {
    return this.baseLearner.learnIncremental(code);
  }

  async synthesize(
    spec: Specification,
    options?: SynthesizeOptions
  ): Promise<SynthesisResult> {
    return this.baseLearner.synthesize(spec, options);
  }

  async getStats(): Promise<LibraryStats> {
    return this.baseLearner.getStats();
  }

  async exportLibrary(): Promise<LearnedPattern[]> {
    return this.baseLearner.exportLibrary();
  }

  async importLibrary(patterns: LearnedPattern[]): Promise<void> {
    return this.baseLearner.importLibrary(patterns);
  }

  // =========================================================================
  // v2.2.0 Enhanced Methods
  // =========================================================================

  async learnFromCode(code: string): Promise<LearnResult> {
    const corpus: CodeCorpus = {
      id: `code-${Date.now()}`,
      files: [
        {
          path: 'input.ts',
          content: code,
          language: 'typescript',
        },
      ],
    };

    const result = await this.learnFromCorpus(corpus);

    // Update hierarchy if enabled
    if (this.config.enableHierarchyManagement) {
      const hierarchyResult = await this.hierarchyManager.extractHierarchy(corpus);
      this.lastHierarchyMetrics = hierarchyResult.metrics;
    }

    return result;
  }

  async synthesizeWithTypes(spec: TypedSpecification): Promise<TypedSynthesisResult> {
    const startTime = Date.now();
    let candidatesExamined = 0;
    let candidatesPruned = 0;

    // Get all patterns
    const patterns = await this.exportLibrary();
    candidatesExamined = patterns.length;

    // Apply type-directed pruning if enabled
    if (this.config.enableTypedSearch) {
      // Create type signature from spec
      const targetSignature: TypeSignature = {
        kind: 'function',
        params: spec.inputTypes,
        returns: spec.outputType,
      };

      // Prune candidates using type pruner
      const candidates = patterns.map((p) => ({
        id: p.id,
        ast: (typeof p.content === 'object' && p.content !== null && 'ast' in p.content 
          ? (p.content as { ast: ASTNode }).ast
          : { type: 'unknown' }) as ASTNode,
        typeSignature: {
          kind: 'function',
          params: spec.inputTypes,
          returns: spec.outputType,
        } as TypeSignature,
        score: p.confidence,
      }));

      const pruneResult = await this.typePruner.prune(candidates, targetSignature);
      candidatesPruned = candidates.length - pruneResult.candidates.length;
    }

    // Perform synthesis
    const inputTypes = spec.inputTypes.map((t: string) => ({
      kind: 'primitive' as const,
      name: t,
    }));

    const baseSpec: Specification = {
      description: spec.description,
      examples: spec.examples ?? [],
      type: {
        kind: 'function',
        paramTypes: inputTypes,
        returnType: { kind: 'primitive', name: spec.outputType },
      },
    };

    const result = await this.synthesize(baseSpec);

    return {
      ...result,
      searchStats: {
        candidatesExamined,
        candidatesPruned,
        searchTimeMs: Date.now() - startTime,
      },
    };
  }

  async optimizeWithRewrites(program: string): Promise<OptimizationResult> {
    const startTime = Date.now();
    let rewritesApplied = 0;

    if (!this.config.enableRewriteRules) {
      return {
        original: program,
        optimized: program,
        rewritesApplied: 0,
        optimizationTimeMs: Date.now() - startTime,
      };
    }

    // Convert program string to a simple AST node for rewriting
    const programAst: ASTNode = { type: 'Program', content: program };

    // Apply rewrites
    const result = this.rewriteRules.rewrite(programAst);

    if (result.changed) {
      rewritesApplied = result.rulesApplied.length;
    }

    this.rewriteApplications += rewritesApplied;

    // Extract optimized content
    const optimized = result.changed && 'content' in result.rewritten
      ? String(result.rewritten['content'])
      : program;

    return {
      original: program,
      optimized,
      rewritesApplied,
      optimizationTimeMs: Date.now() - startTime,
    };
  }

  async processFileChange(change: FileChange): Promise<UpdateResult> {
    if (!this.config.enableIncrementalUpdate) {
      return {
        success: true,
        changeType: change.changeType,
        processingTimeMs: 0,
        affectedPatterns: [],
        dependentFiles: [],
        cacheHit: false,
      };
    }

    return this.incrementalUpdater.processChange(change);
  }

  // =========================================================================
  // Component Access
  // =========================================================================

  getHierarchyManager(): HierarchyManager {
    return this.hierarchyManager;
  }

  getTypePruner(): TypeDirectedPruner {
    return this.typePruner;
  }

  getRewriteRules(): RewriteRuleSet {
    return this.rewriteRules;
  }

  getIncrementalUpdater(): IncrementalUpdater {
    return this.incrementalUpdater;
  }

  // =========================================================================
  // Enhanced Stats
  // =========================================================================

  getHierarchyMetrics(): HierarchyMetrics {
    // Return cached metrics from last extraction, or default if no extraction yet
    return this.lastHierarchyMetrics;
  }

  async getEnhancedStats(): Promise<EnhancedStats> {
    const basicStats = await this.getStats();
    const hierarchyMetrics = this.lastHierarchyMetrics;
    const incrementalStats = this.incrementalUpdater.getStatistics();

    return {
      basic: basicStats,
      hierarchy: hierarchyMetrics,
      rewrite: {
        ruleCount: this.rewriteRules.getRuleCount(),
        totalApplications: this.rewriteApplications,
      },
      incremental: {
        totalChanges: incrementalStats.totalChangesProcessed,
        averageTimeMs: incrementalStats.averageProcessingTimeMs,
      },
    };
  }

  // =========================================================================
  // Serialization
  // =========================================================================

  toJSON(): string {
    return JSON.stringify({
      // IncrementalUpdater has toJSON/fromJSON
      incrementalState: this.incrementalUpdater.toJSON(),
      rewriteApplications: this.rewriteApplications,
      lastHierarchyMetrics: this.lastHierarchyMetrics,
    });
  }

  fromJSON(json: string): void {
    const data = JSON.parse(json);

    // IncrementalUpdater has fromJSON
    if (data.incrementalState) {
      this.incrementalUpdater.fromJSON(data.incrementalState);
    }
    if (data.rewriteApplications !== undefined) {
      this.rewriteApplications = data.rewriteApplications;
    }
    if (data.lastHierarchyMetrics) {
      this.lastHierarchyMetrics = data.lastHierarchyMetrics;
    }
  }
}

// =============================================================================
// Factory Function
// =============================================================================

/**
 * Create an EnhancedLibraryLearner instance
 * @param config - Optional configuration
 * @returns EnhancedLibraryLearner instance
 */
export function createEnhancedLibraryLearner(
  config: EnhancedLibraryLearnerConfig = {}
): EnhancedLibraryLearner {
  return new DefaultEnhancedLibraryLearner(config);
}

export { DefaultEnhancedLibraryLearner };
