/**
 * LibraryLearner - High-level API for library learning
 *
 * REQ-LL-001: 階層的抽象化
 * REQ-LL-002: ライブラリ成長
 * REQ-LL-003: 型指向探索
 * REQ-LL-004: E-graph最適化
 *
 * DES-PHASE2-001: High-level API
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
  ConcretePattern,
} from './types.js';

import { createPatternMiner, type PatternMiner } from './abstraction/PatternMiner.js';
import { createAbstractor, type Abstractor } from './abstraction/Abstractor.js';
import { createTypeAnalyzer, type TypeAnalyzer } from './abstraction/TypeAnalyzer.js';
import { createLibraryStore, type LibraryStore } from './library/LibraryStore.js';
import { createConsolidator, type Consolidator } from './library/Consolidator.js';
import { createPruner, type Pruner } from './library/Pruner.js';
import { createEGraphBuilder, type EGraphBuilder } from './egraph/EGraphBuilder.js';
import { createExtractor, type Extractor } from './egraph/Extractor.js';

/**
 * LibraryLearner interface
 */
export interface LibraryLearner {
  /** Learn patterns from a code corpus */
  learnFromCorpus(corpus: CodeCorpus): Promise<LearnResult>;

  /** Incremental learning from single code snippet */
  learnIncremental(code: string): Promise<void>;

  /** Synthesize code using learned library */
  synthesize(spec: Specification, options?: SynthesizeOptions): Promise<SynthesisResult>;

  /** Get the pattern library */
  getLibrary(): LibraryStore;

  /** Get library statistics */
  getStats(): Promise<LibraryStats>;

  /** Export library data */
  exportLibrary(): Promise<LearnedPattern[]>;

  /** Import library data */
  importLibrary(patterns: LearnedPattern[]): Promise<void>;
}

/**
 * Default LibraryLearner implementation
 */
class LibraryLearnerImpl implements LibraryLearner {
  private config: Required<LibraryLearnerConfig>;
  private patternMiner: PatternMiner;
  private abstractor: Abstractor;
  // @ts-expect-error - Will be used in type-directed synthesis
  private typeAnalyzer: TypeAnalyzer;
  private libraryStore: LibraryStore;
  private consolidator: Consolidator;
  // @ts-expect-error - Will be used in maintenance operations
  private pruner: Pruner;
  private egraphBuilder: EGraphBuilder;
  private extractor: Extractor;

  constructor(config: LibraryLearnerConfig = {}) {
    this.config = {
      abstractionLevels: config.abstractionLevels ?? 3,
      minOccurrences: config.minOccurrences ?? 2,
      decayRate: config.decayRate ?? 0.95,
      pruneThreshold: config.pruneThreshold ?? 0.1,
      useEGraph: config.useEGraph ?? true,
      storagePath: config.storagePath ?? '.musubix/library',
    };

    // Initialize components
    this.patternMiner = createPatternMiner({
      minOccurrences: this.config.minOccurrences,
    });
    this.abstractor = createAbstractor();
    this.typeAnalyzer = createTypeAnalyzer();
    this.libraryStore = createLibraryStore();
    this.consolidator = createConsolidator();
    this.pruner = createPruner();
    this.egraphBuilder = createEGraphBuilder();
    this.extractor = createExtractor();
  }

  async learnFromCorpus(corpus: CodeCorpus): Promise<LearnResult> {
    const startTime = Date.now();

    // Step 1: Mine patterns
    const candidates = await this.patternMiner.mine(corpus);

    // Step 2: Hierarchical abstraction
    const { concrete, templates, concepts } = this.abstractor.abstract(candidates);

    // Step 3: Store patterns in library
    let patternsAdded = 0;

    // Add level 1 patterns (concrete)
    for (const pattern of concrete) {
      await this.libraryStore.add(this.createLearnedPattern(pattern, 1));
      patternsAdded++;
    }

    // Add level 2 patterns (templates) if configured
    if (this.config.abstractionLevels >= 2) {
      for (const template of templates) {
        await this.libraryStore.add({
          id: template.id,
          name: `Template: ${template.id}`,
          level: 2,
          content: template,
          usageCount: 0,
          confidence: 0.7,
          createdAt: new Date(),
          lastUsedAt: new Date(),
          tags: ['template'],
        });
        patternsAdded++;
      }
    }

    // Add level 3 patterns (concepts) if configured
    if (this.config.abstractionLevels >= 3) {
      for (const concept of concepts) {
        await this.libraryStore.add({
          id: concept.id,
          name: concept.name,
          level: 3,
          content: concept,
          usageCount: 0,
          confidence: 0.6,
          createdAt: new Date(),
          lastUsedAt: new Date(),
          tags: ['concept', concept.category],
        });
        patternsAdded++;
      }
    }

    // Step 4: Consolidate similar patterns
    const consolidationReport = await this.consolidator.consolidateLibrary(this.libraryStore);

    return {
      patternsExtracted: candidates.length,
      patternsAdded,
      patternsConsolidated: consolidationReport.patternsMerged,
      duration: Date.now() - startTime,
    };
  }

  async learnIncremental(code: string): Promise<void> {
    const corpus: CodeCorpus = {
      id: `incremental-${Date.now()}`,
      files: [
        {
          path: 'incremental.ts',
          content: code,
          language: 'typescript',
        },
      ],
    };

    await this.learnFromCorpus(corpus);
  }

  async synthesize(
    spec: Specification,
    options: SynthesizeOptions = {}
  ): Promise<SynthesisResult> {
    const startTime = Date.now();
    const patternsUsed: string[] = [];

    // Get all patterns from library
    const patterns = await this.libraryStore.getAll();

    // Filter patterns by type if specified
    let candidates = patterns;
    if (spec.type && options.useTypeDirected !== false) {
      // Use type analyzer to filter
      // Note: This is simplified - full implementation would need pattern type inference
      candidates = patterns.filter((p) => p.confidence > 0.5);
    }

    // Build e-graph if enabled
    if (this.config.useEGraph && options.useEGraph !== false) {
      const graph = this.egraphBuilder.build(candidates);
      const optimal = this.extractor.extract(graph, (_node, childCosts) => {
        // Simple cost function: prefer smaller expressions
        return 1 + childCosts.reduce((a, b) => a + b, 0);
      });

      if (optimal.cost < Infinity) {
        patternsUsed.push(...candidates.slice(0, 1).map((p) => p.id));

        return {
          success: true,
          program: optimal.ast,
          candidates: [optimal.ast],
          duration: Date.now() - startTime,
          searchNodes: candidates.length,
          patternsUsed,
        };
      }
    }

    // Fallback: no synthesis possible
    return {
      success: false,
      duration: Date.now() - startTime,
      searchNodes: candidates.length,
      patternsUsed,
    };
  }

  getLibrary(): LibraryStore {
    return this.libraryStore;
  }

  async getStats(): Promise<LibraryStats> {
    const patterns = await this.libraryStore.getAll();

    const patternsByLevel: Record<1 | 2 | 3, number> = { 1: 0, 2: 0, 3: 0 };
    let totalConfidence = 0;
    let totalUsageCount = 0;

    for (const pattern of patterns) {
      patternsByLevel[pattern.level]++;
      totalConfidence += pattern.confidence;
      totalUsageCount += pattern.usageCount;
    }

    const sortedByUsage = [...patterns].sort((a, b) => b.usageCount - a.usageCount);

    return {
      totalPatterns: patterns.length,
      patternsByLevel,
      averageConfidence: patterns.length > 0 ? totalConfidence / patterns.length : 0,
      averageUsageCount: patterns.length > 0 ? totalUsageCount / patterns.length : 0,
      mostUsed: sortedByUsage.slice(0, 5).map((p) => p.id),
      leastUsed: sortedByUsage.slice(-5).map((p) => p.id),
    };
  }

  async exportLibrary(): Promise<LearnedPattern[]> {
    return this.libraryStore.getAll();
  }

  async importLibrary(patterns: LearnedPattern[]): Promise<void> {
    for (const pattern of patterns) {
      await this.libraryStore.add(pattern);
    }
  }

  // =========================================================================
  // Private methods
  // =========================================================================

  private createLearnedPattern(concrete: ConcretePattern, level: 1 | 2 | 3): LearnedPattern {
    return {
      id: concrete.id,
      name: `Pattern: ${concrete.ast.type}`,
      level,
      content: concrete,
      usageCount: 0,
      confidence: Math.min(0.5 + concrete.occurrenceCount * 0.1, 1.0),
      createdAt: new Date(),
      lastUsedAt: new Date(),
      tags: [concrete.ast.type.toLowerCase()],
    };
  }
}

/**
 * Factory function to create a LibraryLearner
 */
export function createLibraryLearner(config?: LibraryLearnerConfig): LibraryLearner {
  return new LibraryLearnerImpl(config);
}
