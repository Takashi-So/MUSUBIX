/**
 * HierarchyManager - Hierarchical Abstraction Manager
 *
 * DreamCoder-style hierarchical pattern abstraction for library learning.
 * Manages multiple levels of abstraction from concrete to abstract patterns.
 *
 * @module @nahisaho/musubix-library-learner
 * @see TSK-LL-101
 * @see DES-LL-101
 * @see REQ-LL-101
 *
 * 既存クラス関係: LibraryLearner.extractPatterns() から委譲される新規コンポーネント
 * 依存: PatternMiner, Abstractor (既存)
 *
 * @example
 * ```typescript
 * import { createHierarchyManager } from './HierarchyManager.js';
 *
 * const manager = createHierarchyManager({ maxLevels: 4 });
 * const result = await manager.extractHierarchy(corpus);
 * console.log(`Extracted ${result.levels.size} levels`);
 * ```
 */

import type {
  CodeCorpus,
  PatternCandidate,
  PatternId,
  ASTNode,
  PatternOccurrence,
} from '../types.js';
import type { PatternMiner } from '../abstraction/PatternMiner.js';
import type { Abstractor } from '../abstraction/Abstractor.js';

// =============================================================================
// Types
// =============================================================================

/**
 * Internal pattern representation for hierarchy extraction.
 * Different from library's HierarchyPattern as this is used during extraction.
 */
export interface HierarchyPattern {
  /** Unique pattern identifier */
  id: PatternId;
  /** Abstraction level (1=concrete, 2=parameterized, 3=abstract, 4+=composite) */
  level: number;
  /** Number of occurrences in corpus */
  occurrenceCount: number;
  /** Confidence score (0-1) */
  confidence: number;
  /** Abstract syntax tree representation */
  ast: ASTNode;
  /** Source locations where pattern was found */
  sourceLocations: PatternOccurrence[];
}

/**
 * Abstraction level definition
 */
export interface AbstractionLevel {
  /** Unique level identifier (1-based) */
  id: number;
  /** Human-readable name */
  name: string;
  /** Description of this abstraction level */
  description: string;
  /** Minimum occurrences to be considered at this level */
  minOccurrences?: number;
}

/**
 * Record of a pattern promotion between levels
 */
export interface PromotionRecord {
  /** Pattern that was promoted */
  patternId: PatternId;
  /** Source level */
  fromLevel: number;
  /** Target level */
  toLevel: number;
  /** Timestamp of promotion */
  timestamp: Date;
  /** Confidence score at promotion */
  confidence: number;
}

/**
 * Metrics for hierarchy extraction
 */
export interface HierarchyMetrics {
  /** Time taken for extraction in milliseconds */
  extractionTimeMs: number;
  /** Number of patterns per level */
  patternsPerLevel: number[];
  /** Compression ratio achieved */
  compressionRatio: number;
  /** Total patterns before abstraction */
  totalPatternsRaw: number;
  /** Total patterns after abstraction */
  totalPatternsAbstracted: number;
}

/**
 * Result of hierarchy extraction
 */
export interface HierarchyResult {
  /** Patterns organized by level */
  levels: Map<number, HierarchyPattern[]>;
  /** Records of pattern promotions */
  promotions: PromotionRecord[];
  /** Extraction metrics */
  metrics: HierarchyMetrics;
}

/**
 * Configuration for HierarchyManager
 */
export interface HierarchyManagerConfig {
  /** Maximum number of abstraction levels */
  maxLevels?: number;
  /** Threshold for pattern promotion */
  promotionThreshold?: number;
  /** Minimum occurrences for promotion */
  minOccurrences?: number;
  /** External PatternMiner (optional, for DI) */
  patternMiner?: PatternMiner;
  /** External Abstractor (optional, for DI) */
  abstractor?: Abstractor;
}

/**
 * HierarchyManager interface
 *
 * Manages hierarchical pattern abstraction at multiple levels:
 * - Level 1: ConcretePattern (token-level)
 * - Level 2: ParameterizedTemplate (expression-level)
 * - Level 3: AbstractConcept (function-level)
 * - Level 4+: CompositeAbstraction (composite patterns)
 */
export interface HierarchyManager {
  /** Add a new abstraction level */
  addLevel(level: AbstractionLevel): void;

  /** Extract hierarchical abstractions from a code corpus */
  extractHierarchy(corpus: CodeCorpus): Promise<HierarchyResult>;

  /** Determine if a pattern should be promoted to a higher level */
  shouldPromote(pattern: HierarchyPattern): boolean;

  /** Get the current depth (number of levels) */
  getDepth(): number;

  /** Get all registered abstraction levels */
  getLevels(): AbstractionLevel[];
}

// =============================================================================
// Default Implementation
// =============================================================================

/**
 * Default built-in abstraction levels
 */
const DEFAULT_LEVELS: AbstractionLevel[] = [
  { id: 1, name: 'concrete', description: 'Token-level patterns', minOccurrences: 2 },
  { id: 2, name: 'parameterized', description: 'Expression-level templates', minOccurrences: 3 },
  { id: 3, name: 'abstract', description: 'Function-level concepts', minOccurrences: 5 },
  { id: 4, name: 'composite', description: 'Composite patterns', minOccurrences: 10 },
];

/**
 * Default HierarchyManager implementation
 */
export class DefaultHierarchyManager implements HierarchyManager {
  private levels: Map<number, AbstractionLevel> = new Map();
  private patterns: Map<number, HierarchyPattern[]> = new Map();
  private promotions: PromotionRecord[] = [];
  private config: Required<HierarchyManagerConfig>;

  constructor(config: HierarchyManagerConfig = {}) {
    this.config = {
      maxLevels: config.maxLevels ?? 4,
      promotionThreshold: config.promotionThreshold ?? 0.7,
      minOccurrences: config.minOccurrences ?? 3,
      patternMiner: config.patternMiner ?? null!,
      abstractor: config.abstractor ?? null!,
    };
  }

  /**
   * Add a new abstraction level
   * @throws Error if level ID already exists
   */
  addLevel(level: AbstractionLevel): void {
    if (this.levels.has(level.id)) {
      throw new Error(`Duplicate level ID: ${level.id}`);
    }
    this.levels.set(level.id, level);
  }

  /**
   * Extract hierarchical abstractions from a code corpus
   *
   * Process:
   * 1. Mine concrete patterns (Level 1)
   * 2. Abstract to parameterized templates (Level 2)
   * 3. Extract function-level concepts (Level 3)
   * 4. Compose higher-level patterns (Level 4+)
   */
  async extractHierarchy(corpus: CodeCorpus): Promise<HierarchyResult> {
    const startTime = Date.now();

    // Initialize default levels if none added
    if (this.levels.size === 0) {
      DEFAULT_LEVELS.forEach((level) => this.addLevel(level));
    }

    // Step 1: Mine concrete patterns
    const concretePatterns = await this.mineConcretePatterns(corpus);
    this.patterns.set(1, concretePatterns);

    // Step 2: Abstract to parameterized templates
    const parameterizedPatterns = await this.abstractToTemplates(concretePatterns);
    this.patterns.set(2, parameterizedPatterns);

    // Step 3: Extract function-level concepts
    const abstractPatterns = await this.extractAbstractConcepts(parameterizedPatterns);
    this.patterns.set(3, abstractPatterns);

    // Step 4: Compose higher-level patterns
    if (this.config.maxLevels >= 4) {
      const compositePatterns = await this.composeHigherLevel(abstractPatterns);
      this.patterns.set(4, compositePatterns);
    }

    const endTime = Date.now();

    // Calculate metrics
    const totalRaw = concretePatterns.length;
    const totalAbstracted = Array.from(this.patterns.values()).reduce(
      (sum, patterns) => sum + patterns.length,
      0
    );

    const metrics: HierarchyMetrics = {
      extractionTimeMs: endTime - startTime,
      patternsPerLevel: Array.from(this.patterns.entries())
        .sort(([a], [b]) => a - b)
        .map(([, patterns]) => patterns.length),
      compressionRatio: totalRaw > 0 ? totalAbstracted / totalRaw : 0,
      totalPatternsRaw: totalRaw,
      totalPatternsAbstracted: totalAbstracted,
    };

    return {
      levels: new Map(this.patterns),
      promotions: [...this.promotions],
      metrics,
    };
  }

  /**
   * Determine if a pattern should be promoted to a higher level
   */
  shouldPromote(pattern: HierarchyPattern): boolean {
    const meetsOccurrenceThreshold = pattern.occurrenceCount >= this.config.minOccurrences;
    const meetsConfidenceThreshold = pattern.confidence >= this.config.promotionThreshold;
    return meetsOccurrenceThreshold && meetsConfidenceThreshold;
  }

  /**
   * Get the current depth (number of levels)
   */
  getDepth(): number {
    return this.levels.size;
  }

  /**
   * Get all registered abstraction levels
   */
  getLevels(): AbstractionLevel[] {
    return Array.from(this.levels.values()).sort((a, b) => a.id - b.id);
  }

  // ===========================================================================
  // Private Methods
  // ===========================================================================

  /**
   * Mine concrete patterns from corpus (Level 1)
   */
  private async mineConcretePatterns(corpus: CodeCorpus): Promise<HierarchyPattern[]> {
    // If external PatternMiner is provided, use it
    if (this.config.patternMiner) {
      const candidates = await this.config.patternMiner.mine(corpus);
      return this.candidatesToHierarchyPatterns(candidates, 1);
    }

    // Simple built-in mining for testing
    const patterns: HierarchyPattern[] = [];
    let patternCounter = 0;

    for (const file of corpus.files) {
      // Simple AST simulation: split into statements
      const lines = file.content.split('\n').filter((l) => l.trim());
      const statementCounts = new Map<string, number>();

      for (const line of lines) {
        const normalized = this.normalizeStatement(line);
        statementCounts.set(normalized, (statementCounts.get(normalized) || 0) + 1);
      }

      for (const [statement, count] of statementCounts) {
        if (count >= 2) {
          patterns.push({
            id: `pattern-${++patternCounter}` as PatternId,
            level: 1,
            occurrenceCount: count,
            confidence: Math.min(0.5 + count * 0.1, 1.0),
            ast: { type: 'Statement', value: statement } as unknown as ASTNode,
            sourceLocations: [],
          });
        }
      }
    }

    return patterns;
  }

  /**
   * Abstract concrete patterns to parameterized templates (Level 2)
   */
  private async abstractToTemplates(patterns: HierarchyPattern[]): Promise<HierarchyPattern[]> {
    // Simple abstraction: group similar patterns
    const templates: HierarchyPattern[] = [];
    const groups = this.groupSimilarPatterns(patterns);
    let templateCounter = 0;

    for (const group of groups.values()) {
      if (group.length >= 2) {
        const combinedOccurrences = group.reduce((sum, p) => sum + p.occurrenceCount, 0);
        const avgConfidence = group.reduce((sum, p) => sum + p.confidence, 0) / group.length;

        const template: HierarchyPattern = {
          id: `template-${++templateCounter}` as PatternId,
          level: 2,
          occurrenceCount: combinedOccurrences,
          confidence: avgConfidence,
          ast: { type: 'Template', children: group.map((p) => p.ast) } as unknown as ASTNode,
          sourceLocations: group.flatMap((p) => p.sourceLocations),
        };

        // Record promotions
        for (const pattern of group) {
          if (this.shouldPromote(pattern)) {
            this.promotions.push({
              patternId: pattern.id,
              fromLevel: 1,
              toLevel: 2,
              timestamp: new Date(),
              confidence: pattern.confidence,
            });
          }
        }

        templates.push(template);
      }
    }

    return templates;
  }

  /**
   * Extract function-level concepts (Level 3)
   */
  private async extractAbstractConcepts(templates: HierarchyPattern[]): Promise<HierarchyPattern[]> {
    const concepts: HierarchyPattern[] = [];
    let conceptCounter = 0;

    // Group templates by structural similarity
    const conceptGroups = this.groupByStructure(templates);

    for (const group of conceptGroups.values()) {
      if (group.length >= 1) {
        const combinedOccurrences = group.reduce((sum, p) => sum + p.occurrenceCount, 0);
        const avgConfidence = group.reduce((sum, p) => sum + p.confidence, 0) / group.length;

        const concept: HierarchyPattern = {
          id: `concept-${++conceptCounter}` as PatternId,
          level: 3,
          occurrenceCount: combinedOccurrences,
          confidence: Math.min(avgConfidence * 1.1, 1.0), // Slight confidence boost
          ast: { type: 'Concept', templates: group.map((t) => t.ast) } as unknown as ASTNode,
          sourceLocations: group.flatMap((t) => t.sourceLocations),
        };

        concepts.push(concept);
      }
    }

    return concepts;
  }

  /**
   * Compose higher-level patterns (Level 4+)
   */
  private async composeHigherLevel(concepts: HierarchyPattern[]): Promise<HierarchyPattern[]> {
    const composites: HierarchyPattern[] = [];
    let compositeCounter = 0;

    // Combine concepts that often appear together
    if (concepts.length >= 2) {
      const combinedOccurrences = concepts.reduce((sum, c) => sum + c.occurrenceCount, 0);
      const avgConfidence = concepts.reduce((sum, c) => sum + c.confidence, 0) / concepts.length;

      const composite: HierarchyPattern = {
        id: `composite-${++compositeCounter}` as PatternId,
        level: 4,
        occurrenceCount: Math.floor(combinedOccurrences / concepts.length),
        confidence: avgConfidence,
        ast: { type: 'Composite', concepts: concepts.map((c) => c.ast) } as unknown as ASTNode,
        sourceLocations: concepts.flatMap((c) => c.sourceLocations),
      };

      composites.push(composite);
    }

    return composites;
  }

  /**
   * Convert pattern candidates to learned patterns
   */
  private candidatesToHierarchyPatterns(
    candidates: PatternCandidate[],
    level: number
  ): HierarchyPattern[] {
    return candidates.map((c) => ({
      id: c.id,
      level,
      occurrenceCount: c.occurrences.length,
      confidence: c.score,
      ast: c.ast,
      sourceLocations: c.occurrences,
    }));
  }

  /**
   * Normalize a statement for comparison
   */
  private normalizeStatement(statement: string): string {
    return statement
      .trim()
      .replace(/\s+/g, ' ')
      .replace(/['"]/g, '"')
      .replace(/\b\d+\b/g, 'N')
      .replace(/\b[a-z][a-zA-Z0-9]*\b/g, (match) => {
        // Keep keywords, normalize identifiers
        const keywords = ['function', 'const', 'let', 'var', 'return', 'if', 'else', 'for', 'while'];
        return keywords.includes(match) ? match : 'ID';
      });
  }

  /**
   * Group similar patterns by normalized form
   */
  private groupSimilarPatterns(patterns: HierarchyPattern[]): Map<string, HierarchyPattern[]> {
    const groups = new Map<string, HierarchyPattern[]>();

    for (const pattern of patterns) {
      const key = this.getPatternSignature(pattern);
      const group = groups.get(key) || [];
      group.push(pattern);
      groups.set(key, group);
    }

    return groups;
  }

  /**
   * Group by structural pattern
   */
  private groupByStructure(patterns: HierarchyPattern[]): Map<string, HierarchyPattern[]> {
    const groups = new Map<string, HierarchyPattern[]>();

    for (const pattern of patterns) {
      const key = this.getStructuralSignature(pattern);
      const group = groups.get(key) || [];
      group.push(pattern);
      groups.set(key, group);
    }

    return groups;
  }

  /**
   * Get a signature for pattern similarity grouping
   */
  private getPatternSignature(pattern: HierarchyPattern): string {
    const ast = pattern.ast as unknown as { type: string; value?: string };
    return `${ast.type}:${pattern.level}`;
  }

  /**
   * Get a structural signature for concept extraction
   */
  private getStructuralSignature(pattern: HierarchyPattern): string {
    const ast = pattern.ast as unknown as { type: string };
    return `structure:${ast.type}`;
  }
}

// =============================================================================
// Factory Function
// =============================================================================

/**
 * Create a new HierarchyManager instance
 *
 * @param config - Configuration options
 * @returns A new HierarchyManager instance
 *
 * @example
 * ```typescript
 * const manager = createHierarchyManager({
 *   maxLevels: 4,
 *   promotionThreshold: 0.7,
 * });
 * ```
 */
export function createHierarchyManager(config: HierarchyManagerConfig = {}): HierarchyManager {
  return new DefaultHierarchyManager(config);
}
