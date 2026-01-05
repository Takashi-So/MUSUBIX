/**
 * @fileoverview Wake-Sleep Cycle Learning System
 * @traceability TSK-WAKE-002, REQ-PATTERN-003
 * 
 * Implements DreamCoder-style wake-sleep learning:
 * - Wake Phase: Extract patterns from observed code
 * - Sleep Phase: Compress and optimize pattern library
 */

import type { Pattern, ASTNode } from '../types.js';
import { PatternCompressor } from '../compression/pattern-compressor.js';
import { PatternQualityEvaluator, type PatternQuality } from '../compression/quality-evaluator.js';

/**
 * Configuration for wake-sleep cycle
 */
export interface WakeSleepConfig {
  /** Minimum quality score to keep pattern */
  minQualityThreshold: number;
  /** Maximum patterns in library */
  maxLibrarySize: number;
  /** Compression iterations per sleep cycle */
  compressionIterations: number;
  /** Whether to enable automatic cycling */
  autoSleep: boolean;
  /** Wake observations before triggering auto sleep */
  wakeThreshold: number;
}

/**
 * Wake phase observation
 */
export interface WakeObservation {
  ast: ASTNode;
  source: string;
  context: {
    language: string;
    filename?: string;
    domain?: string;
  };
  timestamp: string;
}

/**
 * Sleep cycle result
 */
export interface SleepResult {
  patternsConsolidated: number;
  patternsRemoved: number;
  compressionRatio: number;
  mdlImprovement: number;
  cycleTimeMs: number;
}

/**
 * Wake-Sleep learning statistics
 */
export interface LearningStats {
  totalWakeObservations: number;
  totalSleepCycles: number;
  currentLibrarySize: number;
  averagePatternQuality: number;
  totalPatternsExtracted: number;
  totalPatternsRemoved: number;
}

/**
 * Pattern with quality metadata
 */
interface EnhancedPattern extends Pattern {
  quality?: PatternQuality;
  lastUsed: string;
  extractionSource?: string;
}

/**
 * Wake-Sleep Cycle Learning System
 * 
 * Implements alternating wake and sleep phases for continuous learning:
 * 
 * Wake Phase:
 * - Observe new code/patterns
 * - Extract potential patterns
 * - Add to candidate pool
 * 
 * Sleep Phase:
 * - Compress pattern library using MDL
 * - Remove low-quality patterns
 * - Merge similar patterns
 * - Optimize for generality/utility balance
 */
export class WakeSleepCycle {
  private config: WakeSleepConfig;
  private compressor: PatternCompressor;
  private evaluator: PatternQualityEvaluator;
  private library: Map<string, EnhancedPattern> = new Map();
  private wakeBuffer: WakeObservation[] = [];
  private stats: LearningStats;

  constructor(config?: Partial<WakeSleepConfig>) {
    this.config = {
      minQualityThreshold: config?.minQualityThreshold ?? 0.3,
      maxLibrarySize: config?.maxLibrarySize ?? 1000,
      compressionIterations: config?.compressionIterations ?? 3,
      autoSleep: config?.autoSleep ?? true,
      wakeThreshold: config?.wakeThreshold ?? 100,
    };

    this.compressor = new PatternCompressor({
      minCompressionRatio: 1.1,
    });

    this.evaluator = new PatternQualityEvaluator({
      minFrequency: 2,
      maxHoles: 5,
      idealDepthRange: [3, 8],
    });

    this.stats = {
      totalWakeObservations: 0,
      totalSleepCycles: 0,
      currentLibrarySize: 0,
      averagePatternQuality: 0,
      totalPatternsExtracted: 0,
      totalPatternsRemoved: 0,
    };
  }

  /**
   * Wake Phase: Observe new code and extract patterns
   */
  wake(observation: WakeObservation): Pattern[] {
    this.wakeBuffer.push(observation);
    this.stats.totalWakeObservations++;

    // Simple pattern extraction from observation
    const patterns = this.extractPatternsFromAST(observation);

    // Add to library candidates
    for (const pattern of patterns) {
      this.addToLibrary(pattern);
    }

    // Auto-trigger sleep if threshold reached
    if (this.config.autoSleep && this.wakeBuffer.length >= this.config.wakeThreshold) {
      this.sleep();
    }

    return patterns;
  }

  /**
   * Sleep Phase: Consolidate and optimize pattern library
   */
  sleep(): SleepResult {
    const startTime = Date.now();
    const initialSize = this.library.size;
    let patternsRemoved = 0;

    // Get all patterns
    const patterns = Array.from(this.library.values());

    // Calculate initial MDL
    const allAsts = this.wakeBuffer.map(o => o.ast);
    const initialMDLResult = allAsts.length > 0
      ? this.compressor.calculateMDL(patterns, allAsts)
      : null;
    const initialMDL = initialMDLResult?.total ?? this.estimateLibraryMDL(patterns);

    // Phase 1: Quality filtering
    const qualityFiltered = this.evaluator.filterByQuality(
      patterns,
      this.config.minQualityThreshold
    );
    patternsRemoved += patterns.length - qualityFiltered.length;

    // Phase 2: MDL-based compression
    let compressed = qualityFiltered;
    for (let i = 0; i < this.config.compressionIterations; i++) {
      const beforeCompression = compressed.length;
      compressed = this.compressor.compressLibrary(compressed);
      if (compressed.length >= beforeCompression) break; // No improvement
    }
    patternsRemoved += qualityFiltered.length - compressed.length;

    // Phase 3: Size limiting
    if (compressed.length > this.config.maxLibrarySize) {
      const ranked = this.evaluator.rankPatterns(compressed);
      compressed = ranked.slice(0, this.config.maxLibrarySize).map(r => r.pattern);
      patternsRemoved += ranked.length - this.config.maxLibrarySize;
    }

    // Update library
    this.library.clear();
    for (const pattern of compressed) {
      const enhanced = pattern as EnhancedPattern;
      enhanced.quality = this.evaluator.evaluate(pattern);
      enhanced.lastUsed = new Date().toISOString();
      this.library.set(pattern.id, enhanced);
    }

    // Calculate final MDL
    const finalMDLResult = allAsts.length > 0
      ? this.compressor.calculateMDL(compressed, allAsts)
      : null;
    const finalMDL = finalMDLResult?.total ?? this.estimateLibraryMDL(compressed);

    // Update stats
    this.stats.totalSleepCycles++;
    this.stats.currentLibrarySize = this.library.size;
    this.stats.totalPatternsRemoved += patternsRemoved;
    this.updateAverageQuality();

    // Clear wake buffer
    this.wakeBuffer = [];

    return {
      patternsConsolidated: initialSize - patternsRemoved,
      patternsRemoved,
      compressionRatio: initialSize > 0 ? this.library.size / initialSize : 1,
      mdlImprovement: initialMDL > 0 ? (initialMDL - finalMDL) / initialMDL : 0,
      cycleTimeMs: Date.now() - startTime,
    };
  }

  /**
   * Extract patterns from AST
   */
  private extractPatternsFromAST(observation: WakeObservation): Pattern[] {
    const patterns: Pattern[] = [];
    const seen = new Set<string>();

    // Traverse AST and extract subtrees as pattern candidates
    const traverse = (node: ASTNode, depth: number): void => {
      // Only extract patterns of reasonable depth
      if (depth >= 2 && depth <= 6) {
        const key = this.getPatternKey(node);
        if (!seen.has(key)) {
          seen.add(key);

          const pattern: Pattern = {
            id: `WP-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`,
            name: `${node.type}_pattern`,
            language: observation.context.language,
            ast: node,
            holes: [],
            frequency: 1,
            createdAt: observation.timestamp,
            updatedAt: observation.timestamp,
          };

          patterns.push(pattern);
          this.stats.totalPatternsExtracted++;
        }
      }

      // Recurse into children
      for (const child of node.children) {
        traverse(child, depth + 1);
      }
    };

    traverse(observation.ast, 0);
    return patterns;
  }

  /**
   * Add pattern to library (or update existing)
   */
  private addToLibrary(pattern: Pattern): void {
    const key = this.getPatternKey(pattern.ast);
    const existing = this.findSimilarPattern(key);

    if (existing) {
      // Update existing pattern
      existing.frequency = (existing.frequency ?? 0) + 1;
      existing.lastUsed = new Date().toISOString();
      existing.updatedAt = new Date().toISOString();
    } else {
      // Add new pattern
      const enhanced: EnhancedPattern = {
        ...pattern,
        lastUsed: new Date().toISOString(),
      };
      this.library.set(pattern.id, enhanced);
    }
  }

  /**
   * Find similar pattern in library
   */
  private findSimilarPattern(key: string): EnhancedPattern | undefined {
    for (const pattern of this.library.values()) {
      if (this.getPatternKey(pattern.ast) === key) {
        return pattern;
      }
    }
    return undefined;
  }

  /**
   * Generate key for pattern deduplication
   */
  private getPatternKey(ast: ASTNode): string {
    const parts: string[] = [];

    const traverse = (node: ASTNode): void => {
      parts.push(node.type);
      if (node.type === 'Hole') {
        parts.push('?');
      } else if (node.value) {
        parts.push(node.value.slice(0, 20));
      }
      for (const child of node.children) {
        traverse(child);
      }
    };

    traverse(ast);
    return parts.join('|');
  }

  /**
   * Estimate MDL for library without data
   */
  private estimateLibraryMDL(patterns: Pattern[]): number {
    return patterns.reduce((sum, p) => {
      return sum + this.countNodes(p.ast) + p.holes.length * 2;
    }, 0);
  }

  /**
   * Count nodes in AST
   */
  private countNodes(ast: ASTNode): number {
    return 1 + ast.children.reduce((sum, child) => sum + this.countNodes(child), 0);
  }

  /**
   * Update average quality statistic
   */
  private updateAverageQuality(): void {
    const patterns = Array.from(this.library.values());
    if (patterns.length === 0) {
      this.stats.averagePatternQuality = 0;
      return;
    }

    const totalQuality = patterns.reduce((sum, p) => {
      return sum + (p.quality?.score ?? 0);
    }, 0);

    this.stats.averagePatternQuality = totalQuality / patterns.length;
  }

  /**
   * Get current pattern library
   */
  getLibrary(): Pattern[] {
    return Array.from(this.library.values());
  }

  /**
   * Get learning statistics
   */
  getStats(): LearningStats {
    return { ...this.stats };
  }

  /**
   * Get pattern by ID
   */
  getPattern(id: string): Pattern | undefined {
    return this.library.get(id);
  }

  /**
   * Clear library and reset stats
   */
  reset(): void {
    this.library.clear();
    this.wakeBuffer = [];
    this.stats = {
      totalWakeObservations: 0,
      totalSleepCycles: 0,
      currentLibrarySize: 0,
      averagePatternQuality: 0,
      totalPatternsExtracted: 0,
      totalPatternsRemoved: 0,
    };
  }

  /**
   * Export library to JSON
   */
  exportLibrary(): string {
    return JSON.stringify({
      patterns: Array.from(this.library.values()),
      stats: this.stats,
      exportedAt: new Date().toISOString(),
    }, null, 2);
  }

  /**
   * Import library from JSON
   */
  importLibrary(json: string): number {
    const data = JSON.parse(json);
    let imported = 0;

    for (const pattern of data.patterns ?? []) {
      if (pattern.id && pattern.ast) {
        this.library.set(pattern.id, pattern as EnhancedPattern);
        imported++;
      }
    }

    this.stats.currentLibrarySize = this.library.size;
    return imported;
  }
}
