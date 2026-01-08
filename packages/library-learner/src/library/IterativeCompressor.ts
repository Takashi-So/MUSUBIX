/**
 * IterativeCompressor - Iterative Pattern Compression
 * @module @nahisaho/musubix-library-learner
 * @see TSK-LL-103
 * @see DES-LL-103
 * @see REQ-LL-103 30%+ size reduction, 95% coverage retention
 */

import type { LearnedPattern, ConcretePattern } from '../types.js';

// ============================================================================
// Types
// ============================================================================

/**
 * IterativeCompressor configuration
 */
export interface IterativeCompressorConfig {
  /** Similarity threshold for merging (0-1, default: 0.75) */
  similarityThreshold: number;
  /** Minimum patterns to trigger compression (default: 100) */
  minPatterns: number;
  /** Target reduction ratio (default: 0.3 = 30%) */
  targetReduction: number;
  /** Maximum iterations for convergence */
  maxIterations: number;
}

/**
 * Compression result report
 */
export interface CompressionReport {
  /** Original pattern count */
  originalCount: number;
  /** Compressed pattern count */
  compressedCount: number;
  /** Merged groups info */
  mergedGroups: MergedGroup[];
  /** Coverage retained (0-1) */
  coverageRetained: number;
  /** Compression ratio achieved */
  compressionRatio: number;
  /** Compressed patterns */
  compressedPatterns: LearnedPattern[];
}

/**
 * Information about a merged group
 */
export interface MergedGroup {
  /** Merged pattern ID */
  mergedId: string;
  /** Source pattern IDs */
  sourceIds: string[];
  /** Similarity score */
  similarityScore: number;
}

/**
 * Compression statistics
 */
export interface CompressionStatistics {
  /** Total compression operations */
  totalCompressions: number;
  /** Average reduction achieved */
  averageReduction: number;
  /** Last compression timestamp */
  lastCompressionTime: Date | null;
}

/**
 * IterativeCompressor interface
 */
export interface IterativeCompressor {
  /**
   * Check if compression should be triggered
   */
  shouldCompress(patterns: LearnedPattern[]): boolean;

  /**
   * Compress patterns
   */
  compress(patterns: LearnedPattern[]): Promise<CompressionReport>;

  /**
   * Calculate similarity between two patterns
   */
  calculateSimilarity(p1: LearnedPattern, p2: LearnedPattern): number;

  /**
   * Merge similar patterns into one
   */
  mergePatterns(patterns: LearnedPattern[]): Promise<LearnedPattern>;

  /**
   * Get compression statistics
   */
  getStatistics(): CompressionStatistics;

  /**
   * Reset statistics
   */
  resetStatistics(): void;

  /**
   * Get current configuration
   */
  getConfig(): IterativeCompressorConfig;

  /**
   * Update configuration
   */
  updateConfig(config: Partial<IterativeCompressorConfig>): void;

  /**
   * Serialize to JSON
   */
  toJSON(): string;

  /**
   * Deserialize from JSON
   */
  fromJSON(json: string): void;
}

// ============================================================================
// Default Implementation
// ============================================================================

/**
 * Default IterativeCompressor implementation
 */
export class DefaultIterativeCompressor implements IterativeCompressor {
  private config: IterativeCompressorConfig;
  private statistics: CompressionStatistics;

  constructor(config?: Partial<IterativeCompressorConfig>) {
    this.config = {
      similarityThreshold: config?.similarityThreshold ?? 0.75,
      minPatterns: config?.minPatterns ?? 100,
      targetReduction: config?.targetReduction ?? 0.3,
      maxIterations: config?.maxIterations ?? 10,
    };

    this.statistics = {
      totalCompressions: 0,
      averageReduction: 0,
      lastCompressionTime: null,
    };
  }

  /**
   * Check if compression should be triggered
   */
  shouldCompress(patterns: LearnedPattern[]): boolean {
    return patterns.length >= this.config.minPatterns;
  }

  /**
   * Compress patterns using iterative merging
   */
  async compress(patterns: LearnedPattern[]): Promise<CompressionReport> {
    if (patterns.length === 0) {
      return {
        originalCount: 0,
        compressedCount: 0,
        mergedGroups: [],
        coverageRetained: 1.0,
        compressionRatio: 0,
        compressedPatterns: [],
      };
    }

    const originalCount = patterns.length;
    const mergedGroups: MergedGroup[] = [];
    let currentPatterns = [...patterns];

    // Iterative compression until target reached or convergence
    for (let iteration = 0; iteration < this.config.maxIterations; iteration++) {
      const { merged, groups } = await this.compressIteration(currentPatterns);

      if (groups.length === 0) {
        // No more merges possible
        break;
      }

      mergedGroups.push(...groups);
      currentPatterns = merged;

      // Check if target reduction achieved
      const currentReduction = 1 - currentPatterns.length / originalCount;
      if (currentReduction >= this.config.targetReduction) {
        break;
      }
    }

    // Calculate coverage (based on usage counts)
    const originalUsage = patterns.reduce((sum, p) => sum + p.usageCount, 0);
    const compressedUsage = currentPatterns.reduce(
      (sum, p) => sum + p.usageCount,
      0
    );
    const coverageRetained =
      originalUsage > 0 ? compressedUsage / originalUsage : 1.0;

    const compressionRatio = 1 - currentPatterns.length / originalCount;

    // Update statistics
    this.updateStatistics(compressionRatio);

    return {
      originalCount,
      compressedCount: currentPatterns.length,
      mergedGroups,
      coverageRetained: Math.min(coverageRetained, 1.0),
      compressionRatio,
      compressedPatterns: currentPatterns,
    };
  }

  /**
   * Single compression iteration
   */
  private async compressIteration(
    patterns: LearnedPattern[]
  ): Promise<{ merged: LearnedPattern[]; groups: MergedGroup[] }> {
    const clusters = this.findSimilarClusters(patterns);
    const groups: MergedGroup[] = [];
    const merged: LearnedPattern[] = [];
    const mergedIds = new Set<string>();

    // Merge each cluster
    for (const cluster of clusters) {
      if (cluster.length > 1) {
        const mergedPattern = await this.mergePatterns(cluster);
        merged.push(mergedPattern);

        groups.push({
          mergedId: mergedPattern.id,
          sourceIds: cluster.map((p) => p.id),
          similarityScore: this.calculateClusterSimilarity(cluster),
        });

        cluster.forEach((p) => mergedIds.add(p.id));
      }
    }

    // Add patterns that weren't merged
    for (const pattern of patterns) {
      if (!mergedIds.has(pattern.id)) {
        merged.push(pattern);
      }
    }

    return { merged, groups };
  }

  /**
   * Find clusters of similar patterns
   */
  private findSimilarClusters(patterns: LearnedPattern[]): LearnedPattern[][] {
    const clusters: LearnedPattern[][] = [];
    const used = new Set<string>();

    for (const pattern of patterns) {
      if (used.has(pattern.id)) continue;

      const cluster: LearnedPattern[] = [pattern];
      used.add(pattern.id);

      for (const other of patterns) {
        if (used.has(other.id)) continue;

        const similarity = this.calculateSimilarity(pattern, other);
        if (similarity >= this.config.similarityThreshold) {
          cluster.push(other);
          used.add(other.id);
        }
      }

      if (cluster.length > 1) {
        clusters.push(cluster);
      }
    }

    return clusters;
  }

  /**
   * Calculate similarity between two patterns
   */
  calculateSimilarity(p1: LearnedPattern, p2: LearnedPattern): number {
    if (p1.id === p2.id) return 1.0;

    let similarity = 0;
    let factors = 0;

    // Name similarity (Jaccard on words)
    const words1 = this.tokenizeName(p1.name);
    const words2 = this.tokenizeName(p2.name);
    const nameSimilarity = this.jaccardSimilarity(words1, words2);
    similarity += nameSimilarity * 0.3;
    factors += 0.3;

    // Tag similarity
    const tagSimilarity = this.jaccardSimilarity(
      new Set(p1.tags),
      new Set(p2.tags)
    );
    similarity += tagSimilarity * 0.2;
    factors += 0.2;

    // Level match bonus
    if (p1.level === p2.level) {
      similarity += 0.1;
    }
    factors += 0.1;

    // AST structure similarity (simplified)
    const astSimilarity = this.calculateASTSimilarity(p1, p2);
    similarity += astSimilarity * 0.4;
    factors += 0.4;

    return factors > 0 ? similarity / factors : 0;
  }

  /**
   * Tokenize pattern name into words
   */
  private tokenizeName(name: string): Set<string> {
    // Split on camelCase, PascalCase, snake_case, kebab-case
    const words = name
      .replace(/([a-z])([A-Z])/g, '$1 $2')
      .replace(/[_-]/g, ' ')
      .toLowerCase()
      .split(/\s+/)
      .filter((w) => w.length > 0);

    return new Set(words);
  }

  /**
   * Jaccard similarity between two sets
   */
  private jaccardSimilarity<T>(set1: Set<T>, set2: Set<T>): number {
    const intersection = new Set([...set1].filter((x) => set2.has(x)));
    const union = new Set([...set1, ...set2]);

    if (union.size === 0) return 0;
    return intersection.size / union.size;
  }

  /**
   * Calculate AST structure similarity
   */
  private calculateASTSimilarity(
    p1: LearnedPattern,
    p2: LearnedPattern
  ): number {
    const content1 = p1.content as ConcretePattern;
    const content2 = p2.content as ConcretePattern;

    if (!content1?.ast || !content2?.ast) return 0;

    // Simplified: compare AST type
    if (content1.ast.type === content2.ast.type) {
      return 0.8;
    }

    return 0.2;
  }

  /**
   * Calculate average similarity within a cluster
   */
  private calculateClusterSimilarity(cluster: LearnedPattern[]): number {
    if (cluster.length < 2) return 1.0;

    let totalSimilarity = 0;
    let count = 0;

    for (let i = 0; i < cluster.length; i++) {
      for (let j = i + 1; j < cluster.length; j++) {
        totalSimilarity += this.calculateSimilarity(cluster[i], cluster[j]);
        count++;
      }
    }

    return count > 0 ? totalSimilarity / count : 0;
  }

  /**
   * Merge similar patterns into one
   */
  async mergePatterns(patterns: LearnedPattern[]): Promise<LearnedPattern> {
    if (patterns.length === 0) {
      throw new Error('Cannot merge empty pattern array');
    }

    if (patterns.length === 1) {
      return patterns[0];
    }

    // Use the most confident pattern as base
    const sortedByConfidence = [...patterns].sort(
      (a, b) => b.confidence - a.confidence
    );
    const base = sortedByConfidence[0];

    // Aggregate usage counts
    const totalUsage = patterns.reduce((sum, p) => sum + p.usageCount, 0);

    // Combine tags
    const allTags = new Set<string>();
    patterns.forEach((p) => p.tags.forEach((t) => allTags.add(t)));

    // Create merged pattern
    const merged: LearnedPattern = {
      id: `MERGED-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`,
      name: this.generateMergedName(patterns),
      level: base.level,
      content: base.content,
      usageCount: totalUsage,
      confidence: base.confidence, // Keep highest confidence
      createdAt: new Date(),
      lastUsedAt: new Date(),
      tags: Array.from(allTags),
    };

    return merged;
  }

  /**
   * Generate a name for merged pattern
   */
  private generateMergedName(patterns: LearnedPattern[]): string {
    // Find common prefix
    const names = patterns.map((p) => p.name);
    const prefix = this.findCommonPrefix(names);

    if (prefix.length >= 3) {
      return `${prefix}*`;
    }

    return `Merged(${patterns.length})`;
  }

  /**
   * Find common prefix among strings
   */
  private findCommonPrefix(strings: string[]): string {
    if (strings.length === 0) return '';
    if (strings.length === 1) return strings[0];

    let prefix = '';
    const first = strings[0];

    for (let i = 0; i < first.length; i++) {
      const char = first[i];
      if (strings.every((s) => s[i] === char)) {
        prefix += char;
      } else {
        break;
      }
    }

    return prefix;
  }

  /**
   * Update statistics after compression
   */
  private updateStatistics(compressionRatio: number): void {
    const prevTotal = this.statistics.totalCompressions;
    const prevAvg = this.statistics.averageReduction;

    this.statistics.totalCompressions++;
    this.statistics.averageReduction =
      (prevAvg * prevTotal + compressionRatio) / (prevTotal + 1);
    this.statistics.lastCompressionTime = new Date();
  }

  /**
   * Get compression statistics
   */
  getStatistics(): CompressionStatistics {
    return { ...this.statistics };
  }

  /**
   * Reset statistics
   */
  resetStatistics(): void {
    this.statistics = {
      totalCompressions: 0,
      averageReduction: 0,
      lastCompressionTime: null,
    };
  }

  /**
   * Get current configuration
   */
  getConfig(): IterativeCompressorConfig {
    return { ...this.config };
  }

  /**
   * Update configuration
   */
  updateConfig(config: Partial<IterativeCompressorConfig>): void {
    this.config = { ...this.config, ...config };
  }

  /**
   * Serialize to JSON
   */
  toJSON(): string {
    return JSON.stringify({
      config: this.config,
      statistics: {
        ...this.statistics,
        lastCompressionTime: this.statistics.lastCompressionTime?.toISOString(),
      },
    });
  }

  /**
   * Deserialize from JSON
   */
  fromJSON(json: string): void {
    const data = JSON.parse(json);

    if (data.config) {
      this.config = { ...this.config, ...data.config };
    }

    if (data.statistics) {
      this.statistics = {
        totalCompressions: data.statistics.totalCompressions ?? 0,
        averageReduction: data.statistics.averageReduction ?? 0,
        lastCompressionTime: data.statistics.lastCompressionTime
          ? new Date(data.statistics.lastCompressionTime)
          : null,
      };
    }
  }
}

// ============================================================================
// Factory Function
// ============================================================================

/**
 * Create an IterativeCompressor instance
 * @param config - Optional configuration
 * @returns IterativeCompressor instance
 */
export function createIterativeCompressor(
  config?: Partial<IterativeCompressorConfig>
): IterativeCompressor {
  return new DefaultIterativeCompressor(config);
}
