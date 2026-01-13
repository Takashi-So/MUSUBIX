/**
 * Pattern Merger
 *
 * Merges and deduplicates extracted patterns
 *
 * @packageDocumentation
 * @module cli/generators/pattern-merger
 *
 * @traceability REQ-PTN-003, REQ-PTN-004
 * @see DES-PTN-002 - Pattern Merger Design
 */

import type { ExtractedPattern } from './pattern-extractor.js';

/**
 * Merged pattern result
 */
export interface MergedPattern extends ExtractedPattern {
  /** Merge metadata */
  mergeInfo: {
    /** Source pattern IDs that were merged */
    sourcePatternIds: string[];

    /** Number of times this pattern was seen */
    occurrences: number;

    /** Average confidence across merged patterns */
    averageConfidence: number;

    /** Merge timestamp */
    mergedAt: string;
  };
}

/**
 * Pattern merge result
 */
export interface MergeResult {
  /** Merged patterns */
  patterns: MergedPattern[];

  /** Merge statistics */
  stats: {
    /** Total input patterns */
    inputCount: number;

    /** Output pattern count */
    outputCount: number;

    /** Patterns merged */
    mergedCount: number;

    /** Deduplication ratio */
    deduplicationRatio: number;
  };
}

/**
 * Pattern merger configuration
 */
export interface PatternMergerConfig {
  /** Similarity threshold for merging (0-1) */
  similarityThreshold?: number;

  /** Minimum occurrences to keep pattern */
  minOccurrences?: number;

  /** Strategy for resolving conflicts */
  conflictStrategy?: 'newest' | 'highest-confidence' | 'most-occurrences';
}

/**
 * Pattern Merger
 *
 * Combines similar patterns and removes duplicates
 */
export class PatternMerger {
  constructor(private config: PatternMergerConfig = {}) {
    this.config = {
      similarityThreshold: 0.8,
      minOccurrences: 1,
      conflictStrategy: 'highest-confidence',
      ...config,
    };
  }

  /**
   * Merge patterns
   */
  merge(patterns: ExtractedPattern[]): MergeResult {
    if (patterns.length === 0) {
      return {
        patterns: [],
        stats: {
          inputCount: 0,
          outputCount: 0,
          mergedCount: 0,
          deduplicationRatio: 1,
        },
      };
    }

    // Group patterns by category
    const byCategory = this.groupByCategory(patterns);

    // Merge within each category
    const merged: MergedPattern[] = [];
    let totalMerged = 0;

    for (const [_category, categoryPatterns] of Object.entries(byCategory)) {
      const { patterns: mergedPatterns, mergedCount } = this.mergeCategory(categoryPatterns);
      merged.push(...mergedPatterns);
      totalMerged += mergedCount;
    }

    // Filter by minimum occurrences
    const filtered = merged.filter(
      (p) => p.mergeInfo.occurrences >= (this.config.minOccurrences ?? 1)
    );

    return {
      patterns: filtered,
      stats: {
        inputCount: patterns.length,
        outputCount: filtered.length,
        mergedCount: totalMerged,
        deduplicationRatio: patterns.length > 0 ? filtered.length / patterns.length : 1,
      },
    };
  }

  /**
   * Group patterns by category
   */
  private groupByCategory(patterns: ExtractedPattern[]): Record<string, ExtractedPattern[]> {
    const groups: Record<string, ExtractedPattern[]> = {};

    for (const pattern of patterns) {
      if (!groups[pattern.category]) {
        groups[pattern.category] = [];
      }
      groups[pattern.category].push(pattern);
    }

    return groups;
  }

  /**
   * Merge patterns within a category
   */
  private mergeCategory(patterns: ExtractedPattern[]): {
    patterns: MergedPattern[];
    mergedCount: number;
  } {
    const merged: MergedPattern[] = [];
    const used = new Set<number>();
    let mergedCount = 0;

    for (let i = 0; i < patterns.length; i++) {
      if (used.has(i)) continue;

      const pattern = patterns[i];
      const similar: ExtractedPattern[] = [pattern];
      used.add(i);

      // Find similar patterns
      for (let j = i + 1; j < patterns.length; j++) {
        if (used.has(j)) continue;

        const similarity = this.calculateSimilarity(pattern, patterns[j]);
        if (similarity >= (this.config.similarityThreshold ?? 0.8)) {
          similar.push(patterns[j]);
          used.add(j);
          mergedCount++;
        }
      }

      // Merge similar patterns
      const mergedPattern = this.mergePatterns(similar);
      merged.push(mergedPattern);
    }

    return { patterns: merged, mergedCount };
  }

  /**
   * Calculate similarity between two patterns
   */
  private calculateSimilarity(a: ExtractedPattern, b: ExtractedPattern): number {
    let score = 0;
    let weights = 0;

    // Category match (high weight)
    if (a.category === b.category) {
      score += 0.3;
    }
    weights += 0.3;

    // Name similarity
    const nameSimilarity = this.stringSimilarity(a.name, b.name);
    score += nameSimilarity * 0.3;
    weights += 0.3;

    // Template similarity
    const templateSimilarity = this.stringSimilarity(a.template, b.template);
    score += templateSimilarity * 0.3;
    weights += 0.3;

    // Variable count similarity
    const varCountDiff = Math.abs(a.variables.length - b.variables.length);
    const varScore = Math.max(0, 1 - varCountDiff / 5);
    score += varScore * 0.1;
    weights += 0.1;

    return score / weights;
  }

  /**
   * Calculate string similarity (simple Jaccard-like)
   */
  private stringSimilarity(a: string, b: string): number {
    const wordsA = new Set(a.toLowerCase().split(/\W+/).filter((w) => w.length > 2));
    const wordsB = new Set(b.toLowerCase().split(/\W+/).filter((w) => w.length > 2));

    if (wordsA.size === 0 && wordsB.size === 0) return 1;
    if (wordsA.size === 0 || wordsB.size === 0) return 0;

    const intersection = new Set([...wordsA].filter((x) => wordsB.has(x)));
    const union = new Set([...wordsA, ...wordsB]);

    return intersection.size / union.size;
  }

  /**
   * Merge multiple patterns into one
   */
  private mergePatterns(patterns: ExtractedPattern[]): MergedPattern {
    // Select best pattern based on strategy
    const best = this.selectBestPattern(patterns);

    // Calculate average confidence
    const avgConfidence =
      patterns.reduce((sum, p) => sum + p.metadata.confidence, 0) / patterns.length;

    // Collect all examples
    const allExamples = [...new Set(patterns.flatMap((p) => p.examples))].slice(0, 5);

    // Merge variables
    const mergedVariables = this.mergeVariables(patterns.flatMap((p) => p.variables));

    return {
      ...best,
      metadata: {
        ...best.metadata,
        confidence: avgConfidence,
      },
      variables: mergedVariables,
      examples: allExamples,
      mergeInfo: {
        sourcePatternIds: patterns.map((p) => p.id),
        occurrences: patterns.length,
        averageConfidence: avgConfidence,
        mergedAt: new Date().toISOString(),
      },
    };
  }

  /**
   * Select best pattern based on conflict strategy
   */
  private selectBestPattern(patterns: ExtractedPattern[]): ExtractedPattern {
    switch (this.config.conflictStrategy) {
      case 'newest':
        return patterns.sort(
          (a, b) =>
            new Date(b.metadata.extractedAt).getTime() - new Date(a.metadata.extractedAt).getTime()
        )[0];

      case 'most-occurrences':
        // For initial merge, just use the first one
        return patterns[0];

      case 'highest-confidence':
      default:
        return patterns.sort((a, b) => b.metadata.confidence - a.metadata.confidence)[0];
    }
  }

  /**
   * Merge variables from multiple patterns
   */
  private mergeVariables(variables: ExtractedPattern['variables']): ExtractedPattern['variables'] {
    const byName = new Map<string, ExtractedPattern['variables'][0]>();

    for (const variable of variables) {
      const existing = byName.get(variable.name);
      if (!existing || variable.required) {
        byName.set(variable.name, variable);
      }
    }

    return Array.from(byName.values());
  }

  /**
   * Find duplicate patterns
   */
  findDuplicates(patterns: ExtractedPattern[]): Array<[ExtractedPattern, ExtractedPattern]> {
    const duplicates: Array<[ExtractedPattern, ExtractedPattern]> = [];

    for (let i = 0; i < patterns.length; i++) {
      for (let j = i + 1; j < patterns.length; j++) {
        const similarity = this.calculateSimilarity(patterns[i], patterns[j]);
        if (similarity >= (this.config.similarityThreshold ?? 0.8)) {
          duplicates.push([patterns[i], patterns[j]]);
        }
      }
    }

    return duplicates;
  }
}

/**
 * Create a new pattern merger
 */
export function createPatternMerger(config?: PatternMergerConfig): PatternMerger {
  return new PatternMerger(config);
}
