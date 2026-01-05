/**
 * @fileoverview Sleep Phase Implementation for YATA Local
 * @module @nahisaho/yata-local/wake-sleep
 * @version 0.1.0
 * @license MIT
 * 
 * Trace: REQ-WSL-002, TSK-WSL-002
 */

import { randomUUID } from 'crypto';
import type {
  LocalPatternCandidate,
  LocalPatternCluster,
  LocalConsolidatedPattern,
  SleepClusterOptions,
  SleepClusterResult,
  SimilarityMethod,
} from './types.js';

/**
 * Sleep Phase - Pattern Clustering and Consolidation
 * 
 * Responsible for:
 * - Clustering similar patterns
 * - Selecting representative patterns
 * - Confidence management (update/decay)
 */
export class LocalSleepPhase {
  private readonly options: Required<SleepClusterOptions>;
  private readonly similarityMethod: SimilarityMethod;

  constructor(
    options: Partial<SleepClusterOptions> = {},
    similarityMethod: SimilarityMethod = 'jaccard'
  ) {
    this.options = {
      similarityThreshold: options.similarityThreshold ?? 0.8,
      minClusterSize: options.minClusterSize ?? 2,
      maxClusters: options.maxClusters ?? 100,
    };
    this.similarityMethod = similarityMethod;
  }

  /**
   * Cluster similar pattern candidates
   */
  async cluster(candidates: LocalPatternCandidate[]): Promise<SleepClusterResult> {
    const startTime = Date.now();
    const clusters: LocalPatternCluster[] = [];
    const unclustered: LocalPatternCandidate[] = [];
    const assigned = new Set<string>();

    // Sort by confidence (higher first)
    const sorted = [...candidates].sort((a, b) => b.confidence - a.confidence);

    for (const candidate of sorted) {
      if (assigned.has(candidate.tempId)) continue;

      // Try to find or create a cluster
      let foundCluster = false;

      for (const cluster of clusters) {
        const similarity = this.calculateSimilarity(
          candidate.signature,
          cluster.centroid
        );

        if (similarity >= this.options.similarityThreshold) {
          // Add to existing cluster
          cluster.patterns.push(candidate);
          cluster.avgSimilarity = this.recalculateAvgSimilarity(cluster);
          cluster.totalOccurrences++;
          assigned.add(candidate.tempId);
          foundCluster = true;
          break;
        }
      }

      if (!foundCluster && clusters.length < this.options.maxClusters) {
        // Create new cluster with this candidate as seed
        const newCluster: LocalPatternCluster = {
          clusterId: `CLUST-${Date.now()}-${randomUUID().substring(0, 8)}`,
          patterns: [candidate],
          representative: candidate,
          avgSimilarity: 1.0,
          centroid: candidate.signature,
          totalOccurrences: 1,
        };
        clusters.push(newCluster);
        assigned.add(candidate.tempId);
      } else if (!foundCluster) {
        unclustered.push(candidate);
      }
    }

    // Select representatives for each cluster
    for (const cluster of clusters) {
      cluster.representative = this.selectRepresentative(cluster);
      cluster.centroid = this.computeCentroid(cluster);
    }

    // Filter clusters by minimum size
    const validClusters = clusters.filter(
      c => c.patterns.length >= this.options.minClusterSize
    );
    
    // Add patterns from small clusters to unclustered
    for (const cluster of clusters) {
      if (cluster.patterns.length < this.options.minClusterSize) {
        unclustered.push(...cluster.patterns);
      }
    }

    return {
      clusters: validClusters,
      unclustered,
      stats: {
        totalPatterns: candidates.length,
        clusteredPatterns: validClusters.reduce((sum, c) => sum + c.patterns.length, 0),
        unclusteredPatterns: unclustered.length,
        clustersFormed: validClusters.length,
        avgClusterSize: validClusters.length > 0
          ? validClusters.reduce((sum, c) => sum + c.patterns.length, 0) / validClusters.length
          : 0,
        processingTimeMs: Date.now() - startTime,
      },
    };
  }

  /**
   * Select the representative pattern from a cluster
   */
  selectRepresentative(cluster: LocalPatternCluster): LocalPatternCandidate {
    // Score each pattern
    const scored = cluster.patterns.map(pattern => ({
      pattern,
      score: this.scorePattern(pattern, cluster),
    }));

    // Sort by score (higher is better)
    scored.sort((a, b) => b.score - a.score);

    return scored[0]?.pattern ?? cluster.patterns[0];
  }

  /**
   * Update confidence for a pattern based on usage
   */
  updateConfidence(
    pattern: LocalConsolidatedPattern,
    used: boolean
  ): LocalConsolidatedPattern {
    const now = new Date();
    
    if (used) {
      // Increase confidence and update usage
      return {
        ...pattern,
        confidence: Math.min(1.0, pattern.confidence + 0.05),
        usageCount: pattern.usageCount + 1,
        lastUsedAt: now,
      };
    }

    return pattern;
  }

  /**
   * Decay confidence for unused patterns
   */
  decay(
    pattern: LocalConsolidatedPattern,
    decayRate: number = 0.01
  ): LocalConsolidatedPattern {
    const now = new Date();
    const lastUsed = pattern.lastUsedAt ?? pattern.createdAt;
    const daysSinceUse = Math.floor(
      (now.getTime() - lastUsed.getTime()) / (1000 * 60 * 60 * 24)
    );

    // Decay based on days since last use
    const decayFactor = Math.pow(1 - decayRate, daysSinceUse);
    const newConfidence = pattern.confidence * decayFactor;

    return {
      ...pattern,
      confidence: Math.max(0.0, newConfidence),
    };
  }

  /**
   * Calculate similarity between two signatures
   */
  calculateSimilarity(sig1: string, sig2: string): number {
    switch (this.similarityMethod) {
      case 'jaccard':
        return this.jaccardSimilarity(sig1, sig2);
      case 'cosine':
        return this.cosineSimilarity(sig1, sig2);
      case 'levenshtein':
        return this.levenshteinSimilarity(sig1, sig2);
      case 'ast':
        return this.astSimilarity(sig1, sig2);
      default:
        return this.jaccardSimilarity(sig1, sig2);
    }
  }

  /**
   * Jaccard similarity coefficient
   */
  private jaccardSimilarity(a: string, b: string): number {
    const tokensA = new Set(a.split('|'));
    const tokensB = new Set(b.split('|'));

    const intersection = new Set([...tokensA].filter(x => tokensB.has(x)));
    const union = new Set([...tokensA, ...tokensB]);

    if (union.size === 0) return 0;
    return intersection.size / union.size;
  }

  /**
   * Cosine similarity (token-based)
   */
  private cosineSimilarity(a: string, b: string): number {
    const tokensA = a.split('|');
    const tokensB = b.split('|');

    // Build vocabulary
    const vocab = new Set([...tokensA, ...tokensB]);
    
    // Create frequency vectors
    const vectorA = new Map<string, number>();
    const vectorB = new Map<string, number>();

    for (const token of tokensA) {
      vectorA.set(token, (vectorA.get(token) ?? 0) + 1);
    }
    for (const token of tokensB) {
      vectorB.set(token, (vectorB.get(token) ?? 0) + 1);
    }

    // Calculate dot product and magnitudes
    let dotProduct = 0;
    let magA = 0;
    let magB = 0;

    for (const token of vocab) {
      const a = vectorA.get(token) ?? 0;
      const b = vectorB.get(token) ?? 0;
      dotProduct += a * b;
      magA += a * a;
      magB += b * b;
    }

    const magnitude = Math.sqrt(magA) * Math.sqrt(magB);
    if (magnitude === 0) return 0;

    return dotProduct / magnitude;
  }

  /**
   * Levenshtein-based similarity
   */
  private levenshteinSimilarity(a: string, b: string): number {
    const distance = this.levenshteinDistance(a, b);
    const maxLen = Math.max(a.length, b.length);
    if (maxLen === 0) return 1;
    return 1 - distance / maxLen;
  }

  /**
   * Levenshtein edit distance
   */
  private levenshteinDistance(a: string, b: string): number {
    const matrix: number[][] = [];

    for (let i = 0; i <= b.length; i++) {
      matrix[i] = [i];
    }
    for (let j = 0; j <= a.length; j++) {
      matrix[0][j] = j;
    }

    for (let i = 1; i <= b.length; i++) {
      for (let j = 1; j <= a.length; j++) {
        if (b.charAt(i - 1) === a.charAt(j - 1)) {
          matrix[i][j] = matrix[i - 1][j - 1];
        } else {
          matrix[i][j] = Math.min(
            matrix[i - 1][j - 1] + 1, // substitution
            matrix[i][j - 1] + 1, // insertion
            matrix[i - 1][j] + 1 // deletion
          );
        }
      }
    }

    return matrix[b.length][a.length];
  }

  /**
   * AST-based similarity (simplified)
   */
  private astSimilarity(a: string, b: string): number {
    // For now, use Jaccard with structure-aware parsing
    const structA = a.split(':');
    const structB = b.split(':');

    // Check type match first
    if (structA[0] !== structB[0]) {
      return 0; // Different types are never similar
    }

    // Compare token parts
    const tokensA = structA[1]?.split('|') ?? [];
    const tokensB = structB[1]?.split('|') ?? [];

    return this.jaccardSimilarity(tokensA.join('|'), tokensB.join('|'));
  }

  /**
   * Score a pattern for representative selection
   */
  private scorePattern(
    pattern: LocalPatternCandidate,
    cluster: LocalPatternCluster
  ): number {
    let score = pattern.confidence;

    // Bonus for documentation
    if (pattern.content.includes('/**') || pattern.content.includes('* @')) {
      score += 0.2;
    }

    // Bonus for type annotations
    if (pattern.content.includes(': ') || pattern.content.includes('<')) {
      score += 0.1;
    }

    // Penalty for very short patterns
    if (pattern.content.split('\n').length < 3) {
      score -= 0.1;
    }

    // Penalty for very long patterns
    if (pattern.content.split('\n').length > 100) {
      score -= 0.2;
    }

    // Similarity to cluster centroid
    const simToCentroid = this.calculateSimilarity(
      pattern.signature,
      cluster.centroid
    );
    score += simToCentroid * 0.2;

    return score;
  }

  /**
   * Compute cluster centroid
   */
  private computeCentroid(cluster: LocalPatternCluster): string {
    // Use the most common tokens as centroid
    const tokenCounts = new Map<string, number>();

    for (const pattern of cluster.patterns) {
      const tokens = pattern.signature.split('|');
      for (const token of tokens) {
        tokenCounts.set(token, (tokenCounts.get(token) ?? 0) + 1);
      }
    }

    // Get tokens that appear in majority of patterns
    const threshold = cluster.patterns.length / 2;
    const centroidTokens = [...tokenCounts.entries()]
      .filter(([_, count]) => count >= threshold)
      .map(([token]) => token);

    // Preserve type prefix
    const type = cluster.patterns[0].type;
    return `${type}:${centroidTokens.join('|')}`;
  }

  /**
   * Recalculate average similarity within a cluster
   */
  private recalculateAvgSimilarity(cluster: LocalPatternCluster): number {
    if (cluster.patterns.length <= 1) return 1.0;

    let totalSimilarity = 0;
    let count = 0;

    for (let i = 0; i < cluster.patterns.length; i++) {
      for (let j = i + 1; j < cluster.patterns.length; j++) {
        totalSimilarity += this.calculateSimilarity(
          cluster.patterns[i].signature,
          cluster.patterns[j].signature
        );
        count++;
      }
    }

    return count > 0 ? totalSimilarity / count : 1.0;
  }
}

/**
 * Factory function to create a LocalSleepPhase instance
 */
export function createLocalSleepPhase(
  options?: Partial<SleepClusterOptions>,
  similarityMethod?: SimilarityMethod
): LocalSleepPhase {
  return new LocalSleepPhase(options, similarityMethod);
}
