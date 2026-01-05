/**
 * @fileoverview Sleep phase for pattern consolidation and abstraction
 * @traceability TSK-WAKE-002, REQ-WAKE-001-F002
 */

import type { ConsolidationInput, SleepResult, AbstractedPattern, PatternCandidate } from '../types.js';

/**
 * Sleep phase executor
 * 
 * @description
 * Consolidates and abstracts patterns during the sleep phase.
 * - Groups similar patterns
 * - Creates higher-level abstractions
 * - Prunes low-value patterns
 * - Optimizes using MDL principle
 */
export class SleepPhase {
  private mdlThreshold: number;
  private minFrequency: number;

  constructor(options: { mdlThreshold?: number; minFrequency?: number } = {}) {
    this.mdlThreshold = options.mdlThreshold ?? 0.5;
    this.minFrequency = options.minFrequency ?? 2;
  }

  /**
   * Run consolidation on collected patterns
   */
  async consolidate(input: ConsolidationInput): Promise<SleepResult> {
    const { patterns, existingLibrary: _existingLibrary } = input;

    // Get frequency from patterns (use occurrences if frequency not set)
    const getFrequency = (p: PatternCandidate): number => p.frequency ?? p.occurrences ?? 1;

    // Filter by frequency
    const frequentPatterns = patterns.filter(p => getFrequency(p) >= this.minFrequency);

    // Group similar patterns for abstraction
    const groups = this.groupSimilarPatterns(frequentPatterns);

    // Abstract each group
    const abstracted: AbstractedPattern[] = [];
    for (const group of groups) {
      if (group.length > 1) {
        const abstractedPattern = this.abstractGroup(group);
        if (abstractedPattern) {
          abstracted.push(abstractedPattern);
        }
      }
    }

    // Calculate MDL score
    const mdlScore = this.calculateMDL(abstracted, frequentPatterns);

    // Determine which patterns to keep and which to prune
    const getPatternId = (p: PatternCandidate): string => p.id ?? p.name;
    const consolidated = frequentPatterns.map(p => getPatternId(p));
    const pruned = patterns
      .filter(p => getFrequency(p) < this.minFrequency)
      .map(p => getPatternId(p));

    return {
      consolidatedPatterns: consolidated,
      abstractedPatterns: abstracted,
      prunedPatterns: pruned,
      mdlScore,
    };
  }

  /**
   * Group similar patterns together
   */
  private groupSimilarPatterns(patterns: PatternCandidate[]): PatternCandidate[][] {
    // Group by source type first
    const bySource = new Map<string, PatternCandidate[]>();
    for (const p of patterns) {
      const source = p.source ?? 'unknown';
      if (!bySource.has(source)) {
        bySource.set(source, []);
      }
      bySource.get(source)!.push(p);
    }

    // Return groups
    return Array.from(bySource.values());
  }

  /**
   * Abstract a group of similar patterns into one
   */
  private abstractGroup(group: PatternCandidate[]): AbstractedPattern | null {
    if (group.length < 2) return null;

    const getPatternId = (p: PatternCandidate): string => p.id ?? p.name;
    const getPatternCode = (p: PatternCandidate): string => 
      p.code ?? JSON.stringify(p.structure);

    // Create abstracted pattern
    return {
      id: `abstract-${Date.now()}`,
      originalPatterns: group.map(p => getPatternId(p)),
      abstractedCode: getPatternCode(group[0]),
      compressionRatio: group.length,
    };
  }

  /**
   * Calculate Minimum Description Length score
   */
  private calculateMDL(abstracted: AbstractedPattern[], patterns: PatternCandidate[]): number {
    // MDL = Description of library + Description of data given library
    // Lower is better
    const librarySize = abstracted.reduce((sum, a) => sum + a.abstractedCode.length, 0);
    const getFrequency = (p: PatternCandidate): number => p.frequency ?? p.occurrences ?? 1;
    const getPatternCode = (p: PatternCandidate): string => 
      p.code ?? JSON.stringify(p.structure);
    const dataSize = patterns.reduce((sum, p) => sum + getPatternCode(p).length / getFrequency(p), 0);
    const rawScore = librarySize + dataSize;
    
    // Apply threshold normalization
    return rawScore * this.mdlThreshold;
  }
}
