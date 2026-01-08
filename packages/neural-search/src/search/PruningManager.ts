/**
 * Pruning Manager
 * @module @nahisaho/musubix-neural-search
 * @description Learning-based pruning for search
 * Traces to: REQ-NS-003 (学習ベースプルーニング)
 */

import type {
  IPruningManager,
  PruningDecision,
  PruningStatistics,
  SearchContext,
  SearchState,
} from '../types.js';

/**
 * Pruning configuration
 */
export interface PruningConfig {
  scoreThreshold: number;
  maxDepth: number;
  enableLearning: boolean;
}

/**
 * Default configuration
 */
const DEFAULT_CONFIG: PruningConfig = {
  scoreThreshold: 0.2,
  maxDepth: 15,
  enableLearning: true,
};

/**
 * Learned pattern for pruning
 */
interface LearnedPattern {
  pattern: string;
  pruneRate: number;
  sampleCount: number;
}

/**
 * Internal mutable statistics
 */
interface MutableStatistics {
  totalDecisions: number;
  correctPrunes: number;
  incorrectPrunes: number;
  accuracy: number;
}

/**
 * Pruning manager implementation
 */
export class PruningManager implements IPruningManager {
  private readonly config: PruningConfig;
  private readonly seenStates: Set<string>;
  private readonly learnedPatterns: Map<string, LearnedPattern>;
  private stats: MutableStatistics;

  constructor(config: Partial<PruningConfig> = {}) {
    this.config = { ...DEFAULT_CONFIG, ...config };
    this.seenStates = new Set();
    this.learnedPatterns = new Map();
    this.stats = {
      totalDecisions: 0,
      correctPrunes: 0,
      incorrectPrunes: 0,
      accuracy: 1.0,
    };
  }

  /**
   * Decide whether to prune a state
   */
  shouldPrune(state: SearchState, context: SearchContext): PruningDecision {
    this.stats.totalDecisions++;

    // Check for duplicate
    const stateHash = this.hashState(state);
    if (this.seenStates.has(stateHash)) {
      return {
        prune: true,
        reason: 'duplicate',
        confidence: 1.0,
      };
    }
    this.seenStates.add(stateHash);

    // Check depth limit
    if (state.depth > this.config.maxDepth) {
      return {
        prune: true,
        reason: 'resource_limit',
        confidence: 0.9,
      };
    }

    // Check learned patterns
    if (this.config.enableLearning) {
      const learnedDecision = this.checkLearnedPatterns(state);
      if (learnedDecision) {
        return learnedDecision;
      }
    }

    // Check for dead ends (empty code or obvious failures)
    if (this.isDeadEnd(state, context)) {
      return {
        prune: true,
        reason: 'dead_end',
        confidence: 0.8,
      };
    }

    // Default: don't prune
    return {
      prune: false,
      reason: 'low_score', // Will only be used if prune is true
      confidence: 0.5,
    };
  }

  /**
   * Learn from pruning outcome
   */
  learn(state: SearchState, outcome: 'correct' | 'incorrect'): void {
    if (!this.config.enableLearning) return;

    if (outcome === 'correct') {
      this.stats.correctPrunes++;
    } else {
      this.stats.incorrectPrunes++;
    }

    // Update accuracy
    const total = this.stats.correctPrunes + this.stats.incorrectPrunes;
    this.stats.accuracy = total > 0 
      ? this.stats.correctPrunes / total 
      : 1.0;

    // Learn pattern
    const pattern = this.extractPattern(state);
    const existing = this.learnedPatterns.get(pattern);

    if (existing) {
      existing.sampleCount++;
      existing.pruneRate =
        (existing.pruneRate * (existing.sampleCount - 1) +
          (outcome === 'correct' ? 1 : 0)) /
        existing.sampleCount;
    } else {
      this.learnedPatterns.set(pattern, {
        pattern,
        pruneRate: outcome === 'correct' ? 1 : 0,
        sampleCount: 1,
      });
    }
  }

  /**
   * Get pruning statistics
   */
  getStatistics(): PruningStatistics {
    return { ...this.stats };
  }

  /**
   * Get learned patterns count
   */
  getLearnedPatternsCount(): number {
    return this.learnedPatterns.size;
  }

  /**
   * Reset state (for new search)
   */
  reset(): void {
    this.seenStates.clear();
  }

  /**
   * Hash a state for duplicate detection
   */
  private hashState(state: SearchState): string {
    return `${state.code}:${state.depth}`;
  }

  /**
   * Extract pattern from state for learning
   */
  private extractPattern(state: SearchState): string {
    // Simple pattern: code structure signature
    const codeSignature = state.code
      .replace(/\s+/g, ' ')
      .replace(/[a-z]+/g, 'x')
      .replace(/[0-9]+/g, 'n')
      .substring(0, 50);
    
    return codeSignature;
  }

  /**
   * Check if state matches learned patterns to prune
   */
  private checkLearnedPatterns(state: SearchState): PruningDecision | null {
    const pattern = this.extractPattern(state);
    const learned = this.learnedPatterns.get(pattern);

    if (learned && learned.sampleCount >= 3 && learned.pruneRate > 0.7) {
      return {
        prune: true,
        reason: 'learned_pattern',
        confidence: learned.pruneRate,
      };
    }

    return null;
  }

  /**
   * Check if state is a dead end
   */
  private isDeadEnd(state: SearchState, _context: SearchContext): boolean {
    // Empty code
    if (!state.code || state.code.trim().length === 0) {
      return true;
    }

    // Syntax error indicators
    const errorPatterns = [
      'SyntaxError',
      'TypeError',
      'undefined is not',
      'null is not',
    ];
    
    for (const pattern of errorPatterns) {
      if (state.code.includes(pattern)) {
        return true;
      }
    }

    return false;
  }
}
