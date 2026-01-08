/**
 * AdaptiveBeamSearch - Adaptive Beam Width Search
 *
 * Extends BeamSearch with dynamic beam width adjustment based on
 * search progress. When stagnation is detected (no improvement for
 * N iterations), beam width is increased up to a maximum.
 *
 * @module @nahisaho/musubix-neural-search
 * @see TSK-NS-102
 * @see DES-NS-102
 * @see REQ-NS-102
 *
 * @example
 * ```typescript
 * import { AdaptiveBeamSearch } from './AdaptiveBeamSearch.js';
 *
 * const search = new AdaptiveBeamSearch({
 *   initialBeamWidth: 5,
 *   maxBeamWidth: 100,
 *   stagnationThreshold: 10,
 * });
 * const results = await search.search(initial, expand, scorer, context, config);
 * ```
 */

import type {
  Branch,
  IBranchScorer,
  IBeamSearch,
  SearchConfig,
  SearchContext,
  SearchResult,
  SearchState,
  SearchStatistics,
} from '../types.js';
import { SearchTimeoutError } from '../errors.js';

// =============================================================================
// Types
// =============================================================================

/**
 * Configuration for adaptive beam search
 */
export interface AdaptiveBeamConfig {
  /** Initial beam width (default: 5) */
  initialBeamWidth: number;
  /** Maximum beam width allowed (default: 100) */
  maxBeamWidth: number;
  /** Iterations without improvement before adaptation (default: 10) */
  stagnationThreshold: number;
  /** Fraction to increase beam width on stagnation (default: 0.5 = 50%) */
  beamWidthIncrease: number;
  /** Minimum score improvement to not count as stagnation */
  improvementThreshold: number;
}

/**
 * Adaptive search statistics
 */
export interface AdaptiveStatistics {
  /** Current beam width */
  currentBeamWidth: number;
  /** Number of beam width adjustments made */
  beamWidthAdjustments: number;
  /** Current stagnation counter */
  stagnationCount: number;
  /** Best score seen */
  bestScore: number;
  /** Iterations since last improvement */
  iterationsSinceImprovement: number;
}

// =============================================================================
// Default Configuration
// =============================================================================

const DEFAULT_CONFIG: AdaptiveBeamConfig = {
  initialBeamWidth: 5,
  maxBeamWidth: 100,
  stagnationThreshold: 10,
  beamWidthIncrease: 0.5,
  improvementThreshold: 0.001,
};

// =============================================================================
// Implementation
// =============================================================================

/**
 * Adaptive Beam Search implementation with dynamic beam width adjustment
 */
export class AdaptiveBeamSearch implements IBeamSearch {
  private readonly adaptiveConfig: AdaptiveBeamConfig;
  private currentBeam: SearchState[];
  private statistics: SearchStatistics;

  // Adaptive state
  private currentBeamWidth: number;
  private beamWidthAdjustments: number = 0;
  private stagnationCount: number = 0;
  private bestScore: number = -Infinity;
  private iterationsSinceImprovement: number = 0;

  constructor(config: Partial<AdaptiveBeamConfig> = {}) {
    this.adaptiveConfig = { ...DEFAULT_CONFIG, ...config };
    this.currentBeamWidth = this.adaptiveConfig.initialBeamWidth;
    this.currentBeam = [];
    this.statistics = {
      totalExpanded: 0,
      totalPruned: 0,
      maxDepthReached: 0,
      averageScore: 0,
      timeElapsed: 0,
    };
  }

  /**
   * Execute adaptive beam search
   */
  async search(
    initial: SearchState,
    expand: (state: SearchState) => Promise<Branch[]>,
    scorer: IBranchScorer,
    context: SearchContext,
    config: SearchConfig
  ): Promise<SearchResult[]> {
    const startTime = Date.now();

    // Use config beam width or adaptive width
    this.currentBeamWidth = config.beamWidth ?? this.adaptiveConfig.initialBeamWidth;

    this.currentBeam = [initial];
    const allResults: SearchResult[] = [];
    let iteration = 0;
    let totalPruned = 0;
    let totalExpanded = 0;
    let maxDepth = 0;
    const scores: number[] = [];

    // Reset adaptive state
    this.bestScore = -Infinity;
    this.iterationsSinceImprovement = 0;

    while (iteration < config.maxIterations && this.currentBeam.length > 0) {
      // Check timeout
      if (Date.now() - startTime > config.timeout) {
        throw new SearchTimeoutError(config.timeout);
      }

      // Check depth
      const maxBeamDepth = Math.max(...this.currentBeam.map((s) => s.depth));
      maxDepth = Math.max(maxDepth, maxBeamDepth);
      if (maxBeamDepth >= config.maxDepth) {
        break;
      }

      // Expand all states in beam
      const candidates: Array<{
        state: SearchState;
        score: number;
        path: SearchState[];
      }> = [];

      for (const state of this.currentBeam) {
        const branches = await expand(state);
        totalExpanded += branches.length;

        // Score all branches
        const scored = await scorer.scoreBatch(branches, context);

        for (const branchScore of scored) {
          // Apply pruning threshold
          if (
            config.pruneThreshold !== undefined &&
            branchScore.score < config.pruneThreshold
          ) {
            totalPruned++;
            continue;
          }

          const path = this.buildPath(branchScore.branch.to, context.history);
          candidates.push({
            state: branchScore.branch.to,
            score: branchScore.score,
            path,
          });
          scores.push(branchScore.score);
        }
      }

      // Sort by score and keep top beamWidth
      candidates.sort((a, b) => b.score - a.score);
      const nextBeam = candidates.slice(0, this.currentBeamWidth);

      // Track best score and check for improvement
      const iterationBestScore = nextBeam.length > 0 ? nextBeam[0].score : -Infinity;
      const improved =
        iterationBestScore > this.bestScore + this.adaptiveConfig.improvementThreshold;

      if (improved) {
        this.bestScore = iterationBestScore;
        this.iterationsSinceImprovement = 0;
      } else {
        this.iterationsSinceImprovement++;
      }

      // Check for stagnation and adapt
      if (
        this.iterationsSinceImprovement >= this.adaptiveConfig.stagnationThreshold
      ) {
        this.adjustBeamWidth();
        this.iterationsSinceImprovement = 0;
        this.stagnationCount++;
      }

      // Add to results
      for (const candidate of nextBeam) {
        allResults.push({
          state: candidate.state,
          score: candidate.score,
          path: candidate.path,
          iterations: iteration + 1,
          pruned: totalPruned,
        });
      }

      // Update beam
      this.currentBeam = nextBeam.map((c) => c.state);
      iteration++;
    }

    // Update statistics
    this.statistics = {
      totalExpanded,
      totalPruned,
      maxDepthReached: maxDepth,
      averageScore:
        scores.length > 0
          ? scores.reduce((a, b) => a + b, 0) / scores.length
          : 0,
      timeElapsed: Date.now() - startTime,
    };

    // Return best results (deduplicated)
    const seen = new Set<string>();
    return allResults
      .filter((r) => {
        if (seen.has(r.state.id)) return false;
        seen.add(r.state.id);
        return true;
      })
      .sort((a, b) => b.score - a.score)
      .slice(0, this.currentBeamWidth);
  }

  /**
   * Get current beam
   */
  getCurrentBeam(): SearchState[] {
    return [...this.currentBeam];
  }

  /**
   * Get search statistics
   */
  getStatistics(): SearchStatistics {
    return { ...this.statistics };
  }

  /**
   * Get adaptive-specific statistics
   */
  getAdaptiveStatistics(): AdaptiveStatistics {
    return {
      currentBeamWidth: this.currentBeamWidth,
      beamWidthAdjustments: this.beamWidthAdjustments,
      stagnationCount: this.stagnationCount,
      bestScore: this.bestScore,
      iterationsSinceImprovement: this.iterationsSinceImprovement,
    };
  }

  /**
   * Reset adaptive state
   */
  reset(): void {
    this.currentBeamWidth = this.adaptiveConfig.initialBeamWidth;
    this.beamWidthAdjustments = 0;
    this.stagnationCount = 0;
    this.bestScore = -Infinity;
    this.iterationsSinceImprovement = 0;
    this.currentBeam = [];
    this.statistics = {
      totalExpanded: 0,
      totalPruned: 0,
      maxDepthReached: 0,
      averageScore: 0,
      timeElapsed: 0,
    };
  }

  // ===========================================================================
  // Private Methods
  // ===========================================================================

  /**
   * Adjust beam width when stagnation detected
   */
  private adjustBeamWidth(): void {
    const increase = Math.ceil(
      this.currentBeamWidth * this.adaptiveConfig.beamWidthIncrease
    );
    const newWidth = Math.min(
      this.currentBeamWidth + increase,
      this.adaptiveConfig.maxBeamWidth
    );

    if (newWidth > this.currentBeamWidth) {
      this.currentBeamWidth = newWidth;
      this.beamWidthAdjustments++;
    }
  }

  /**
   * Build path from state to root
   */
  private buildPath(state: SearchState, history: SearchState[]): SearchState[] {
    const path: SearchState[] = [state];

    for (let i = history.length - 1; i >= 0; i--) {
      if (history[i].id === state.parent) {
        path.unshift(history[i]);
        break;
      }
    }

    return path;
  }
}
