/**
 * Beam Search
 * @module @nahisaho/musubix-neural-search
 * @description Beam search algorithm for code synthesis
 * Traces to: REQ-NS-002 (探索優先順位付け)
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

/**
 * Beam search implementation
 */
export class BeamSearch implements IBeamSearch {
  private currentBeam: SearchState[];
  private statistics: SearchStatistics;

  constructor() {
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
   * Execute beam search
   */
  async search(
    initial: SearchState,
    expand: (state: SearchState) => Promise<Branch[]>,
    scorer: IBranchScorer,
    context: SearchContext,
    config: SearchConfig
  ): Promise<SearchResult[]> {
    const startTime = Date.now();
    const beamWidth = config.beamWidth ?? 5;

    this.currentBeam = [initial];
    const allResults: SearchResult[] = [];
    let iteration = 0;
    let totalPruned = 0;
    let totalExpanded = 0;
    let maxDepth = 0;
    const scores: number[] = [];

    while (
      iteration < config.maxIterations &&
      this.currentBeam.length > 0
    ) {
      // Check timeout
      if (Date.now() - startTime > config.timeout) {
        throw new SearchTimeoutError(config.timeout);
      }

      // Check depth - return results instead of throwing
      const maxBeamDepth = Math.max(...this.currentBeam.map((s) => s.depth));
      maxDepth = Math.max(maxDepth, maxBeamDepth);
      if (maxBeamDepth >= config.maxDepth) {
        // Reached max depth, return current results
        break;
      }

      // Expand all states in beam
      const candidates: Array<{ state: SearchState; score: number; path: SearchState[] }> = [];

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
      const nextBeam = candidates.slice(0, beamWidth);

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
      averageScore: scores.length > 0 
        ? scores.reduce((a, b) => a + b, 0) / scores.length 
        : 0,
      timeElapsed: Date.now() - startTime,
    };

    // Return best results (deduplicated by state id)
    const seen = new Set<string>();
    return allResults
      .filter((r) => {
        if (seen.has(r.state.id)) return false;
        seen.add(r.state.id);
        return true;
      })
      .sort((a, b) => b.score - a.score)
      .slice(0, beamWidth);
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
   * Build path from state to root
   */
  private buildPath(state: SearchState, history: SearchState[]): SearchState[] {
    const path: SearchState[] = [state];
    
    // Add history states
    for (let i = history.length - 1; i >= 0; i--) {
      if (history[i].id === state.parent) {
        path.unshift(history[i]);
        break;
      }
    }
    
    return path;
  }
}
