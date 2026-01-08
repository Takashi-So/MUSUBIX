/**
 * Best-First Search
 * @module @nahisaho/musubix-neural-search
 * @description Best-first search algorithm for code synthesis
 */

import type {
  Branch,
  IBranchScorer,
  IBestFirstSearch,
  SearchConfig,
  SearchContext,
  SearchResult,
  SearchState,
} from '../types.js';
import { SearchDepthExceededError, SearchTimeoutError } from '../errors.js';
import { PriorityQueue } from './PriorityQueue.js';

/**
 * Best-first search implementation
 */
export class BestFirstSearch implements IBestFirstSearch {
  private openList: PriorityQueue<{ state: SearchState; score: number; path: SearchState[] }>;
  private closedSet: Set<string>;

  constructor() {
    this.openList = new PriorityQueue();
    this.closedSet = new Set();
  }

  /**
   * Execute best-first search
   */
  async search(
    initial: SearchState,
    expand: (state: SearchState) => Promise<Branch[]>,
    scorer: IBranchScorer,
    context: SearchContext,
    config: SearchConfig
  ): Promise<SearchResult> {
    const startTime = Date.now();

    // Reset state
    this.openList.clear();
    this.closedSet.clear();

    // Add initial state with neutral score (not a goal yet)
    this.openList.push({ state: initial, score: 0.0, path: [initial] }, 0.0);

    let iteration = 0;
    let totalPruned = 0;

    while (!this.openList.isEmpty() && iteration < config.maxIterations) {
      // Check timeout
      if (Date.now() - startTime > config.timeout) {
        throw new SearchTimeoutError(config.timeout);
      }

      // Get best state
      const current = this.openList.pop();
      if (!current) break;

      const { state, score, path } = current;

      // Skip if already visited
      if (this.closedSet.has(state.id)) {
        continue;
      }
      this.closedSet.add(state.id);

      // Check depth (only after at least one expansion)
      if (state.depth > 0 && state.depth >= config.maxDepth) {
        throw new SearchDepthExceededError(config.maxDepth);
      }

      // Check if goal (assume high score = goal, but only for non-initial states)
      if (state.depth > 0 && score >= 0.9) {
        return {
          state,
          score,
          path,
          iterations: iteration + 1,
          pruned: totalPruned,
        };
      }

      // Expand state
      const branches = await expand(state);
      
      // Check timeout again after expansion (expansion might be slow)
      if (Date.now() - startTime > config.timeout) {
        throw new SearchTimeoutError(config.timeout);
      }
      
      const scored = await scorer.scoreBatch(branches, context);

      for (const branchScore of scored) {
        const nextState = branchScore.branch.to;

        // Skip if already visited
        if (this.closedSet.has(nextState.id)) {
          continue;
        }

        // Apply pruning
        if (
          config.pruneThreshold !== undefined &&
          branchScore.score < config.pruneThreshold
        ) {
          totalPruned++;
          continue;
        }

        const nextPath = [...path, nextState];
        this.openList.push(
          { state: nextState, score: branchScore.score, path: nextPath },
          branchScore.score
        );
      }

      iteration++;
    }

    // Return best found if no goal reached
    const best = this.openList.pop();
    if (best) {
      return {
        state: best.state,
        score: best.score,
        path: best.path,
        iterations: iteration,
        pruned: totalPruned,
      };
    }

    // Return initial if nothing better found
    return {
      state: initial,
      score: 0,
      path: [initial],
      iterations: iteration,
      pruned: totalPruned,
    };
  }

  /**
   * Get open list size
   */
  getOpenListSize(): number {
    return this.openList.size();
  }
}
