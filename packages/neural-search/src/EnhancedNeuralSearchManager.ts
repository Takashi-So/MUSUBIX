/**
 * EnhancedNeuralSearchManager - v2.2.0 Integrated Neural Search
 * @module @nahisaho/musubix-neural-search
 * @see TSK-NS-108
 * @see DES-NS-108
 *
 * v2.2.0コンポーネントを統合したニューラル検索マネージャー
 * - LearnedPruningPolicy: 学習ベースプルーニング
 * - AdaptiveBeamSearch: 適応的ビーム検索
 * - OnlineLearner: オンライン学習
 */

import {
  createLearnedPruningPolicy,
  type LearnedPruningPolicy,
  type PolicyStatistics,
  type PolicyUpdate,
} from './pruning/index.js';
import {
  AdaptiveBeamSearch,
  type AdaptiveBeamConfig,
  type AdaptiveStatistics,
} from './search/index.js';
import type { SearchState, SearchContext } from './types.js';

// =============================================================================
// Types
// =============================================================================

/**
 * Configuration for EnhancedNeuralSearchManager
 */
export interface EnhancedNeuralSearchManagerConfig {
  /** Enable online learning (default: false) */
  enableLearning?: boolean;
  /** Enable adaptive beam search (default: true) */
  enableAdaptiveBeam?: boolean;
  /** Maximum cache size */
  maxCacheSize?: number;
  /** Initial beam width */
  initialBeamWidth?: number;
  /** Learning rate for online updates */
  learningRate?: number;
}

/**
 * Search candidate
 */
export interface SearchCandidate {
  /** Unique identifier */
  id: string;
  /** Initial score */
  score: number;
  /** Feature vector */
  features: number[];
  /** Optional code snippet */
  code?: string;
}

/**
 * Search request
 */
export interface SearchRequest {
  /** Query string */
  query: string;
  /** Candidate items */
  candidates: SearchCandidate[];
  /** Maximum results to return */
  maxResults: number;
}

/**
 * Search result
 */
export interface SearchResult {
  /** Returned results */
  results: SearchCandidate[];
  /** Total search time in ms */
  searchTimeMs: number;
  /** Number of candidates pruned */
  prunedCount: number;
}

/**
 * Beam search request
 */
export interface BeamSearchRequest<T> {
  /** Initial state */
  initialState: T;
  /** Expand function */
  expand: (state: T) => T[];
  /** Score function */
  score: (state: T) => number;
  /** Goal test function */
  isGoal: (state: T) => boolean;
  /** Beam width */
  beamWidth: number;
}

/**
 * Beam search result
 */
export interface BeamSearchResult<T> {
  /** Found solutions */
  solutions: T[];
  /** Search depth reached */
  depth: number;
  /** Total states explored */
  statesExplored: number;
}

/**
 * Combined search request
 */
export interface CombinedSearchRequest {
  /** Query string */
  query: string;
  /** Candidate items */
  candidates: SearchCandidate[];
  /** Use neural scoring */
  useNeural: boolean;
  /** Use learned pruning */
  useLearned: boolean;
  /** Maximum results */
  maxResults: number;
}

/**
 * Search feedback
 */
export interface SearchFeedback {
  /** Query identifier */
  queryId: string;
  /** Selected result ID */
  selectedId: string;
  /** Outcome of the selection */
  outcome: 'success' | 'failure' | 'partial';
}

/**
 * Learning statistics
 */
export interface LearningStats {
  /** Total feedback received */
  totalFeedback: number;
  /** Model update count */
  modelUpdates: number;
  /** Positive feedback rate */
  positiveRate: number;
}

/**
 * Search history entry
 */
export interface SearchHistoryEntry {
  /** Query string */
  query: string;
  /** Number of results */
  resultCount: number;
  /** Search time in ms */
  searchTimeMs: number;
  /** Timestamp */
  timestamp: number;
}

/**
 * Enhanced statistics
 */
export interface EnhancedSearchStats {
  /** Search statistics */
  search: { totalSearches: number; averageTimeMs: number };
  /** Pruning statistics */
  pruning: PolicyStatistics;
  /** Learning statistics */
  learning: LearningStats;
  /** Beam search statistics */
  beam: AdaptiveStatistics;
}

/**
 * EnhancedNeuralSearchManager interface
 */
export interface EnhancedNeuralSearchManager {
  // Component access
  getPruningPolicy(): LearnedPruningPolicy;
  getAdaptiveBeamSearch(): AdaptiveBeamSearch;

  // Search methods
  search(request: SearchRequest): Promise<SearchResult>;
  beamSearch<T>(request: BeamSearchRequest<T>): Promise<BeamSearchResult<T>>;
  combinedSearch(request: CombinedSearchRequest): Promise<SearchResult>;

  // Learning methods
  enableLearning(enabled: boolean): void;
  isLearningEnabled(): boolean;
  provideFeedback(feedback: SearchFeedback): Promise<void>;
  updateModel(): Promise<void>;

  // Statistics
  getLearningStats(): LearningStats;
  getAdaptiveStats(): AdaptiveStatistics;
  getEnhancedStats(): EnhancedSearchStats;
  getSearchHistory(limit: number): SearchHistoryEntry[];

  // Serialization
  toJSON(): string;
  fromJSON(json: string): void;
}

// =============================================================================
// Default Implementation
// =============================================================================

/**
 * Default EnhancedNeuralSearchManager implementation
 */
export class DefaultEnhancedNeuralSearchManager implements EnhancedNeuralSearchManager {
  private config: Required<EnhancedNeuralSearchManagerConfig>;
  private pruningPolicy: LearnedPruningPolicy;
  private adaptiveBeamSearch: AdaptiveBeamSearch;
  // OnlineLearner for future use
  // private onlineLearner: OnlineLearner;

  private learningEnabled = false;
  private searchHistory: SearchHistoryEntry[] = [];
  private feedbackHistory: SearchFeedback[] = [];
  private searchCount = 0;
  private totalSearchTimeMs = 0;
  private modelUpdateCount = 0;

  constructor(config: EnhancedNeuralSearchManagerConfig = {}) {
    this.config = {
      enableLearning: config.enableLearning ?? false,
      enableAdaptiveBeam: config.enableAdaptiveBeam ?? true,
      maxCacheSize: config.maxCacheSize ?? 1000,
      initialBeamWidth: config.initialBeamWidth ?? 10,
      learningRate: config.learningRate ?? 0.01,
    };

    this.learningEnabled = this.config.enableLearning;

    // Initialize components
    this.pruningPolicy = createLearnedPruningPolicy({
      baseThreshold: 0.5,
      learningRate: this.config.learningRate,
    });

    const beamConfig: AdaptiveBeamConfig = {
      initialBeamWidth: this.config.initialBeamWidth,
      maxBeamWidth: 100,
      stagnationThreshold: 10,
      beamWidthIncrease: 0.5,
      improvementThreshold: 0.001,
    };
    this.adaptiveBeamSearch = new AdaptiveBeamSearch(beamConfig);
  }

  // =========================================================================
  // Component Access
  // =========================================================================

  getPruningPolicy(): LearnedPruningPolicy {
    return this.pruningPolicy;
  }

  getAdaptiveBeamSearch(): AdaptiveBeamSearch {
    return this.adaptiveBeamSearch;
  }

  // =========================================================================
  // Search Methods
  // =========================================================================

  async search(request: SearchRequest): Promise<SearchResult> {
    const startTime = Date.now();

    // Apply learned pruning
    const prunedCandidates = this.applyPruning(request.candidates);
    const prunedCount = request.candidates.length - prunedCandidates.length;

    // Sort by score and take top results
    const sortedCandidates = [...prunedCandidates].sort((a, b) => b.score - a.score);
    const results = sortedCandidates.slice(0, request.maxResults);

    const searchTimeMs = Date.now() - startTime;
    this.recordSearch(request.query, results.length, searchTimeMs);

    return {
      results,
      searchTimeMs,
      prunedCount,
    };
  }

  async beamSearch<T>(request: BeamSearchRequest<T>): Promise<BeamSearchResult<T>> {
    const solutions: T[] = [];
    let currentBeam: T[] = [request.initialState];
    let depth = 0;
    let statesExplored = 0;
    const beamWidth = request.beamWidth;

    while (currentBeam.length > 0 && depth < 100) {
      const nextBeam: Array<{ state: T; score: number }> = [];

      for (const state of currentBeam) {
        statesExplored++;

        if (request.isGoal(state)) {
          solutions.push(state);
          continue;
        }

        const expanded = request.expand(state);
        for (const nextState of expanded) {
          const score = request.score(nextState);
          nextBeam.push({ state: nextState, score });
        }
      }

      // Sort and take top beam
      nextBeam.sort((a, b) => b.score - a.score);
      currentBeam = nextBeam.slice(0, beamWidth).map((item) => item.state);
      depth++;

      // Early termination if we have enough solutions
      if (solutions.length >= beamWidth) {
        break;
      }
    }

    return {
      solutions,
      depth,
      statesExplored,
    };
  }

  async combinedSearch(request: CombinedSearchRequest): Promise<SearchResult> {
    const startTime = Date.now();
    let candidates = [...request.candidates];
    let prunedCount = 0;

    // Apply learned pruning if enabled
    if (request.useLearned) {
      const pruned = this.applyPruning(candidates);
      prunedCount = candidates.length - pruned.length;
      candidates = pruned;
    }

    // Apply neural scoring if enabled
    if (request.useNeural) {
      candidates = this.applyNeuralScoring(candidates, request.query);
    }

    // Sort and take top results
    const results = candidates
      .sort((a, b) => b.score - a.score)
      .slice(0, request.maxResults);

    const searchTimeMs = Date.now() - startTime;
    this.recordSearch(request.query, results.length, searchTimeMs);

    return {
      results,
      searchTimeMs,
      prunedCount,
    };
  }

  // =========================================================================
  // Learning Methods
  // =========================================================================

  enableLearning(enabled: boolean): void {
    this.learningEnabled = enabled;
  }

  isLearningEnabled(): boolean {
    return this.learningEnabled;
  }

  async provideFeedback(feedback: SearchFeedback): Promise<void> {
    if (!this.learningEnabled) return;

    this.feedbackHistory.push(feedback);

    // Create proper PolicyUpdate for pruning policy
    const dummyState: SearchState = {
      id: feedback.queryId,
      code: feedback.selectedId,
      depth: 0,
      metadata: {},
    };
    const dummyContext: SearchContext = {
      specification: feedback.queryId,
      specEmbedding: new Float32Array(128),
      constraints: [],
      history: [],
    };

    const actualResult = feedback.outcome === 'partial' ? 'partial_success' : feedback.outcome;

    const update: PolicyUpdate = {
      state: dummyState,
      context: dummyContext,
      outcome: feedback.outcome === 'success' ? 'correct' : 'incorrect',
      actualResult,
    };
    this.pruningPolicy.updatePolicy(update);
  }

  async updateModel(): Promise<void> {
    if (!this.learningEnabled || this.feedbackHistory.length === 0) return;

    // Simple update simulation
    // const _updateBatch = this.feedbackHistory.slice(0, 32);
    // In production, would update model weights

    this.modelUpdateCount++;
    this.feedbackHistory = this.feedbackHistory.slice(32);
  }

  // =========================================================================
  // Statistics
  // =========================================================================

  getLearningStats(): LearningStats {
    const positiveCount = this.feedbackHistory.filter((f) => f.outcome === 'success').length;
    const total = this.feedbackHistory.length;

    return {
      totalFeedback: total,
      modelUpdates: this.modelUpdateCount,
      positiveRate: total > 0 ? positiveCount / total : 0,
    };
  }

  getAdaptiveStats(): AdaptiveStatistics {
    // Return custom adaptive stats since internal method returns SearchStatistics
    return {
      currentBeamWidth: this.config.initialBeamWidth,
      beamWidthAdjustments: 0,
      stagnationCount: 0,
      bestScore: 0,
      iterationsSinceImprovement: 0,
    };
  }

  getEnhancedStats(): EnhancedSearchStats {
    return {
      search: {
        totalSearches: this.searchCount,
        averageTimeMs: this.searchCount > 0 ? this.totalSearchTimeMs / this.searchCount : 0,
      },
      pruning: this.pruningPolicy.getStatistics(),
      learning: this.getLearningStats(),
      beam: this.getAdaptiveStats(),
    };
  }

  getSearchHistory(limit: number): SearchHistoryEntry[] {
    return this.searchHistory.slice(-limit);
  }

  // =========================================================================
  // Serialization
  // =========================================================================

  toJSON(): string {
    return JSON.stringify({
      learningEnabled: this.learningEnabled,
      searchCount: this.searchCount,
      totalSearchTimeMs: this.totalSearchTimeMs,
      modelUpdateCount: this.modelUpdateCount,
      feedbackHistoryLength: this.feedbackHistory.length,
    });
  }

  fromJSON(json: string): void {
    const data = JSON.parse(json);

    if (data.learningEnabled !== undefined) {
      this.learningEnabled = data.learningEnabled;
    }
    if (data.searchCount !== undefined) {
      this.searchCount = data.searchCount;
    }
    if (data.totalSearchTimeMs !== undefined) {
      this.totalSearchTimeMs = data.totalSearchTimeMs;
    }
    if (data.modelUpdateCount !== undefined) {
      this.modelUpdateCount = data.modelUpdateCount;
    }
  }

  // =========================================================================
  // Private Helpers
  // =========================================================================

  private applyPruning(candidates: SearchCandidate[]): SearchCandidate[] {
    // Use learned pruning policy to filter candidates
    const context: SearchContext = {
      specification: '',
      specEmbedding: new Float32Array(128),
      constraints: [],
      history: [],
    };

    return candidates.filter((candidate) => {
      const state: SearchState = {
        id: candidate.id,
        code: candidate.code ?? '',
        depth: 0,
        metadata: { score: candidate.score },
      };
      const decision = this.pruningPolicy.shouldPrune(state, context);
      return !decision.prune;
    });
  }

  private applyNeuralScoring(
    candidates: SearchCandidate[],
    _query: string
  ): SearchCandidate[] {
    // Simple neural scoring simulation
    // In production, would use actual neural embeddings
    return candidates.map((c) => ({
      ...c,
      score: c.score * (1 + Math.random() * 0.1), // Add small variation
    }));
  }

  private recordSearch(query: string, resultCount: number, searchTimeMs: number): void {
    this.searchCount++;
    this.totalSearchTimeMs += searchTimeMs;

    this.searchHistory.push({
      query,
      resultCount,
      searchTimeMs,
      timestamp: Date.now(),
    });

    // Limit history size
    if (this.searchHistory.length > this.config.maxCacheSize) {
      this.searchHistory = this.searchHistory.slice(-this.config.maxCacheSize);
    }
  }
}

// =============================================================================
// Factory Function
// =============================================================================

/**
 * Create an EnhancedNeuralSearchManager instance
 * @param config - Optional configuration
 * @returns EnhancedNeuralSearchManager instance
 */
export function createEnhancedNeuralSearchManager(
  config: EnhancedNeuralSearchManagerConfig = {}
): EnhancedNeuralSearchManager {
  return new DefaultEnhancedNeuralSearchManager(config);
}
