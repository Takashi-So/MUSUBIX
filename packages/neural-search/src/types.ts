/**
 * Neural Search Types
 * @module @nahisaho/musubix-neural-search
 * @description Type definitions for neural search engine
 */

// ============================================================================
// Embedding Types
// ============================================================================

/**
 * Vector embedding representation
 */
export type Embedding = Float32Array | number[];

/**
 * Configuration for embedding model
 */
export interface EmbeddingConfig {
  readonly modelName: string;
  readonly dimension: number;
  readonly maxLength: number;
  readonly poolingStrategy: 'mean' | 'cls' | 'max';
}

/**
 * Embedding model interface
 * Traces to: REQ-NS-001 (分岐スコアリング)
 */
export interface IEmbeddingModel {
  /**
   * Embed source code
   */
  embedCode(code: string): Promise<Embedding>;
  
  /**
   * Embed specification/requirement
   */
  embedSpec(spec: string): Promise<Embedding>;
  
  /**
   * Calculate similarity between embeddings
   */
  similarity(a: Embedding, b: Embedding): number;
  
  /**
   * Batch embed multiple texts
   */
  embedBatch(texts: string[]): Promise<Embedding[]>;
}

// ============================================================================
// Scorer Types
// ============================================================================

/**
 * Search state representing a partial synthesis
 */
export interface SearchState {
  readonly id: string;
  readonly code: string;
  readonly parent?: string;
  readonly depth: number;
  readonly metadata: Record<string, unknown>;
}

/**
 * Branch in the search tree
 */
export interface Branch {
  readonly from: SearchState;
  readonly to: SearchState;
  readonly action: string;
  readonly features: BranchFeatures;
}

/**
 * Features extracted from a branch
 */
export interface BranchFeatures {
  readonly codeEmbedding: Embedding;
  readonly specSimilarity: number;
  readonly syntaxValid: boolean;
  readonly typeChecks: boolean;
  readonly complexity: number;
  readonly novelty: number;
}

/**
 * Score result for a branch
 */
export interface BranchScore {
  readonly branch: Branch;
  readonly score: number;
  readonly confidence: number;
  readonly components: ScoreComponents;
}

/**
 * Components of the score
 */
export interface ScoreComponents {
  readonly specAlignment: number;
  readonly codeQuality: number;
  readonly novelty: number;
  readonly feasibility: number;
}

/**
 * Branch scorer interface
 * Traces to: REQ-NS-001 (分岐スコアリング)
 */
export interface IBranchScorer {
  /**
   * Score a single branch
   */
  score(branch: Branch, context: SearchContext): Promise<BranchScore>;
  
  /**
   * Score multiple branches
   */
  scoreBatch(branches: Branch[], context: SearchContext): Promise<BranchScore[]>;
  
  /**
   * Update scorer with feedback
   */
  update(feedback: ScoreFeedback): void;
}

/**
 * Context for search scoring
 */
export interface SearchContext {
  readonly specification: string;
  readonly specEmbedding: Embedding;
  readonly constraints: string[];
  readonly history: SearchState[];
}

/**
 * Feedback for score adjustment
 */
export interface ScoreFeedback {
  readonly branchId: string;
  readonly actualOutcome: 'success' | 'failure' | 'partial';
  readonly reason?: string;
}

// ============================================================================
// Context Encoder Types
// ============================================================================

/**
 * Encoded context representation
 */
export interface EncodedContext {
  readonly embedding: Embedding;
  readonly features: ContextFeatures;
  readonly tokens: number;
}

/**
 * Features extracted from context
 */
export interface ContextFeatures {
  readonly specLength: number;
  readonly constraintCount: number;
  readonly complexityEstimate: number;
  readonly domainSignals: string[];
}

/**
 * Context encoder interface
 */
export interface IContextEncoder {
  /**
   * Encode full search context
   */
  encode(context: SearchContext): Promise<EncodedContext>;
  
  /**
   * Encode specification only
   */
  encodeSpec(spec: string): Promise<EncodedContext>;
  
  /**
   * Update encoder with learned patterns
   */
  updatePatterns(patterns: string[]): void;
}

// ============================================================================
// Search Engine Types
// ============================================================================

/**
 * Search configuration
 */
export interface SearchConfig {
  readonly maxDepth: number;
  readonly maxIterations: number;
  readonly timeout: number;
  readonly beamWidth?: number;
  readonly pruneThreshold?: number;
}

/**
 * Search result
 */
export interface SearchResult {
  readonly state: SearchState;
  readonly score: number;
  readonly path: SearchState[];
  readonly iterations: number;
  readonly pruned: number;
}

/**
 * Beam search interface
 * Traces to: REQ-NS-002 (探索優先順位付け)
 */
export interface IBeamSearch {
  /**
   * Execute beam search
   */
  search(
    initial: SearchState,
    expand: (state: SearchState) => Promise<Branch[]>,
    scorer: IBranchScorer,
    context: SearchContext,
    config: SearchConfig
  ): Promise<SearchResult[]>;
  
  /**
   * Get current beam
   */
  getCurrentBeam(): SearchState[];
  
  /**
   * Get search statistics
   */
  getStatistics(): SearchStatistics;
}

/**
 * Best-first search interface
 */
export interface IBestFirstSearch {
  /**
   * Execute best-first search
   */
  search(
    initial: SearchState,
    expand: (state: SearchState) => Promise<Branch[]>,
    scorer: IBranchScorer,
    context: SearchContext,
    config: SearchConfig
  ): Promise<SearchResult>;
  
  /**
   * Get open list size
   */
  getOpenListSize(): number;
}

/**
 * Search statistics
 */
export interface SearchStatistics {
  readonly totalExpanded: number;
  readonly totalPruned: number;
  readonly maxDepthReached: number;
  readonly averageScore: number;
  readonly timeElapsed: number;
}

/**
 * Pruning decision
 */
export interface PruningDecision {
  readonly prune: boolean;
  readonly reason: PruningReason;
  readonly confidence: number;
}

/**
 * Pruning reason
 */
export type PruningReason = 
  | 'low_score'
  | 'duplicate'
  | 'dead_end'
  | 'resource_limit'
  | 'learned_pattern';

/**
 * Pruning manager interface
 * Traces to: REQ-NS-003 (学習ベースプルーニング)
 */
export interface IPruningManager {
  /**
   * Decide whether to prune a state
   */
  shouldPrune(state: SearchState, context: SearchContext): PruningDecision;
  
  /**
   * Learn from pruning outcome
   */
  learn(state: SearchState, outcome: 'correct' | 'incorrect'): void;
  
  /**
   * Get pruning statistics
   */
  getStatistics(): PruningStatistics;
}

/**
 * Pruning statistics
 */
export interface PruningStatistics {
  readonly totalDecisions: number;
  readonly correctPrunes: number;
  readonly incorrectPrunes: number;
  readonly accuracy: number;
}

// ============================================================================
// Learning Module Types
// ============================================================================

/**
 * Search trajectory
 * Traces to: REQ-NS-004 (探索履歴学習)
 */
export interface SearchTrajectory {
  readonly id: string;
  readonly specification: string;
  readonly path: TrajectoryStep[];
  readonly outcome: TrajectoryOutcome;
  readonly timestamp: Date;
}

/**
 * Step in a trajectory
 */
export interface TrajectoryStep {
  readonly state: SearchState;
  readonly score: number;
  readonly action: string;
  readonly duration: number;
}

/**
 * Outcome of a trajectory
 */
export interface TrajectoryOutcome {
  readonly success: boolean;
  readonly finalScore: number;
  readonly reason?: string;
  readonly userFeedback?: 'accept' | 'reject' | 'modify';
}

/**
 * Trajectory log interface
 */
export interface ITrajectoryLog {
  /**
   * Log a completed trajectory
   */
  log(trajectory: SearchTrajectory): void;
  
  /**
   * Query trajectories by specification
   */
  queryBySpec(spec: string, limit?: number): SearchTrajectory[];
  
  /**
   * Get successful trajectories
   */
  getSuccessful(limit?: number): SearchTrajectory[];
  
  /**
   * Get statistics
   */
  getStatistics(): TrajectoryStatistics;
}

/**
 * Trajectory statistics
 */
export interface TrajectoryStatistics {
  readonly totalTrajectories: number;
  readonly successRate: number;
  readonly averageLength: number;
  readonly averageDuration: number;
}

/**
 * Learning update
 */
export interface LearningUpdate {
  readonly trajectoryId: string;
  readonly gradients: Map<string, number>;
  readonly loss: number;
}

/**
 * Online learner interface
 */
export interface IOnlineLearner {
  /**
   * Learn from a trajectory
   */
  learnFromTrajectory(trajectory: SearchTrajectory): LearningUpdate;
  
  /**
   * Get current model parameters
   */
  getParameters(): Map<string, number>;
  
  /**
   * Apply learning update
   */
  applyUpdate(update: LearningUpdate): void;
  
  /**
   * Get learning statistics
   */
  getStatistics(): LearningStatistics;
}

/**
 * Learning statistics
 */
export interface LearningStatistics {
  readonly totalUpdates: number;
  readonly averageLoss: number;
  readonly learningRate: number;
  readonly convergenceMetric: number;
}

/**
 * Model update request
 */
export interface ModelUpdateRequest {
  readonly updates: LearningUpdate[];
  readonly batchSize: number;
  readonly epoch: number;
}

/**
 * Model updater interface
 */
export interface IModelUpdater {
  /**
   * Queue an update
   */
  queueUpdate(update: LearningUpdate): void;
  
  /**
   * Flush pending updates
   */
  flushUpdates(): Promise<void>;
  
  /**
   * Get pending update count
   */
  getPendingCount(): number;
}

// ============================================================================
// Priority Queue Types
// ============================================================================

/**
 * Priority queue item
 */
export interface PriorityItem<T> {
  readonly item: T;
  readonly priority: number;
}

/**
 * Priority queue interface
 */
export interface IPriorityQueue<T> {
  /**
   * Add item with priority
   */
  push(item: T, priority: number): void;
  
  /**
   * Remove and return highest priority item
   */
  pop(): T | undefined;
  
  /**
   * Peek at highest priority item
   */
  peek(): T | undefined;
  
  /**
   * Get queue size
   */
  size(): number;
  
  /**
   * Check if empty
   */
  isEmpty(): boolean;
  
  /**
   * Clear the queue
   */
  clear(): void;
}
