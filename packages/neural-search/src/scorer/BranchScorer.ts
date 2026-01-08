/**
 * Branch Scorer
 * @module @nahisaho/musubix-neural-search
 * @description Neural scoring for search branches
 * Traces to: REQ-NS-001 (分岐スコアリング)
 */

import type {
  Branch,
  BranchScore,
  IBranchScorer,
  IEmbeddingModel,
  ScoreComponents,
  ScoreFeedback,
  SearchContext,
} from '../types.js';
import { EmbeddingModel } from './EmbeddingModel.js';

/**
 * Weight configuration for score components
 */
export interface ScoreWeights {
  specAlignment: number;
  codeQuality: number;
  novelty: number;
  feasibility: number;
}

/**
 * Default score weights
 */
const DEFAULT_WEIGHTS: ScoreWeights = {
  specAlignment: 0.4,
  codeQuality: 0.3,
  novelty: 0.15,
  feasibility: 0.15,
};

/**
 * Branch scorer implementation
 */
export class BranchScorer implements IBranchScorer {
  private readonly embeddingModel: IEmbeddingModel;
  private readonly weights: ScoreWeights;
  private readonly feedbackHistory: Map<string, ScoreFeedback[]>;

  constructor(
    embeddingModel?: IEmbeddingModel,
    weights: Partial<ScoreWeights> = {}
  ) {
    this.embeddingModel = embeddingModel ?? new EmbeddingModel();
    this.weights = { ...DEFAULT_WEIGHTS, ...weights };
    this.feedbackHistory = new Map();
  }

  /**
   * Score a single branch
   */
  async score(branch: Branch, context: SearchContext): Promise<BranchScore> {
    const components = await this.computeComponents(branch, context);
    const score = this.combineScores(components);
    const confidence = this.computeConfidence(branch, context);

    return {
      branch,
      score,
      confidence,
      components,
    };
  }

  /**
   * Score multiple branches in batch
   */
  async scoreBatch(
    branches: Branch[],
    context: SearchContext
  ): Promise<BranchScore[]> {
    return Promise.all(branches.map((branch) => this.score(branch, context)));
  }

  /**
   * Update scorer with feedback
   */
  update(feedback: ScoreFeedback): void {
    const history = this.feedbackHistory.get(feedback.branchId) ?? [];
    history.push(feedback);
    this.feedbackHistory.set(feedback.branchId, history);
  }

  /**
   * Get current weights
   */
  getWeights(): ScoreWeights {
    return { ...this.weights };
  }

  /**
   * Get feedback history for a branch
   */
  getFeedbackHistory(branchId: string): ScoreFeedback[] {
    return this.feedbackHistory.get(branchId) ?? [];
  }

  /**
   * Compute individual score components
   */
  private async computeComponents(
    branch: Branch,
    context: SearchContext
  ): Promise<ScoreComponents> {
    // Spec alignment: similarity between code embedding and spec embedding
    const specAlignment = this.embeddingModel.similarity(
      branch.features.codeEmbedding,
      context.specEmbedding
    );

    // Code quality: based on syntax and type checks
    const codeQuality = this.computeCodeQuality(branch);

    // Novelty: inverse of depth normalized
    const novelty = this.computeNovelty(branch, context);

    // Feasibility: based on complexity and constraints
    const feasibility = this.computeFeasibility(branch, context);

    return {
      specAlignment,
      codeQuality,
      novelty,
      feasibility,
    };
  }

  /**
   * Compute code quality score
   */
  private computeCodeQuality(branch: Branch): number {
    let quality = 0.5; // Base score

    if (branch.features.syntaxValid) {
      quality += 0.25;
    }

    if (branch.features.typeChecks) {
      quality += 0.25;
    }

    // Penalize high complexity
    const complexityPenalty = Math.min(0.3, branch.features.complexity / 100);
    quality -= complexityPenalty;

    return Math.max(0, Math.min(1, quality));
  }

  /**
   * Compute novelty score
   */
  private computeNovelty(branch: Branch, context: SearchContext): number {
    // Base novelty from features
    const baseNovelty = branch.features.novelty;

    // Penalize deep exploration
    const depthPenalty = Math.min(0.5, branch.to.depth / 20);

    // Bonus for different path than history
    const historyBonus = context.history.length > 0 ? 0.1 : 0;

    return Math.max(0, Math.min(1, baseNovelty - depthPenalty + historyBonus));
  }

  /**
   * Compute feasibility score
   */
  private computeFeasibility(branch: Branch, _context: SearchContext): number {
    // Start with spec similarity
    let feasibility = branch.features.specSimilarity;

    // Boost if syntax valid
    if (branch.features.syntaxValid) {
      feasibility += 0.2;
    }

    // Boost if types check
    if (branch.features.typeChecks) {
      feasibility += 0.2;
    }

    return Math.max(0, Math.min(1, feasibility));
  }

  /**
   * Combine component scores with weights
   */
  private combineScores(components: ScoreComponents): number {
    return (
      components.specAlignment * this.weights.specAlignment +
      components.codeQuality * this.weights.codeQuality +
      components.novelty * this.weights.novelty +
      components.feasibility * this.weights.feasibility
    );
  }

  /**
   * Compute confidence in the score
   */
  private computeConfidence(branch: Branch, context: SearchContext): number {
    let confidence = 0.5; // Base confidence

    // Higher confidence for valid code
    if (branch.features.syntaxValid && branch.features.typeChecks) {
      confidence += 0.2;
    }

    // Higher confidence with more history
    if (context.history.length > 0) {
      confidence += Math.min(0.2, context.history.length / 10);
    }

    // Lower confidence for high complexity
    if (branch.features.complexity > 50) {
      confidence -= 0.1;
    }

    return Math.max(0, Math.min(1, confidence));
  }
}
