/**
 * ContextAwareScorer - Project Context-Aware Branch Scoring
 * @module @nahisaho/musubix-neural-search
 * @see TSK-NS-103
 * @see DES-NS-103
 * @see REQ-NS-103
 *
 * プロジェクトコンテキストを30%以上の重みで反映するスコアラー
 * - プロジェクトパターンの検出
 * - コードベース埋め込みとの類似度
 * - 詳細なスコア内訳の提供
 */

import type {
  Branch,
  BranchScore,
  Embedding,
  IBranchScorer,
  ScoreFeedback,
  SearchContext,
} from '../types.js';
import { BranchScorer, type ScoreWeights } from './BranchScorer.js';

// =============================================================================
// Types
// =============================================================================

/**
 * Configuration for ContextAwareScorer
 */
export interface ContextAwareScorerConfig {
  /** Weight for project context (0-1, default: 0.3, minimum: 0.3) */
  contextWeight?: number;
  /** Enable project context scoring (default: true) */
  enableProjectContext?: boolean;
  /** Base scorer weights */
  baseWeights?: Partial<ScoreWeights>;
  /** Pattern match bonus (default: 0.1) */
  patternMatchBonus?: number;
}

/**
 * Project context for scoring
 */
export interface ProjectContext {
  /** Project name */
  projectName: string;
  /** Primary language */
  language: string;
  /** Common patterns in the project */
  patterns: string[];
  /** Embedding representing the codebase */
  codebaseEmbedding: Embedding;
  /** Recently modified files */
  recentFiles: string[];
  /** Optional: domain-specific keywords */
  domainKeywords?: string[];
}

/**
 * Score breakdown details
 */
export interface ScoreBreakdown {
  /** Base score from standard components */
  baseScore: number;
  /** Score from project context */
  contextScore: number;
  /** Weight applied to context */
  contextWeight: number;
  /** Final combined score */
  finalScore: number;
  /** Pattern matches found */
  patternMatches?: string[];
}

/**
 * Scoring statistics
 */
export interface ScoringStatistics {
  /** Total branches scored */
  totalScored: number;
  /** Average score */
  averageScore: number;
  /** Average confidence */
  averageConfidence: number;
  /** Context contribution average */
  averageContextContribution: number;
}

/**
 * Extended BranchScore with context information
 */
interface ExtendedBranchScore extends BranchScore {
  _contextScore?: number;
  _baseScore?: number;
}

/**
 * ContextAwareScorer interface
 */
export interface ContextAwareScorer extends IBranchScorer {
  /** Set project context */
  setProjectContext(context: ProjectContext): void;
  /** Get score breakdown */
  getScoreBreakdown(score: BranchScore): ScoreBreakdown;
  /** Get statistics */
  getStatistics(): ScoringStatistics;
  /** Reset statistics */
  resetStatistics(): void;
  /** Serialize to JSON */
  toJSON(): string;
  /** Deserialize from JSON */
  fromJSON(json: string): void;
}

// =============================================================================
// Implementation
// =============================================================================

/**
 * Default ContextAwareScorer implementation
 */
export class DefaultContextAwareScorer implements ContextAwareScorer {
  private config: Required<ContextAwareScorerConfig>;
  private baseScorer: BranchScorer;
  private projectContext: ProjectContext | null = null;
  private feedbackHistory: Map<string, ScoreFeedback[]> = new Map();

  // Statistics
  private totalScored = 0;
  private scoreSum = 0;
  private confidenceSum = 0;
  private contextContributionSum = 0;

  // Cache for breakdowns
  private breakdownCache: WeakMap<BranchScore, ScoreBreakdown> = new WeakMap();

  constructor(config: ContextAwareScorerConfig = {}) {
    // Ensure context weight is at least 30%
    const contextWeight = Math.max(config.contextWeight ?? 0.3, 0.3);

    this.config = {
      contextWeight,
      enableProjectContext: config.enableProjectContext ?? true,
      baseWeights: config.baseWeights ?? {},
      patternMatchBonus: config.patternMatchBonus ?? 0.1,
    };

    this.baseScorer = new BranchScorer(undefined, this.config.baseWeights);
  }

  // =========================================================================
  // IBranchScorer Implementation
  // =========================================================================

  async score(branch: Branch, context: SearchContext): Promise<BranchScore> {
    // Get base score
    const baseResult = await this.baseScorer.score(branch, context);
    const baseScore = baseResult.score;

    // Compute context score
    const contextScore = this.computeContextScore(branch, context);

    // Combine scores
    const effectiveContextWeight = this.config.enableProjectContext
      ? this.config.contextWeight
      : 0;

    const finalScore =
      baseScore * (1 - effectiveContextWeight) +
      contextScore * effectiveContextWeight;

    // Update statistics
    this.updateStatistics(finalScore, baseResult.confidence, contextScore * effectiveContextWeight);

    // Create result
    const result: ExtendedBranchScore = {
      branch,
      score: finalScore,
      confidence: baseResult.confidence,
      components: baseResult.components,
      _contextScore: contextScore,
      _baseScore: baseScore,
    };

    // Cache breakdown
    this.breakdownCache.set(result, {
      baseScore,
      contextScore,
      contextWeight: effectiveContextWeight,
      finalScore,
      patternMatches: this.findPatternMatches(branch),
    });

    return result;
  }

  async scoreBatch(
    branches: Branch[],
    context: SearchContext
  ): Promise<BranchScore[]> {
    return Promise.all(branches.map((branch) => this.score(branch, context)));
  }

  update(feedback: ScoreFeedback): void {
    const history = this.feedbackHistory.get(feedback.branchId) ?? [];
    history.push(feedback);
    this.feedbackHistory.set(feedback.branchId, history);

    // Also update base scorer
    this.baseScorer.update(feedback);
  }

  // =========================================================================
  // Project Context
  // =========================================================================

  setProjectContext(context: ProjectContext): void {
    this.projectContext = context;
  }

  // =========================================================================
  // Score Breakdown
  // =========================================================================

  getScoreBreakdown(score: BranchScore): ScoreBreakdown {
    // Check cache
    const cached = this.breakdownCache.get(score);
    if (cached) {
      return cached;
    }

    // Reconstruct breakdown if not cached
    const extendedScore = score as ExtendedBranchScore;
    const baseScore = extendedScore._baseScore ?? score.score;
    const contextScore = extendedScore._contextScore ?? 0;
    const contextWeight = this.config.enableProjectContext
      ? this.config.contextWeight
      : 0;

    return {
      baseScore,
      contextScore,
      contextWeight,
      finalScore: score.score,
    };
  }

  // =========================================================================
  // Statistics
  // =========================================================================

  getStatistics(): ScoringStatistics {
    return {
      totalScored: this.totalScored,
      averageScore: this.totalScored > 0 ? this.scoreSum / this.totalScored : 0,
      averageConfidence:
        this.totalScored > 0 ? this.confidenceSum / this.totalScored : 0,
      averageContextContribution:
        this.totalScored > 0
          ? this.contextContributionSum / this.totalScored
          : 0,
    };
  }

  resetStatistics(): void {
    this.totalScored = 0;
    this.scoreSum = 0;
    this.confidenceSum = 0;
    this.contextContributionSum = 0;
  }

  // =========================================================================
  // Serialization
  // =========================================================================

  toJSON(): string {
    return JSON.stringify({
      config: {
        contextWeight: this.config.contextWeight,
        enableProjectContext: this.config.enableProjectContext,
        patternMatchBonus: this.config.patternMatchBonus,
      },
      statistics: this.getStatistics(),
      projectContext: this.projectContext
        ? {
            projectName: this.projectContext.projectName,
            language: this.projectContext.language,
            patterns: this.projectContext.patterns,
          }
        : null,
    });
  }

  fromJSON(json: string): void {
    const data = JSON.parse(json);

    if (data.config) {
      if (data.config.contextWeight !== undefined) {
        this.config.contextWeight = Math.max(data.config.contextWeight, 0.3);
      }
      if (data.config.enableProjectContext !== undefined) {
        this.config.enableProjectContext = data.config.enableProjectContext;
      }
      if (data.config.patternMatchBonus !== undefined) {
        this.config.patternMatchBonus = data.config.patternMatchBonus;
      }
    }

    if (data.statistics) {
      this.totalScored = data.statistics.totalScored ?? 0;
      this.scoreSum =
        (data.statistics.averageScore ?? 0) * this.totalScored;
      this.confidenceSum =
        (data.statistics.averageConfidence ?? 0) * this.totalScored;
      this.contextContributionSum =
        (data.statistics.averageContextContribution ?? 0) * this.totalScored;
    }
  }

  // =========================================================================
  // Private Methods
  // =========================================================================

  private computeContextScore(branch: Branch, context: SearchContext): number {
    if (!this.config.enableProjectContext || !this.projectContext) {
      return 0.5; // Neutral score when no context
    }

    let score = 0.5; // Base

    // Pattern matching bonus
    const patternMatches = this.findPatternMatches(branch);
    if (patternMatches.length > 0) {
      score += this.config.patternMatchBonus * patternMatches.length;
    }

    // Codebase embedding similarity
    if (this.projectContext.codebaseEmbedding) {
      const similarity = this.cosineSimilarity(
        branch.features.codeEmbedding,
        this.projectContext.codebaseEmbedding
      );
      score += similarity * 0.2;
    }

    // Language alignment
    if (this.isLanguageAligned(branch, context)) {
      score += 0.1;
    }

    // Domain keyword matching
    if (this.projectContext.domainKeywords) {
      const keywordScore = this.computeKeywordScore(branch, context);
      score += keywordScore * 0.1;
    }

    // Clamp to [0, 1]
    return Math.max(0, Math.min(1, score));
  }

  private findPatternMatches(branch: Branch): string[] {
    if (!this.projectContext) {
      return [];
    }

    const matches: string[] = [];
    const action = branch.action.toLowerCase();

    for (const pattern of this.projectContext.patterns) {
      if (action.includes(pattern.toLowerCase()) || 
          pattern.toLowerCase().includes(action)) {
        matches.push(pattern);
      }
    }

    return matches;
  }

  private cosineSimilarity(a: Embedding, b: Embedding): number {
    if (a.length !== b.length || a.length === 0) {
      return 0;
    }

    let dotProduct = 0;
    let normA = 0;
    let normB = 0;

    for (let i = 0; i < a.length; i++) {
      dotProduct += a[i] * b[i];
      normA += a[i] * a[i];
      normB += b[i] * b[i];
    }

    const denominator = Math.sqrt(normA) * Math.sqrt(normB);
    if (denominator === 0) {
      return 0;
    }

    return dotProduct / denominator;
  }

  private isLanguageAligned(_branch: Branch, _context: SearchContext): boolean {
    if (!this.projectContext) {
      return false;
    }

    // Simple heuristic: assume TypeScript/JavaScript projects
    const lang = this.projectContext.language.toLowerCase();
    return lang === 'typescript' || lang === 'javascript';
  }

  private computeKeywordScore(branch: Branch, _context: SearchContext): number {
    if (!this.projectContext?.domainKeywords) {
      return 0;
    }

    const code = branch.to.code.toLowerCase();
    let matches = 0;

    for (const keyword of this.projectContext.domainKeywords) {
      if (code.includes(keyword.toLowerCase())) {
        matches++;
      }
    }

    return Math.min(1, matches / Math.max(1, this.projectContext.domainKeywords.length));
  }

  private updateStatistics(
    score: number,
    confidence: number,
    contextContribution: number
  ): void {
    this.totalScored++;
    this.scoreSum += score;
    this.confidenceSum += confidence;
    this.contextContributionSum += contextContribution;
  }
}

// =============================================================================
// Factory Function
// =============================================================================

/**
 * Create a ContextAwareScorer instance
 * @param config - Optional configuration
 * @returns ContextAwareScorer instance
 */
export function createContextAwareScorer(
  config: ContextAwareScorerConfig = {}
): ContextAwareScorer {
  return new DefaultContextAwareScorer(config);
}
