/**
 * @file candidate-ranker.ts
 * @description CandidateRanker - 複数候補のスコアリングとランキング
 * @requirement REQ-SF-003
 * @design DES-SYMB-001 §4.3
 * @task TSK-SYMB-014
 */

import type { Explanation } from './types.js';

// ============================================================================
// Types
// ============================================================================

/**
 * 候補のメトリクス
 */
export interface CandidateMetrics {
  /** 複雑度スコア (0-100, 低いほど良い) */
  complexity: number;
  /** 保守性スコア (0-100, 高いほど良い) */
  maintainability: number;
  /** 要件カバレッジ (0-100, 高いほど良い) */
  requirementCoverage: number;
  /** lint/型エラー数 (0以上, 低いほど良い) */
  errorCount?: number;
  /** 構造的健全性 (0-100, 高いほど良い) */
  structuralSoundness?: number;
}

/**
 * 候補のスコア内訳
 */
export interface ScoreBreakdown {
  /** メトリクス名 → 正規化スコア (0-1) */
  [metric: string]: number;
}

/**
 * ランキングされた候補
 */
export interface RankedCandidate<T = unknown> {
  /** 候補ID */
  id: string;
  /** 候補データ */
  candidate: T;
  /** 総合スコア (0-100) */
  score: number;
  /** スコア内訳 */
  breakdown: ScoreBreakdown;
  /** 候補の説明 */
  description?: string;
}

/**
 * 候補ランキング結果
 */
export interface CandidateRankingResult<T = unknown> {
  /** ランキングされた候補（降順） */
  rankedCandidates: Array<RankedCandidate<T>>;
  /** 推奨候補 */
  recommended: RankedCandidate<T> | null;
  /** 推奨理由 */
  recommendationReason: string;
  /** 説明 */
  explanation: Explanation;
}

/**
 * 候補入力
 */
export interface CandidateInput<T = unknown> {
  /** 候補ID */
  id: string;
  /** 候補データ */
  candidate: T;
  /** メトリクス */
  metrics: CandidateMetrics;
  /** 候補の説明 */
  description?: string;
}

/**
 * ランカー設定
 */
export interface CandidateRankerConfig {
  /** 複雑度の重み (デフォルト: 0.3) */
  complexityWeight?: number;
  /** 保守性の重み (デフォルト: 0.3) */
  maintainabilityWeight?: number;
  /** 要件カバレッジの重み (デフォルト: 0.4) */
  requirementCoverageWeight?: number;
  /** エラー数の重み (デフォルト: 0.2, 追加メトリクス) */
  errorCountWeight?: number;
  /** 構造的健全性の重み (デフォルト: 0.1, 追加メトリクス) */
  structuralSoundnessWeight?: number;
  /** 最小スコア閾値 (この値未満の候補は除外) */
  minimumScoreThreshold?: number;
}

// ============================================================================
// Constants
// ============================================================================

/**
 * デフォルト設定
 */
export const DEFAULT_RANKER_CONFIG: Required<CandidateRankerConfig> = {
  complexityWeight: 0.3,
  maintainabilityWeight: 0.3,
  requirementCoverageWeight: 0.4,
  errorCountWeight: 0.2,
  structuralSoundnessWeight: 0.1,
  minimumScoreThreshold: 0,
};

// ============================================================================
// CandidateRanker Class
// ============================================================================

/**
 * 候補ランカー
 * @description 複数候補をスコアリングし、推奨候補と内訳を返す
 */
export class CandidateRanker<T = unknown> {
  private readonly config: Required<CandidateRankerConfig>;

  constructor(config: CandidateRankerConfig = {}) {
    this.config = { ...DEFAULT_RANKER_CONFIG, ...config };
  }

  /**
   * 候補をランキングする
   */
  rank(candidates: Array<CandidateInput<T>>): CandidateRankingResult<T> {
    if (candidates.length === 0) {
      return {
        rankedCandidates: [],
        recommended: null,
        recommendationReason: 'No candidates provided',
        explanation: {
          summary: 'No candidates to rank',
          reasoning: ['No input candidates were provided'],
          evidence: [],
          relatedRequirements: [],
        },
      };
    }

    // 各候補をスコアリング
    const rankedCandidates: Array<RankedCandidate<T>> = candidates
      .map((input) => this.scoreCandidate(input))
      .filter((ranked) => ranked.score >= this.config.minimumScoreThreshold)
      .sort((a, b) => b.score - a.score);

    // 推奨候補を決定
    const recommended = rankedCandidates.length > 0 ? rankedCandidates[0] : null;

    // 推奨理由を生成
    const recommendationReason = this.generateRecommendationReason(recommended, rankedCandidates);

    // 説明を生成
    const explanation = this.generateExplanation(rankedCandidates, recommended);

    return {
      rankedCandidates,
      recommended,
      recommendationReason,
      explanation,
    };
  }

  /**
   * 単一候補をスコアリング
   */
  private scoreCandidate(input: CandidateInput<T>): RankedCandidate<T> {
    const breakdown: ScoreBreakdown = {};

    // 複雑度スコア（低いほど良いので反転）
    const normalizedComplexity = 1 - Math.min(input.metrics.complexity / 100, 1);
    breakdown.complexity = normalizedComplexity;

    // 保守性スコア
    const normalizedMaintainability = Math.min(input.metrics.maintainability / 100, 1);
    breakdown.maintainability = normalizedMaintainability;

    // 要件カバレッジスコア
    const normalizedCoverage = Math.min(input.metrics.requirementCoverage / 100, 1);
    breakdown.requirementCoverage = normalizedCoverage;

    // 基本重みの合計
    let totalWeight =
      this.config.complexityWeight +
      this.config.maintainabilityWeight +
      this.config.requirementCoverageWeight;

    // 基本スコア計算
    let weightedScore =
      normalizedComplexity * this.config.complexityWeight +
      normalizedMaintainability * this.config.maintainabilityWeight +
      normalizedCoverage * this.config.requirementCoverageWeight;

    // エラー数（オプション）
    if (input.metrics.errorCount !== undefined) {
      // エラー0-10を1-0にマップ
      const normalizedErrorScore = Math.max(0, 1 - input.metrics.errorCount / 10);
      breakdown.errorCount = normalizedErrorScore;
      weightedScore += normalizedErrorScore * this.config.errorCountWeight;
      totalWeight += this.config.errorCountWeight;
    }

    // 構造的健全性（オプション）
    if (input.metrics.structuralSoundness !== undefined) {
      const normalizedSoundness = Math.min(input.metrics.structuralSoundness / 100, 1);
      breakdown.structuralSoundness = normalizedSoundness;
      weightedScore += normalizedSoundness * this.config.structuralSoundnessWeight;
      totalWeight += this.config.structuralSoundnessWeight;
    }

    // 正規化して0-100スコアに変換
    const score = Math.round((weightedScore / totalWeight) * 100);

    return {
      id: input.id,
      candidate: input.candidate,
      score,
      breakdown,
      description: input.description,
    };
  }

  /**
   * 推奨理由を生成
   */
  private generateRecommendationReason(
    recommended: RankedCandidate<T> | null,
    allCandidates: Array<RankedCandidate<T>>,
  ): string {
    if (!recommended) {
      return 'No candidates met the minimum score threshold';
    }

    const reasons: string[] = [];

    // 最高スコアの理由
    reasons.push(`Highest overall score: ${recommended.score}/100`);

    // 強みを特定
    const breakdown = recommended.breakdown;
    const strengths: string[] = [];

    if (breakdown.complexity >= 0.7) {
      strengths.push('low complexity');
    }
    if (breakdown.maintainability >= 0.7) {
      strengths.push('high maintainability');
    }
    if (breakdown.requirementCoverage >= 0.7) {
      strengths.push('good requirement coverage');
    }
    if (breakdown.errorCount !== undefined && breakdown.errorCount >= 0.9) {
      strengths.push('minimal errors');
    }

    if (strengths.length > 0) {
      reasons.push(`Key strengths: ${strengths.join(', ')}`);
    }

    // 比較情報
    if (allCandidates.length > 1) {
      const secondBest = allCandidates[1];
      const scoreDiff = recommended.score - secondBest.score;
      if (scoreDiff > 10) {
        reasons.push(`Significantly better than second choice (+${scoreDiff} points)`);
      } else if (scoreDiff > 0) {
        reasons.push(`Marginally better than second choice (+${scoreDiff} points)`);
      }
    }

    return reasons.join('. ');
  }

  /**
   * 説明を生成
   */
  private generateExplanation(
    rankedCandidates: Array<RankedCandidate<T>>,
    recommended: RankedCandidate<T> | null,
  ): Explanation {
    const reasoning: string[] = [];

    // ランキングプロセスの説明
    reasoning.push(`Evaluated ${rankedCandidates.length} candidate(s) using weighted scoring`);
    reasoning.push(
      `Weights: complexity=${this.config.complexityWeight}, maintainability=${this.config.maintainabilityWeight}, coverage=${this.config.requirementCoverageWeight}`,
    );

    // 各候補の評価概要
    for (const candidate of rankedCandidates.slice(0, 3)) {
      reasoning.push(
        `${candidate.id}: score=${candidate.score}, complexity=${(candidate.breakdown.complexity * 100).toFixed(0)}%, maintainability=${(candidate.breakdown.maintainability * 100).toFixed(0)}%`,
      );
    }

    // 推奨根拠
    if (recommended) {
      reasoning.push(`Recommended: ${recommended.id} based on highest weighted score`);
    }

    return {
      summary: recommended
        ? `Recommended candidate: ${recommended.id} with score ${recommended.score}/100`
        : 'No candidate recommended',
      reasoning,
      evidence: rankedCandidates.map((c) => ({
        type: 'code' as const,
        content: JSON.stringify(c.breakdown),
        source: c.id,
        confidence: c.score / 100,
      })),
      relatedRequirements: [],
    };
  }

  /**
   * 設定を取得
   */
  getConfig(): Required<CandidateRankerConfig> {
    return { ...this.config };
  }

  /**
   * 重み付けを更新
   */
  updateWeights(weights: Partial<CandidateRankerConfig>): void {
    Object.assign(this.config, weights);
  }
}

// ============================================================================
// Factory Functions
// ============================================================================

/**
 * CandidateRankerを作成
 */
export function createCandidateRanker<T = unknown>(
  config?: CandidateRankerConfig,
): CandidateRanker<T> {
  return new CandidateRanker<T>(config);
}

/**
 * メトリクスからスコアを直接計算（静的関数）
 */
export function calculateScore(
  metrics: CandidateMetrics,
  config: CandidateRankerConfig = {},
): number {
  const ranker = new CandidateRanker(config);
  const result = ranker.rank([
    {
      id: 'temp',
      candidate: null,
      metrics,
    },
  ]);
  return result.recommended?.score ?? 0;
}
