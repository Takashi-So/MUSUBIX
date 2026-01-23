/**
 * PatternLearningDB Types
 *
 * @description
 * パターン学習データベースの型定義
 *
 * @see TSK-FR-038 - PatternLearningDB型定義
 * @see REQ-FR-036〜040 - PatternLearningDB
 * @trace DES-MUSUBIX-FR-001 DES-PATTERN-001
 */

import type { Pattern, DesignPattern, PatternExample } from '../types.js';

/**
 * 学習済みパターンの状態
 */
export type PatternStatus =
  | 'candidate'   // 候補パターン（未検証）
  | 'verified'    // 検証済み
  | 'deprecated'  // 非推奨
  | 'archived';   // アーカイブ済み

/**
 * パターン学習のソース
 */
export type LearningSource =
  | 'code-observation'  // コード観察から抽出
  | 'feedback'          // フィードバックから抽出
  | 'manual'            // 手動登録
  | 'imported';         // インポート

/**
 * 学習済みパターンエントリ
 */
export interface LearnedPattern {
  readonly id: string;
  readonly pattern: Pattern | DesignPattern;
  readonly source: LearningSource;
  readonly status: PatternStatus;
  readonly confidence: number;
  readonly usageCount: number;
  readonly lastUsedAt: number | null;
  readonly createdAt: number;
  readonly updatedAt: number;
  readonly examples: readonly PatternExample[];
  readonly metadata?: Readonly<Record<string, unknown>>;
}

/**
 * パターン学習入力
 */
export interface LearnedPatternInput {
  readonly pattern: Pattern | DesignPattern;
  readonly source: LearningSource;
  readonly confidence?: number;
  readonly examples?: readonly PatternExample[];
  readonly metadata?: Record<string, unknown>;
}

/**
 * パターン検索クエリ
 */
export interface PatternQuery {
  readonly status?: PatternStatus | readonly PatternStatus[];
  readonly source?: LearningSource | readonly LearningSource[];
  readonly minConfidence?: number;
  readonly maxConfidence?: number;
  readonly category?: string;
  readonly domain?: string;
  readonly limit?: number;
  readonly offset?: number;
  readonly sortBy?: 'confidence' | 'usageCount' | 'createdAt' | 'updatedAt';
  readonly sortOrder?: 'asc' | 'desc';
}

/**
 * パターン学習統計
 */
export interface PatternLearningStats {
  readonly totalPatterns: number;
  readonly byStatus: Readonly<Record<PatternStatus, number>>;
  readonly bySource: Readonly<Record<LearningSource, number>>;
  readonly avgConfidence: number;
  readonly totalUsage: number;
  readonly healthStatus: 'healthy' | 'warning' | 'critical';
}

/**
 * パターン学習DBの設定
 */
export interface PatternLearningDBConfig {
  readonly maxPatterns: number;
  readonly minConfidenceThreshold: number;
  readonly autoDeprecateAfterDays: number;
  readonly enableAutoCleanup: boolean;
}

/**
 * デフォルト設定
 */
export const DEFAULT_PATTERN_LEARNING_CONFIG: PatternLearningDBConfig = Object.freeze({
  maxPatterns: 10000,
  minConfidenceThreshold: 0.3,
  autoDeprecateAfterDays: 90,
  enableAutoCleanup: true,
});

// IDカウンター
let patternIdCounter = 0;

/**
 * IDカウンターをリセット（テスト用）
 */
export function resetPatternIdCounter(): void {
  patternIdCounter = 0;
}

/**
 * LearnedPatternを作成
 */
export function createLearnedPattern(input: LearnedPatternInput): LearnedPattern {
  patternIdCounter++;
  const id = `LP-${String(patternIdCounter).padStart(5, '0')}`;
  const now = Date.now();

  return Object.freeze({
    id,
    pattern: input.pattern,
    source: input.source,
    status: 'candidate' as PatternStatus,
    confidence: input.confidence ?? 0.5,
    usageCount: 0,
    lastUsedAt: null,
    createdAt: now,
    updatedAt: now,
    examples: Object.freeze(input.examples ?? []),
    metadata: input.metadata ? Object.freeze(input.metadata) : undefined,
  });
}

/**
 * パターン学習統計を計算
 */
export function calculatePatternStats(patterns: readonly LearnedPattern[]): PatternLearningStats {
  const byStatus: Record<PatternStatus, number> = {
    candidate: 0,
    verified: 0,
    deprecated: 0,
    archived: 0,
  };

  const bySource: Record<LearningSource, number> = {
    'code-observation': 0,
    'feedback': 0,
    'manual': 0,
    'imported': 0,
  };

  let totalConfidence = 0;
  let totalUsage = 0;

  for (const p of patterns) {
    byStatus[p.status]++;
    bySource[p.source]++;
    totalConfidence += p.confidence;
    totalUsage += p.usageCount;
  }

  const avgConfidence = patterns.length > 0 ? totalConfidence / patterns.length : 0;

  // ヘルスステータス判定
  let healthStatus: 'healthy' | 'warning' | 'critical';
  const deprecatedRatio = patterns.length > 0 ? byStatus.deprecated / patterns.length : 0;

  if (deprecatedRatio < 0.1 && avgConfidence >= 0.6) {
    healthStatus = 'healthy';
  } else if (deprecatedRatio < 0.3 && avgConfidence >= 0.4) {
    healthStatus = 'warning';
  } else {
    healthStatus = 'critical';
  }

  return Object.freeze({
    totalPatterns: patterns.length,
    byStatus: Object.freeze(byStatus),
    bySource: Object.freeze(bySource),
    avgConfidence,
    totalUsage,
    healthStatus,
  });
}
