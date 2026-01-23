/**
 * PatternLearningDB - パターン学習データベース
 *
 * @description
 * 学習済みパターンの永続化・検索・管理を提供する。
 * GLOBALレイヤーでメトリクス連携し、パターン適用の追跡を行う。
 *
 * @see DES-PATTERN-001 - パターン学習システム
 * @see TSK-FR-038 - PatternLearningDBインターフェース定義
 * @see TSK-FR-039 - add/get/update実装
 * @see TSK-FR-040 - query実装
 * @see TSK-FR-041 - recordUsage実装
 * @trace REQ-FR-004 - 継続的学習
 */

import type {
  LearnedPattern,
  LearnedPatternInput,
  PatternQuery,
  PatternLearningStats,
  PatternLearningDBConfig,
} from './db-types.js';

import {
  createLearnedPattern,
  calculatePatternStats,
  DEFAULT_PATTERN_LEARNING_CONFIG,
} from './db-types.js';

/**
 * PatternLearningDBインターフェース
 *
 * @trace DES-PATTERN-001
 */
export interface IPatternLearningDB {
  /**
   * パターンを追加
   */
  add(input: LearnedPatternInput): Promise<LearnedPattern>;

  /**
   * IDでパターンを取得
   */
  get(id: string): Promise<LearnedPattern | null>;

  /**
   * パターンを更新
   */
  update(id: string, updates: Partial<Pick<LearnedPattern, 'status' | 'confidence' | 'metadata'>>): Promise<LearnedPattern | null>;

  /**
   * パターンを削除
   */
  delete(id: string): Promise<boolean>;

  /**
   * パターンを検索
   */
  query(query: PatternQuery): Promise<readonly LearnedPattern[]>;

  /**
   * 全パターンを取得
   */
  list(): Promise<readonly LearnedPattern[]>;

  /**
   * パターン使用を記録
   */
  recordUsage(id: string): Promise<void>;

  /**
   * 統計を取得
   */
  getStats(): Promise<PatternLearningStats>;

  /**
   * 全パターンをクリア
   */
  clear(): Promise<void>;
}

/**
 * PatternLearningDB実装
 *
 * @trace DES-PATTERN-001
 */
export class PatternLearningDB implements IPatternLearningDB {
  private readonly patterns: Map<string, LearnedPattern> = new Map();
  private readonly config: PatternLearningDBConfig;

  constructor(config: PatternLearningDBConfig = DEFAULT_PATTERN_LEARNING_CONFIG) {
    this.config = config;
  }

  /**
   * @trace TSK-FR-039
   */
  async add(input: LearnedPatternInput): Promise<LearnedPattern> {
    // 最大パターン数を超えた場合、最も古いものを削除
    while (this.patterns.size >= this.config.maxPatterns) {
      const oldest = this.findOldestPattern();
      if (oldest) {
        this.patterns.delete(oldest.id);
      }
    }

    const learned = createLearnedPattern(input);
    this.patterns.set(learned.id, learned);
    return learned;
  }

  /**
   * @trace TSK-FR-039
   */
  async get(id: string): Promise<LearnedPattern | null> {
    return this.patterns.get(id) ?? null;
  }

  /**
   * @trace TSK-FR-039
   */
  async update(
    id: string,
    updates: Partial<Pick<LearnedPattern, 'status' | 'confidence' | 'metadata'>>
  ): Promise<LearnedPattern | null> {
    const existing = this.patterns.get(id);
    if (!existing) {
      return null;
    }

    const updated: LearnedPattern = Object.freeze({
      ...existing,
      ...updates,
      updatedAt: Date.now(),
    });

    this.patterns.set(id, updated);
    return updated;
  }

  async delete(id: string): Promise<boolean> {
    return this.patterns.delete(id);
  }

  /**
   * @trace TSK-FR-040
   */
  async query(query: PatternQuery): Promise<readonly LearnedPattern[]> {
    let results = Array.from(this.patterns.values());

    // ステータスフィルター
    if (query.status) {
      const statuses = Array.isArray(query.status) ? query.status : [query.status];
      results = results.filter(p => statuses.includes(p.status));
    }

    // ソースフィルター
    if (query.source) {
      const sources = Array.isArray(query.source) ? query.source : [query.source];
      results = results.filter(p => sources.includes(p.source));
    }

    // 信頼度フィルター
    if (query.minConfidence !== undefined) {
      results = results.filter(p => p.confidence >= query.minConfidence!);
    }
    if (query.maxConfidence !== undefined) {
      results = results.filter(p => p.confidence <= query.maxConfidence!);
    }

    // カテゴリフィルター（DesignPatternの場合）
    if (query.category) {
      results = results.filter(p => {
        const pattern = p.pattern as any;
        return pattern.category === query.category;
      });
    }

    // ドメインフィルター（DesignPatternの場合）
    if (query.domain) {
      results = results.filter(p => {
        const pattern = p.pattern as any;
        return pattern.domain?.includes(query.domain);
      });
    }

    // ソート
    if (query.sortBy) {
      const order = query.sortOrder === 'desc' ? -1 : 1;
      results.sort((a, b) => {
        const aVal = a[query.sortBy!];
        const bVal = b[query.sortBy!];
        if (typeof aVal === 'number' && typeof bVal === 'number') {
          return (aVal - bVal) * order;
        }
        return 0;
      });
    }

    // ページネーション
    const offset = query.offset ?? 0;
    const limit = query.limit ?? results.length;
    results = results.slice(offset, offset + limit);

    return Object.freeze(results);
  }

  async list(): Promise<readonly LearnedPattern[]> {
    return Object.freeze(Array.from(this.patterns.values()));
  }

  /**
   * @trace TSK-FR-041
   */
  async recordUsage(id: string): Promise<void> {
    const existing = this.patterns.get(id);
    if (!existing) {
      return;
    }

    const updated: LearnedPattern = Object.freeze({
      ...existing,
      usageCount: existing.usageCount + 1,
      lastUsedAt: Date.now(),
      updatedAt: Date.now(),
    });

    this.patterns.set(id, updated);
  }

  async getStats(): Promise<PatternLearningStats> {
    return calculatePatternStats(Array.from(this.patterns.values()));
  }

  async clear(): Promise<void> {
    this.patterns.clear();
  }

  private findOldestPattern(): LearnedPattern | null {
    let oldest: LearnedPattern | null = null;
    for (const pattern of this.patterns.values()) {
      if (!oldest || pattern.createdAt < oldest.createdAt) {
        oldest = pattern;
      }
    }
    return oldest;
  }
}

/**
 * ファクトリ関数
 *
 * @trace TSK-FR-038
 */
export function createPatternLearningDB(config?: PatternLearningDBConfig): IPatternLearningDB {
  return new PatternLearningDB(config);
}
