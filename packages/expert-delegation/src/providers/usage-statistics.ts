/**
 * @nahisaho/musubix-expert-delegation
 * Usage Statistics
 *
 * DES-PRV-002
 * Traces to: REQ-PRV-002
 */

import type { ModelStats } from '../types/index.js';

/**
 * UsageStatisticsを作成するファクトリ関数
 */
export function createUsageStatistics(): UsageStatistics {
  return new UsageStatistics();
}

/**
 * 使用統計管理
 *
 * モデルごとの成功/失敗回数、レイテンシなどを記録する。
 */
export class UsageStatistics {
  private stats: Map<string, ModelStats> = new Map();

  /**
   * 成功を記録
   * @param model - モデルID
   * @param latencyMs - レイテンシ（ミリ秒）
   */
  recordSuccess(model: string, latencyMs: number): void {
    const existing = this.stats.get(model);

    if (existing) {
      const newTotal = existing.totalLatencyMs + latencyMs;
      const newCount = existing.successCount + 1;
      this.stats.set(model, {
        model,
        successCount: newCount,
        failureCount: existing.failureCount,
        totalLatencyMs: newTotal,
        avgLatencyMs: newTotal / newCount,
        lastUsed: new Date(),
      });
    } else {
      this.stats.set(model, {
        model,
        successCount: 1,
        failureCount: 0,
        totalLatencyMs: latencyMs,
        avgLatencyMs: latencyMs,
        lastUsed: new Date(),
      });
    }
  }

  /**
   * 失敗を記録
   * @param model - モデルID
   * @param _error - エラー（将来の分析用）
   */
  recordFailure(model: string, _error: Error): void {
    const existing = this.stats.get(model);

    if (existing) {
      this.stats.set(model, {
        ...existing,
        failureCount: existing.failureCount + 1,
        lastUsed: new Date(),
      });
    } else {
      this.stats.set(model, {
        model,
        successCount: 0,
        failureCount: 1,
        totalLatencyMs: 0,
        avgLatencyMs: 0,
        lastUsed: new Date(),
      });
    }
  }

  /**
   * 全モデルの統計を取得
   */
  getStats(): ModelStats[] {
    return Array.from(this.stats.values());
  }

  /**
   * 特定モデルの統計を取得
   * @param model - モデルID
   */
  getModelStats(model: string): ModelStats | null {
    return this.stats.get(model) ?? null;
  }

  /**
   * 成功率を計算
   * @param model - モデルID
   */
  getSuccessRate(model: string): number {
    const stats = this.stats.get(model);
    if (!stats) {
      return 0;
    }

    const total = stats.successCount + stats.failureCount;
    if (total === 0) {
      return 0;
    }

    return stats.successCount / total;
  }

  /**
   * 最も信頼性の高いモデルを取得
   */
  getMostReliable(): string | null {
    let bestModel: string | null = null;
    let bestScore = -1;

    for (const [model, stats] of this.stats) {
      const total = stats.successCount + stats.failureCount;
      if (total < 3) {
        // 最低3回の使用が必要
        continue;
      }

      const successRate = stats.successCount / total;
      if (successRate > bestScore) {
        bestScore = successRate;
        bestModel = model;
      }
    }

    return bestModel;
  }

  /**
   * 統計をリセット
   */
  reset(): void {
    this.stats.clear();
  }

  /**
   * JSON形式でエクスポート
   */
  toJSON(): Record<string, ModelStats> {
    const result: Record<string, ModelStats> = {};
    for (const [model, stats] of this.stats) {
      result[model] = stats;
    }
    return result;
  }
}
