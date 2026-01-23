/**
 * MetricsCollector - 実行時メトリクス収集システム
 *
 * @description
 * ワークフロー実行中のメトリクスを収集・集計し、
 * GLOBALレイヤーへのレポーティングを提供する。
 *
 * @see DES-CORE-001 - メトリクス収集システム
 * @see TSK-FR-033 - MetricsCollectorインターフェース定義
 * @see TSK-FR-034 - collect()実装
 * @see TSK-FR-035 - aggregate()実装
 * @see TSK-FR-036 - export()実装
 * @trace REQ-FR-003 - ワークフロー最適化
 */

import type {
  Metric,
  MetricInput,
  MetricType,
  MetricCategory,
  MetricTimeSeries,
  MetricsReport,
  MetricsSummary,
  MetricsConfig,
} from './types.js';

import { createMetric, calculateStats, DEFAULT_METRICS_CONFIG } from './types.js';

/**
 * メトリクスコレクターインターフェース
 *
 * @trace DES-CORE-001
 */
export interface IMetricsCollector {
  /**
   * メトリクスを収集
   */
  collect(input: MetricInput): void;

  /**
   * カウンターをインクリメント
   */
  increment(name: string, category: MetricCategory, value?: number, labels?: Record<string, string>): void;

  /**
   * ゲージ値を設定
   */
  gauge(name: string, category: MetricCategory, value: number, labels?: Record<string, string>): void;

  /**
   * タイマー値を記録
   */
  timer(name: string, category: MetricCategory, durationMs?: number, labels?: Record<string, string>): void;

  /**
   * メトリクスを集計
   */
  aggregate(name: string, windowMs?: number): Promise<MetricTimeSeries>;

  /**
   * メトリクスレポートをエクスポート
   */
  export(): Promise<MetricsReport>;

  /**
   * フェーズ開始イベント
   */
  onPhaseStart(workflowId: string, phase?: string): void;

  /**
   * フェーズ終了イベント
   */
  onPhaseEnd(workflowId: string, durationMs: number): void;

  /**
   * エラーイベント
   */
  onError(workflowId: string, error: Error): void;

  /**
   * 全メトリクスを取得
   */
  getMetrics(): readonly Metric[];

  /**
   * カテゴリ別メトリクスを取得
   */
  getMetricsByCategory(category: MetricCategory): readonly Metric[];

  /**
   * メトリクスをクリア
   */
  clear(): void;
}

/**
 * MetricsCollector実装
 *
 * @trace DES-CORE-001
 */
export class MetricsCollector implements IMetricsCollector {
  private readonly metrics: Metric[] = [];
  private readonly config: MetricsConfig;
  private startTime: number;

  constructor(config: MetricsConfig = DEFAULT_METRICS_CONFIG) {
    this.config = config;
    this.startTime = Date.now();
  }

  /**
   * @trace TSK-FR-034
   */
  collect(input: MetricInput): void {
    // 最大メトリクス数を超えた場合、古いものを削除
    while (this.metrics.length >= this.config.maxMetrics) {
      this.metrics.shift();
    }

    const metric = createMetric(input);
    this.metrics.push(metric);
  }

  increment(name: string, category: MetricCategory, value: number = 1, labels?: Record<string, string>): void {
    this.collect({
      name,
      type: 'counter',
      category,
      value,
      labels,
    });
  }

  gauge(name: string, category: MetricCategory, value: number, labels?: Record<string, string>): void {
    this.collect({
      name,
      type: 'gauge',
      category,
      value,
      labels,
    });
  }

  timer(name: string, category: MetricCategory, durationMs: number = 0, labels?: Record<string, string>): void {
    this.collect({
      name,
      type: 'timer',
      category,
      value: durationMs,
      unit: 'ms',
      labels,
    });
  }

  /**
   * @trace TSK-FR-035
   */
  async aggregate(name: string, windowMs?: number): Promise<MetricTimeSeries> {
    const now = Date.now();
    const cutoff = windowMs ? now - windowMs : 0;

    const filtered = this.metrics.filter(
      m => m.name === name && m.timestamp >= cutoff
    );

    const stats = calculateStats(filtered);

    // type/categoryは最初のメトリクスから取得、なければdefault
    const firstMetric = filtered[0];
    const type = firstMetric?.type ?? 'gauge';
    const category = firstMetric?.category ?? 'custom';

    return Object.freeze({
      name,
      type,
      category,
      dataPoints: filtered,
      stats,
      startTime: filtered.length > 0 ? filtered[0].timestamp : now,
      endTime: filtered.length > 0 ? filtered[filtered.length - 1].timestamp : now,
    });
  }

  /**
   * @trace TSK-FR-036
   */
  async export(): Promise<MetricsReport> {
    const now = Date.now();

    // カテゴリごとに集計
    const names = [...new Set(this.metrics.map(m => m.name))];

    const series: MetricTimeSeries[] = [];
    for (const name of names) {
      series.push(await this.aggregate(name));
    }

    // カテゴリ別カウント
    const byCategory: Record<MetricCategory, number> = {
      workflow: 0,
      phase: 0,
      gate: 0,
      resource: 0,
      error: 0,
      performance: 0,
      custom: 0,
    };

    for (const metric of this.metrics) {
      byCategory[metric.category]++;
    }

    // 型別カウント
    const byType: Record<MetricType, number> = {
      counter: 0,
      gauge: 0,
      histogram: 0,
      timer: 0,
      rate: 0,
    };

    for (const metric of this.metrics) {
      byType[metric.type]++;
    }

    // ヘルスステータス判定
    const errorRate = this.metrics.length > 0
      ? byCategory.error / this.metrics.length
      : 0;

    let healthStatus: 'healthy' | 'warning' | 'critical';
    if (errorRate < 0.01) {
      healthStatus = 'healthy';
    } else if (errorRate < 0.05) {
      healthStatus = 'warning';
    } else {
      healthStatus = 'critical';
    }

    const summary: MetricsSummary = Object.freeze({
      totalMetrics: this.metrics.length,
      byCategory,
      byType,
      healthStatus,
    });

    return Object.freeze({
      generatedAt: now,
      summary,
      series,
      startTime: this.startTime,
      endTime: now,
      durationMs: now - this.startTime,
    });
  }

  onPhaseStart(workflowId: string, phase: string = 'unknown'): void {
    this.collect({
      name: 'phase.started',
      type: 'counter',
      category: 'phase',
      value: 1,
      labels: { workflowId, phase },
    });
  }

  onPhaseEnd(workflowId: string, durationMs: number): void {
    this.collect({
      name: 'phase.duration',
      type: 'timer',
      category: 'phase',
      value: durationMs,
      unit: 'ms',
      labels: { workflowId },
    });
  }

  onError(workflowId: string, error: Error): void {
    this.collect({
      name: 'workflow.error',
      type: 'counter',
      category: 'error',
      value: 1,
      labels: { workflowId },
      metadata: { errorMessage: error.message, errorName: error.name },
    });
  }

  getMetrics(): readonly Metric[] {
    return Object.freeze([...this.metrics]);
  }

  getMetricsByCategory(category: MetricCategory): readonly Metric[] {
    return Object.freeze(this.metrics.filter(m => m.category === category));
  }

  clear(): void {
    this.metrics.length = 0;
    this.startTime = Date.now();
  }
}

/**
 * ファクトリ関数
 *
 * @trace TSK-FR-033
 */
export function createMetricsCollector(config?: MetricsConfig): IMetricsCollector {
  return new MetricsCollector(config);
}
