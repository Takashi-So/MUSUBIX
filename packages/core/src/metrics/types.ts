/**
 * MetricsCollector Types
 *
 * Defines types for collecting and aggregating metrics
 * throughout the SDD workflow.
 *
 * @see TSK-FR-033 - MetricsCollector型定義
 * @see REQ-FR-030〜032 - MetricsCollector
 * @trace DES-MUSUBIX-FR-001 DES-CORE-001
 */

/**
 * Metric type categories
 */
export type MetricType =
  | 'counter'     // Incremental count
  | 'gauge'       // Current value
  | 'histogram'   // Distribution of values
  | 'timer'       // Duration measurements
  | 'rate';       // Rate per time period

/**
 * Metric category for grouping
 */
export type MetricCategory =
  | 'workflow'    // Workflow-level metrics
  | 'phase'       // Phase-level metrics
  | 'gate'        // Quality gate metrics
  | 'resource'    // Resource usage metrics
  | 'error'       // Error metrics
  | 'performance' // Performance metrics
  | 'custom';     // User-defined metrics

/**
 * Single metric data point
 */
export interface Metric {
  readonly id: string;
  readonly name: string;
  readonly type: MetricType;
  readonly category: MetricCategory;
  readonly value: number;
  readonly unit?: string;
  readonly timestamp: number;
  readonly labels?: Readonly<Record<string, string>>;
  readonly metadata?: Readonly<Record<string, unknown>>;
}

/**
 * Metric input for creating metrics
 */
export interface MetricInput {
  readonly name: string;
  readonly type: MetricType;
  readonly category: MetricCategory;
  readonly value: number;
  readonly unit?: string;
  readonly labels?: Record<string, string>;
  readonly metadata?: Record<string, unknown>;
}

/**
 * Aggregated metric statistics
 */
export interface MetricStats {
  readonly count: number;
  readonly sum: number;
  readonly min: number;
  readonly max: number;
  readonly avg: number;
  readonly median?: number;
  readonly p95?: number;
  readonly p99?: number;
}

/**
 * Metric time series
 */
export interface MetricTimeSeries {
  readonly name: string;
  readonly type: MetricType;
  readonly category: MetricCategory;
  readonly dataPoints: readonly Metric[];
  readonly stats: MetricStats;
}

/**
 * Metrics report
 */
export interface MetricsReport {
  readonly generatedAt: number;
  readonly startTime: number;
  readonly endTime: number;
  readonly durationMs: number;
  readonly series: readonly MetricTimeSeries[];
  readonly summary: MetricsSummary;
}

/**
 * Metrics summary
 */
export interface MetricsSummary {
  readonly totalMetrics: number;
  readonly byCategory: Readonly<Record<MetricCategory, number>>;
  readonly byType: Readonly<Record<MetricType, number>>;
  readonly healthStatus: 'healthy' | 'warning' | 'critical';
  readonly issues?: readonly string[];
}

/**
 * Metrics collector configuration
 */
export interface MetricsConfig {
  /** Maximum metrics to retain in memory */
  readonly maxMetrics: number;
  /** Time window for aggregation (ms) */
  readonly aggregationWindowMs: number;
  /** Whether to enable histogram calculation */
  readonly enableHistograms: boolean;
  /** Percentiles to calculate */
  readonly percentiles: readonly number[];
  /** Metric categories to collect */
  readonly enabledCategories: readonly MetricCategory[];
  /** Flush interval for persistence (ms) */
  readonly flushIntervalMs: number;
}

/**
 * Default metrics configuration
 */
export const DEFAULT_METRICS_CONFIG: MetricsConfig = Object.freeze({
  maxMetrics: 10000,
  aggregationWindowMs: 60000, // 1 minute
  enableHistograms: true,
  percentiles: [0.5, 0.95, 0.99],
  enabledCategories: ['workflow', 'phase', 'gate', 'resource', 'error', 'performance', 'custom'],
  flushIntervalMs: 300000, // 5 minutes
});

// Auto-increment for metric IDs
let metricCounter = 0;

/**
 * Create a metric
 */
export function createMetric(params: {
  id?: string;
  name: string;
  type: MetricType;
  category: MetricCategory;
  value: number;
  unit?: string;
  timestamp?: number;
  labels?: Record<string, string>;
  metadata?: Record<string, unknown>;
}): Metric {
  const id = params.id ?? `M-${String(++metricCounter).padStart(5, '0')}`;

  return Object.freeze({
    id,
    name: params.name,
    type: params.type,
    category: params.category,
    value: params.value,
    unit: params.unit,
    timestamp: params.timestamp ?? Date.now(),
    labels: params.labels ? Object.freeze({ ...params.labels }) : undefined,
    metadata: params.metadata ? Object.freeze({ ...params.metadata }) : undefined,
  });
}

/**
 * Reset metric counter (for testing)
 */
export function resetMetricCounter(): void {
  metricCounter = 0;
}

/**
 * Calculate statistics for a set of metrics
 */
export function calculateStats(metrics: readonly Metric[]): MetricStats {
  if (metrics.length === 0) {
    return {
      count: 0,
      sum: 0,
      min: 0,
      max: 0,
      avg: 0,
    };
  }

  const values = metrics.map(m => m.value).sort((a, b) => a - b);
  const sum = values.reduce((acc, v) => acc + v, 0);

  return {
    count: values.length,
    sum,
    min: values[0],
    max: values[values.length - 1],
    avg: sum / values.length,
    median: getPercentile(values, 0.5),
    p95: getPercentile(values, 0.95),
    p99: getPercentile(values, 0.99),
  };
}

/**
 * Get percentile value from sorted array
 */
function getPercentile(sortedValues: readonly number[], percentile: number): number {
  if (sortedValues.length === 0) return 0;
  const index = Math.ceil(percentile * sortedValues.length) - 1;
  return sortedValues[Math.max(0, Math.min(index, sortedValues.length - 1))];
}
