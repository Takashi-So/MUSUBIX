/**
 * Metrics Module Exports
 *
 * @description
 * メトリクス収集システムの公開API
 *
 * @see DES-CORE-001 - メトリクス収集システム
 */

export type {
  MetricType,
  MetricCategory,
  Metric,
  MetricInput,
  MetricStats,
  MetricTimeSeries,
  MetricsReport,
  MetricsSummary,
  MetricsConfig,
} from './types.js';

export {
  createMetric,
  resetMetricCounter,
  calculateStats,
  DEFAULT_METRICS_CONFIG,
} from './types.js';

export type { IMetricsCollector } from './MetricsCollector.js';

export { MetricsCollector, createMetricsCollector } from './MetricsCollector.js';
