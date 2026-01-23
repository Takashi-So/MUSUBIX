/**
 * MetricsCollector Tests
 *
 * @see TSK-FR-037 - MetricsCollectorユニットテスト
 */
import { describe, it, expect, beforeEach } from 'vitest';

import {
  createMetric,
  resetMetricCounter,
  calculateStats,
  DEFAULT_METRICS_CONFIG,
} from '../types.js';

import {
  createMetricsCollector,
} from '../MetricsCollector.js';

describe('MetricsCollector', () => {
  beforeEach(() => {
    resetMetricCounter();
  });

  // ============================================================
  // Type Tests
  // ============================================================
  describe('createMetric', () => {
    it('should create a metric with auto-generated ID', () => {
      const metric = createMetric({
        name: 'workflow.duration',
        type: 'timer',
        category: 'workflow',
        value: 1500,
        unit: 'ms',
      });

      expect(metric.id).toBe('M-00001');
      expect(metric.name).toBe('workflow.duration');
      expect(metric.type).toBe('timer');
      expect(metric.value).toBe(1500);
    });

    it('should be immutable', () => {
      const metric = createMetric({
        name: 'test.counter',
        type: 'counter',
        category: 'custom',
        value: 1,
      });

      expect(() => {
        (metric as any).value = 100;
      }).toThrow();
    });

    it('should include labels and metadata', () => {
      const metric = createMetric({
        name: 'phase.duration',
        type: 'timer',
        category: 'phase',
        value: 2000,
        labels: { phase: 'requirements', workflowId: 'wf-001' },
        metadata: { success: true },
      });

      expect(metric.labels?.phase).toBe('requirements');
      expect(metric.metadata?.success).toBe(true);
    });
  });

  describe('calculateStats', () => {
    it('should calculate statistics correctly', () => {
      const metrics = [
        createMetric({ name: 'test', type: 'gauge', category: 'custom', value: 10 }),
        createMetric({ name: 'test', type: 'gauge', category: 'custom', value: 20 }),
        createMetric({ name: 'test', type: 'gauge', category: 'custom', value: 30 }),
        createMetric({ name: 'test', type: 'gauge', category: 'custom', value: 40 }),
        createMetric({ name: 'test', type: 'gauge', category: 'custom', value: 50 }),
      ];

      const stats = calculateStats(metrics);

      expect(stats.count).toBe(5);
      expect(stats.sum).toBe(150);
      expect(stats.min).toBe(10);
      expect(stats.max).toBe(50);
      expect(stats.avg).toBe(30);
      expect(stats.median).toBe(30);
    });

    it('should handle empty metrics', () => {
      const stats = calculateStats([]);

      expect(stats.count).toBe(0);
      expect(stats.sum).toBe(0);
      expect(stats.avg).toBe(0);
    });
  });

  // ============================================================
  // MetricsCollector Tests
  // ============================================================
  describe('collect', () => {
    it('should collect a metric', () => {
      const collector = createMetricsCollector();

      collector.collect({
        name: 'workflow.started',
        type: 'counter',
        category: 'workflow',
        value: 1,
      });

      expect(collector.getMetrics()).toHaveLength(1);
    });

    it('should collect multiple metrics', () => {
      const collector = createMetricsCollector();

      collector.collect({
        name: 'workflow.started',
        type: 'counter',
        category: 'workflow',
        value: 1,
      });
      collector.collect({
        name: 'phase.duration',
        type: 'timer',
        category: 'phase',
        value: 1500,
      });

      expect(collector.getMetrics()).toHaveLength(2);
    });

    it('should respect max metrics limit', () => {
      const collector = createMetricsCollector({
        ...DEFAULT_METRICS_CONFIG,
        maxMetrics: 3,
      });

      for (let i = 0; i < 5; i++) {
        collector.collect({
          name: `metric.${i}`,
          type: 'counter',
          category: 'custom',
          value: i,
        });
      }

      expect(collector.getMetrics()).toHaveLength(3);
    });
  });

  describe('increment', () => {
    it('should increment a counter metric', () => {
      const collector = createMetricsCollector();

      collector.increment('requests.total', 'workflow');
      collector.increment('requests.total', 'workflow');
      collector.increment('requests.total', 'workflow');

      const metrics = collector.getMetrics();
      expect(metrics).toHaveLength(3);
    });

    it('should increment by custom amount', () => {
      const collector = createMetricsCollector();

      collector.increment('errors.count', 'error', 5);

      const metrics = collector.getMetrics();
      expect(metrics[0].value).toBe(5);
    });
  });

  describe('gauge', () => {
    it('should set a gauge value', () => {
      const collector = createMetricsCollector();

      collector.gauge('memory.used', 'resource', 512);

      const metrics = collector.getMetrics();
      expect(metrics[0].type).toBe('gauge');
      expect(metrics[0].value).toBe(512);
    });
  });

  describe('timer', () => {
    it('should record timing', () => {
      const collector = createMetricsCollector();

      collector.timer('phase.duration', 'phase', 1500);

      const metrics = collector.getMetrics();
      expect(metrics[0].type).toBe('timer');
      expect(metrics[0].value).toBe(1500);
    });
  });

  describe('aggregate', () => {
    it('should aggregate metrics by name', async () => {
      const collector = createMetricsCollector();

      collector.timer('phase.duration', 'phase', 1000);
      collector.timer('phase.duration', 'phase', 2000);
      collector.timer('phase.duration', 'phase', 3000);

      const series = await collector.aggregate('phase.duration');

      expect(series.name).toBe('phase.duration');
      expect(series.stats.count).toBe(3);
      expect(series.stats.avg).toBe(2000);
      expect(series.type).toBe('timer');
      expect(series.category).toBe('phase');
    });

    it('should return empty series for unknown metric', async () => {
      const collector = createMetricsCollector();

      const series = await collector.aggregate('unknown.metric');

      expect(series.dataPoints).toHaveLength(0);
      expect(series.stats.count).toBe(0);
    });
  });

  describe('export', () => {
    it('should export metrics report', async () => {
      const collector = createMetricsCollector();

      collector.increment('requests.total', 'workflow');
      collector.timer('phase.duration', 'phase', 1500);
      collector.gauge('memory.used', 'resource', 512);

      const report = await collector.export();

      expect(report.summary.totalMetrics).toBe(3);
      expect(report.series.length).toBeGreaterThan(0);
      expect(report.durationMs).toBeGreaterThanOrEqual(0);
    });

    it('should include health status', async () => {
      const collector = createMetricsCollector();

      collector.increment('errors.count', 'error', 5);

      const report = await collector.export();

      expect(report.summary.healthStatus).toBeDefined();
      expect(['healthy', 'warning', 'critical']).toContain(report.summary.healthStatus);
    });

    it('should include time range', async () => {
      const collector = createMetricsCollector();
      const startTime = Date.now();

      collector.increment('test', 'custom');

      const report = await collector.export();

      expect(report.startTime).toBeGreaterThanOrEqual(startTime - 1000);
      expect(report.endTime).toBeGreaterThanOrEqual(report.startTime);
      expect(report.generatedAt).toBeGreaterThanOrEqual(report.startTime);
    });
  });

  describe('onPhaseStart / onPhaseEnd', () => {
    it('should record phase metrics', () => {
      const collector = createMetricsCollector();

      collector.onPhaseStart('wf-001', 'requirements');
      collector.onPhaseEnd('wf-001', 1500);

      const metrics = collector.getMetrics();
      expect(metrics.some(m => m.name === 'phase.started')).toBe(true);
      expect(metrics.some(m => m.name === 'phase.duration')).toBe(true);
    });
  });

  describe('onError', () => {
    it('should record error metrics', () => {
      const collector = createMetricsCollector();

      collector.onError('wf-001', new Error('Test error'));

      const metrics = collector.getMetrics();
      expect(metrics.some(m => m.category === 'error')).toBe(true);
    });
  });

  describe('getMetricsByCategory', () => {
    it('should filter metrics by category', () => {
      const collector = createMetricsCollector();

      collector.increment('workflow.count', 'workflow');
      collector.timer('phase.duration', 'phase');
      collector.increment('errors.count', 'error');

      const phaseMetrics = collector.getMetricsByCategory('phase');
      expect(phaseMetrics).toHaveLength(1);
      expect(phaseMetrics[0].category).toBe('phase');
    });
  });

  describe('clear', () => {
    it('should clear all metrics', () => {
      const collector = createMetricsCollector();

      collector.increment('test', 'custom');
      collector.increment('test', 'custom');

      collector.clear();

      expect(collector.getMetrics()).toHaveLength(0);
    });
  });
});
