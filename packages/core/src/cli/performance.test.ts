/**
 * Performance module tests
 *
 * @see REQ-NFR-002 - Command response performance
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import {
  PerformanceTimer,
  measureAsync,
  measureSync,
  PerformanceCollector,
  createPerformanceCollector,
  formatPerformanceReport,
  DEFAULT_BASELINES,
} from './performance.js';

describe('PerformanceTimer', () => {
  it('should measure duration', () => {
    const timer = new PerformanceTimer('test-operation');
    timer.start();

    // Simulate some work
    let sum = 0;
    for (let i = 0; i < 10000; i++) {
      sum += i;
    }

    const result = timer.stop();

    expect(result.name).toBe('test-operation');
    expect(result.durationMs).toBeGreaterThanOrEqual(0);
    expect(result.startTime).toBeLessThan(result.endTime);
  });

  it('should include metadata', () => {
    const timer = new PerformanceTimer('test');
    timer.start();
    const result = timer.stop({ operation: 'validate', count: 10 });

    expect(result.metadata).toEqual({ operation: 'validate', count: 10 });
  });

  it('should track memory usage if available', () => {
    const timer = new PerformanceTimer('memory-test');
    timer.start();

    // Allocate some memory
    const arr = new Array(1000).fill({ data: 'test' });

    const result = timer.stop();

    // Memory tracking is platform-dependent
    if (result.memoryUsage !== undefined) {
      expect(typeof result.memoryUsage).toBe('number');
    }

    // Prevent optimization
    expect(arr.length).toBe(1000);
  });
});

describe('measureAsync', () => {
  it('should measure async function duration', async () => {
    const { result, performance } = await measureAsync('async-op', async () => {
      await new Promise((resolve) => setTimeout(resolve, 10));
      return 'completed';
    });

    expect(result).toBe('completed');
    expect(performance.name).toBe('async-op');
    // Use a more lenient threshold due to timing variations
    expect(performance.durationMs).toBeGreaterThanOrEqual(5);
  });

  it('should include metadata', async () => {
    const { performance } = await measureAsync(
      'async-with-meta',
      async () => 42,
      { type: 'calculation' }
    );

    expect(performance.metadata).toEqual({ type: 'calculation' });
  });
});

describe('measureSync', () => {
  it('should measure sync function duration', () => {
    const { result, performance } = measureSync('sync-op', () => {
      let sum = 0;
      for (let i = 0; i < 1000; i++) {
        sum += i;
      }
      return sum;
    });

    expect(result).toBe(499500);
    expect(performance.name).toBe('sync-op');
    expect(performance.durationMs).toBeGreaterThanOrEqual(0);
  });
});

describe('PerformanceCollector', () => {
  let collector: PerformanceCollector;

  beforeEach(() => {
    collector = new PerformanceCollector();
  });

  it('should collect performance results', () => {
    collector.addResult({
      name: 'op1',
      durationMs: 100,
      startTime: 0,
      endTime: 100,
    });
    collector.addResult({
      name: 'op2',
      durationMs: 200,
      startTime: 100,
      endTime: 300,
    });

    const results = collector.getResults();
    expect(results).toHaveLength(2);
  });

  it('should generate report with summary', () => {
    collector.addResult({ name: 'a', durationMs: 100, startTime: 0, endTime: 100 });
    collector.addResult({ name: 'b', durationMs: 200, startTime: 0, endTime: 200 });
    collector.addResult({ name: 'c', durationMs: 300, startTime: 0, endTime: 300 });

    const report = collector.generateReport();

    expect(report.totalOperations).toBe(3);
    expect(report.summary.averageMs).toBe(200);
    expect(report.summary.minMs).toBe(100);
    expect(report.summary.maxMs).toBe(300);
  });

  it('should compare against baselines', () => {
    collector.setBaseline({ name: 'cli:init', targetMs: 500, maxMs: 1000 });
    collector.addResult({ name: 'cli:init', durationMs: 300, startTime: 0, endTime: 300 });

    const report = collector.generateReport();

    expect(report.baselineComparison).toBeDefined();
    expect(report.baselineComparison).toHaveLength(1);
    expect(report.baselineComparison![0].withinTarget).toBe(true);
    expect(report.baselineComparison![0].percentageOfTarget).toBe(60);
  });

  it('should mark as outside target when exceeded', () => {
    collector.setBaseline({ name: 'cli:init', targetMs: 100, maxMs: 200 });
    collector.addResult({ name: 'cli:init', durationMs: 150, startTime: 0, endTime: 150 });

    const report = collector.generateReport();

    expect(report.baselineComparison![0].withinTarget).toBe(false);
    expect(report.baselineComparison![0].percentageOfTarget).toBe(150);
  });

  it('should clear results', () => {
    collector.addResult({ name: 'op', durationMs: 100, startTime: 0, endTime: 100 });
    collector.clear();

    expect(collector.getResults()).toHaveLength(0);
  });

  it('should calculate p95 correctly', () => {
    // Add 20 results
    for (let i = 1; i <= 20; i++) {
      collector.addResult({ name: 'op', durationMs: i * 10, startTime: 0, endTime: i * 10 });
    }

    const report = collector.generateReport();

    // P95 should be around 190ms (19th percentile of 10-200)
    expect(report.summary.p95Ms).toBeGreaterThanOrEqual(180);
    expect(report.summary.p95Ms).toBeLessThanOrEqual(200);
  });

  it('should handle empty results', () => {
    const report = collector.generateReport();

    expect(report.totalOperations).toBe(0);
    expect(report.summary.averageMs).toBe(0);
    expect(report.summary.minMs).toBe(0);
    expect(report.summary.maxMs).toBe(0);
  });
});

describe('createPerformanceCollector', () => {
  it('should create collector with default baselines', () => {
    const collector = createPerformanceCollector();

    // Add result for a default baseline
    collector.addResult({ name: 'cli:init', durationMs: 300, startTime: 0, endTime: 300 });

    const report = collector.generateReport();

    expect(report.baselineComparison).toBeDefined();
    expect(report.baselineComparison![0].name).toBe('cli:init');
  });
});

describe('DEFAULT_BASELINES', () => {
  it('should have baselines for common operations', () => {
    const baselineNames = DEFAULT_BASELINES.map((b) => b.name);

    expect(baselineNames).toContain('cli:init');
    expect(baselineNames).toContain('cli:validate');
    expect(baselineNames).toContain('pattern:query');
  });

  it('should have reasonable target times', () => {
    for (const baseline of DEFAULT_BASELINES) {
      expect(baseline.targetMs).toBeGreaterThan(0);
      expect(baseline.maxMs).toBeGreaterThan(baseline.targetMs);
    }
  });
});

describe('formatPerformanceReport', () => {
  it('should format report as string', () => {
    const collector = createPerformanceCollector();
    collector.addResult({ name: 'cli:init', durationMs: 300, startTime: 0, endTime: 300 });

    const report = collector.generateReport();
    const formatted = formatPerformanceReport(report);

    expect(formatted).toContain('Performance Report');
    expect(formatted).toContain('Average:');
    expect(formatted).toContain('cli:init');
    expect(formatted).toContain('✅');
  });

  it('should show failure indicator when target exceeded', () => {
    const collector = new PerformanceCollector();
    collector.setBaseline({ name: 'slow-op', targetMs: 50, maxMs: 100 });
    collector.addResult({ name: 'slow-op', durationMs: 100, startTime: 0, endTime: 100 });

    const report = collector.generateReport();
    const formatted = formatPerformanceReport(report);

    expect(formatted).toContain('❌');
  });
});
