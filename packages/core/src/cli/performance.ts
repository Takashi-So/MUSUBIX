/**
 * Performance Measurement Utilities
 *
 * @packageDocumentation
 * @module cli/performance
 * @see REQ-NFR-002 - Command response performance
 * @see DES-NFR-002 - Performance optimization design
 */

/**
 * Performance measurement result
 */
export interface PerformanceResult {
  /** Operation name */
  name: string;
  /** Duration in milliseconds */
  durationMs: number;
  /** Start timestamp */
  startTime: number;
  /** End timestamp */
  endTime: number;
  /** Memory usage in bytes (if available) */
  memoryUsage?: number;
  /** Additional metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Performance baseline for comparison
 */
export interface PerformanceBaseline {
  /** Operation name */
  name: string;
  /** Target duration in milliseconds */
  targetMs: number;
  /** Maximum acceptable duration */
  maxMs: number;
}

/**
 * Performance report
 */
export interface PerformanceReport {
  /** Report timestamp */
  timestamp: Date;
  /** Total operations measured */
  totalOperations: number;
  /** Results by operation */
  results: PerformanceResult[];
  /** Summary statistics */
  summary: {
    /** Average duration across all operations */
    averageMs: number;
    /** Minimum duration */
    minMs: number;
    /** Maximum duration */
    maxMs: number;
    /** 95th percentile */
    p95Ms: number;
  };
  /** Baseline comparison (if baselines provided) */
  baselineComparison?: Array<{
    name: string;
    actualMs: number;
    targetMs: number;
    withinTarget: boolean;
    percentageOfTarget: number;
  }>;
}

/**
 * Performance timer for measuring operation duration
 */
export class PerformanceTimer {
  private startTime: number = 0;
  private startMemory: number = 0;
  private readonly name: string;

  constructor(name: string) {
    this.name = name;
  }

  /**
   * Start the timer
   */
  start(): void {
    this.startTime = performance.now();
    if (typeof process !== 'undefined' && process.memoryUsage) {
      this.startMemory = process.memoryUsage().heapUsed;
    }
  }

  /**
   * Stop the timer and return the result
   */
  stop(metadata?: Record<string, unknown>): PerformanceResult {
    const endTime = performance.now();
    const durationMs = endTime - this.startTime;

    let memoryUsage: number | undefined;
    if (typeof process !== 'undefined' && process.memoryUsage) {
      memoryUsage = process.memoryUsage().heapUsed - this.startMemory;
    }

    return {
      name: this.name,
      durationMs,
      startTime: this.startTime,
      endTime,
      memoryUsage,
      metadata,
    };
  }
}

/**
 * Measure the execution time of a function
 */
export async function measureAsync<T>(
  name: string,
  fn: () => Promise<T>,
  metadata?: Record<string, unknown>
): Promise<{ result: T; performance: PerformanceResult }> {
  const timer = new PerformanceTimer(name);
  timer.start();

  const result = await fn();
  const perf = timer.stop(metadata);

  return { result, performance: perf };
}

/**
 * Measure the execution time of a synchronous function
 */
export function measureSync<T>(
  name: string,
  fn: () => T,
  metadata?: Record<string, unknown>
): { result: T; performance: PerformanceResult } {
  const timer = new PerformanceTimer(name);
  timer.start();

  const result = fn();
  const perf = timer.stop(metadata);

  return { result, performance: perf };
}

/**
 * Performance collector for aggregating multiple measurements
 */
export class PerformanceCollector {
  private results: PerformanceResult[] = [];
  private baselines: Map<string, PerformanceBaseline> = new Map();

  /**
   * Add a performance result
   */
  addResult(result: PerformanceResult): void {
    this.results.push(result);
  }

  /**
   * Set baseline for an operation
   */
  setBaseline(baseline: PerformanceBaseline): void {
    this.baselines.set(baseline.name, baseline);
  }

  /**
   * Clear all results
   */
  clear(): void {
    this.results = [];
  }

  /**
   * Get all results
   */
  getResults(): PerformanceResult[] {
    return [...this.results];
  }

  /**
   * Generate a performance report
   */
  generateReport(): PerformanceReport {
    const durations = this.results.map((r) => r.durationMs);
    const sortedDurations = [...durations].sort((a, b) => a - b);

    const summary = {
      averageMs:
        durations.length > 0
          ? durations.reduce((a, b) => a + b, 0) / durations.length
          : 0,
      minMs: durations.length > 0 ? Math.min(...durations) : 0,
      maxMs: durations.length > 0 ? Math.max(...durations) : 0,
      p95Ms:
        sortedDurations.length > 0
          ? sortedDurations[Math.floor(sortedDurations.length * 0.95)] ?? 0
          : 0,
    };

    // Group results by name and calculate averages
    const resultsByName = new Map<string, number[]>();
    for (const result of this.results) {
      const existing = resultsByName.get(result.name) ?? [];
      existing.push(result.durationMs);
      resultsByName.set(result.name, existing);
    }

    // Compare against baselines
    const baselineComparison: PerformanceReport['baselineComparison'] = [];
    for (const [name, durations] of resultsByName) {
      const baseline = this.baselines.get(name);
      if (baseline) {
        const avgMs = durations.reduce((a, b) => a + b, 0) / durations.length;
        baselineComparison.push({
          name,
          actualMs: avgMs,
          targetMs: baseline.targetMs,
          withinTarget: avgMs <= baseline.targetMs,
          percentageOfTarget: (avgMs / baseline.targetMs) * 100,
        });
      }
    }

    return {
      timestamp: new Date(),
      totalOperations: this.results.length,
      results: [...this.results],
      summary,
      baselineComparison:
        baselineComparison.length > 0 ? baselineComparison : undefined,
    };
  }
}

/**
 * Default performance baselines for CLI commands
 */
export const DEFAULT_BASELINES: PerformanceBaseline[] = [
  { name: 'cli:init', targetMs: 500, maxMs: 1000 },
  { name: 'cli:validate', targetMs: 200, maxMs: 500 },
  { name: 'cli:analyze', targetMs: 1000, maxMs: 2000 },
  { name: 'cli:generate', targetMs: 500, maxMs: 1000 },
  { name: 'pattern:query', targetMs: 100, maxMs: 300 },
  { name: 'pattern:extract', targetMs: 500, maxMs: 1000 },
  { name: 'learning:recommend', targetMs: 200, maxMs: 500 },
];

/**
 * Create a performance collector with default baselines
 */
export function createPerformanceCollector(): PerformanceCollector {
  const collector = new PerformanceCollector();
  for (const baseline of DEFAULT_BASELINES) {
    collector.setBaseline(baseline);
  }
  return collector;
}

/**
 * Format a performance report as a human-readable string
 */
export function formatPerformanceReport(report: PerformanceReport): string {
  const lines: string[] = [
    '=== Performance Report ===',
    `Timestamp: ${report.timestamp.toISOString()}`,
    `Total Operations: ${report.totalOperations}`,
    '',
    '--- Summary ---',
    `Average: ${report.summary.averageMs.toFixed(2)}ms`,
    `Min: ${report.summary.minMs.toFixed(2)}ms`,
    `Max: ${report.summary.maxMs.toFixed(2)}ms`,
    `P95: ${report.summary.p95Ms.toFixed(2)}ms`,
  ];

  if (report.baselineComparison && report.baselineComparison.length > 0) {
    lines.push('', '--- Baseline Comparison ---');
    for (const comparison of report.baselineComparison) {
      const status = comparison.withinTarget ? '✅' : '❌';
      lines.push(
        `${status} ${comparison.name}: ${comparison.actualMs.toFixed(2)}ms ` +
          `(target: ${comparison.targetMs}ms, ${comparison.percentageOfTarget.toFixed(1)}%)`
      );
    }
  }

  return lines.join('\n');
}
