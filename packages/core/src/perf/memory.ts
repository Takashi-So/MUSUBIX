/**
 * Memory Monitor - Track memory usage and detect leaks
 *
 * @module perf/memory
 * @traces DES-PERF-004, REQ-PERF-004
 * @pattern Observer / Health Check
 */

import type { MemoryStats, MemoryReport } from './types.js';

/**
 * Memory monitor for tracking heap usage
 */
export class MemoryMonitor {
  private samples: MemoryStats[] = [];
  private readonly maxSamples: number;
  private readonly warningThresholdBytes: number;
  private warningCallback?: (stats: MemoryStats) => void;

  /**
   * Create memory monitor
   *
   * @param warningThresholdMB - Memory threshold for warnings (in MB)
   * @param maxSamples - Maximum samples to keep
   */
  constructor(warningThresholdMB: number = 400, maxSamples: number = 100) {
    this.warningThresholdBytes = warningThresholdMB * 1024 * 1024;
    this.maxSamples = maxSamples;
  }

  /**
   * Take memory snapshot
   */
  sample(): MemoryStats {
    const mem = process.memoryUsage();
    const stats: MemoryStats = {
      heapUsed: mem.heapUsed,
      heapTotal: mem.heapTotal,
      external: mem.external,
      rss: mem.rss,
      timestamp: Date.now(),
    };

    this.samples.push(stats);
    if (this.samples.length > this.maxSamples) {
      this.samples.shift();
    }

    // Check warning threshold
    if (stats.heapUsed > this.warningThresholdBytes && this.warningCallback) {
      this.warningCallback(stats);
    }

    return stats;
  }

  /**
   * Force garbage collection (if --expose-gc flag is set)
   */
  gc(): boolean {
    if (global.gc) {
      global.gc();
      return true;
    }
    return false;
  }

  /**
   * Get current memory stats
   */
  current(): MemoryStats {
    return this.sample();
  }

  /**
   * Get peak memory stats
   */
  peak(): MemoryStats {
    if (this.samples.length === 0) {
      return this.sample();
    }

    return this.samples.reduce((peak, current) => {
      return current.heapUsed > peak.heapUsed ? current : peak;
    });
  }

  /**
   * Get average memory stats
   */
  average(): MemoryStats {
    if (this.samples.length === 0) {
      return this.sample();
    }

    const sum = this.samples.reduce(
      (acc, s) => ({
        heapUsed: acc.heapUsed + s.heapUsed,
        heapTotal: acc.heapTotal + s.heapTotal,
        external: acc.external + s.external,
        rss: acc.rss + s.rss,
        timestamp: s.timestamp,
      }),
      { heapUsed: 0, heapTotal: 0, external: 0, rss: 0, timestamp: 0 }
    );

    const count = this.samples.length;
    return {
      heapUsed: Math.round(sum.heapUsed / count),
      heapTotal: Math.round(sum.heapTotal / count),
      external: Math.round(sum.external / count),
      rss: Math.round(sum.rss / count),
      timestamp: Date.now(),
    };
  }

  /**
   * Get memory trend
   */
  trend(): 'increasing' | 'stable' | 'decreasing' {
    if (this.samples.length < 3) {
      return 'stable';
    }

    // Compare first third vs last third
    const third = Math.floor(this.samples.length / 3);
    const firstThird = this.samples.slice(0, third);
    const lastThird = this.samples.slice(-third);

    const firstAvg = firstThird.reduce((sum, s) => sum + s.heapUsed, 0) / firstThird.length;
    const lastAvg = lastThird.reduce((sum, s) => sum + s.heapUsed, 0) / lastThird.length;

    const delta = (lastAvg - firstAvg) / firstAvg;

    if (delta > 0.1) return 'increasing';
    if (delta < -0.1) return 'decreasing';
    return 'stable';
  }

  /**
   * Get full memory report
   */
  report(): MemoryReport {
    return {
      current: this.current(),
      peak: this.peak(),
      average: this.average(),
      trend: this.trend(),
    };
  }

  /**
   * Set warning callback
   */
  onWarning(callback: (stats: MemoryStats) => void): void {
    this.warningCallback = callback;
  }

  /**
   * Clear samples
   */
  clear(): void {
    this.samples = [];
  }

  /**
   * Get all samples
   */
  getSamples(): MemoryStats[] {
    return [...this.samples];
  }

  /**
   * Start periodic sampling
   *
   * @param intervalMs - Sampling interval in milliseconds
   * @returns Function to stop sampling
   */
  startSampling(intervalMs: number = 1000): () => void {
    const timer = setInterval(() => this.sample(), intervalMs);
    return () => clearInterval(timer);
  }
}

/**
 * Format bytes to human-readable string
 */
export function formatBytes(bytes: number): string {
  const units = ['B', 'KB', 'MB', 'GB'];
  let value = bytes;
  let unitIndex = 0;

  while (value >= 1024 && unitIndex < units.length - 1) {
    value /= 1024;
    unitIndex++;
  }

  return `${value.toFixed(2)} ${units[unitIndex]}`;
}

/**
 * Format memory stats for display
 */
export function formatMemoryStats(stats: MemoryStats): string {
  return [
    `Heap Used:  ${formatBytes(stats.heapUsed)}`,
    `Heap Total: ${formatBytes(stats.heapTotal)}`,
    `External:   ${formatBytes(stats.external)}`,
    `RSS:        ${formatBytes(stats.rss)}`,
  ].join('\n');
}

/**
 * Format memory report for display
 */
export function formatMemoryReport(report: MemoryReport): string {
  const lines = [
    '=== Memory Report ===',
    '',
    '--- Current ---',
    formatMemoryStats(report.current),
    '',
    '--- Peak ---',
    formatMemoryStats(report.peak),
    '',
    '--- Average ---',
    formatMemoryStats(report.average),
    '',
    `Trend: ${report.trend}`,
  ];

  return lines.join('\n');
}

/**
 * Measure memory usage of a function
 *
 * @param fn - Function to measure
 * @returns Result and memory delta
 */
export async function measureMemory<R>(
  fn: () => R | Promise<R>
): Promise<{ result: R; memoryDelta: number; stats: { before: MemoryStats; after: MemoryStats } }> {
  // Force GC before measurement if available
  if (global.gc) {
    global.gc();
  }

  const before: MemoryStats = {
    ...process.memoryUsage(),
    timestamp: Date.now(),
  };

  const result = await fn();

  // Force GC after measurement if available
  if (global.gc) {
    global.gc();
  }

  const after: MemoryStats = {
    ...process.memoryUsage(),
    timestamp: Date.now(),
  };

  return {
    result,
    memoryDelta: after.heapUsed - before.heapUsed,
    stats: { before, after },
  };
}

// Global memory monitor instance
let globalMonitor: MemoryMonitor | null = null;

/**
 * Get global memory monitor
 */
export function getMemoryMonitor(): MemoryMonitor {
  if (!globalMonitor) {
    globalMonitor = new MemoryMonitor();
  }
  return globalMonitor;
}

/**
 * Check if memory usage exceeds threshold
 *
 * @param thresholdMB - Threshold in megabytes
 * @returns True if exceeds threshold
 */
export function isMemoryHigh(thresholdMB: number = 400): boolean {
  const usage = process.memoryUsage();
  return usage.heapUsed > thresholdMB * 1024 * 1024;
}

/**
 * Get memory usage percentage
 */
export function getMemoryUsagePercent(): number {
  const usage = process.memoryUsage();
  return (usage.heapUsed / usage.heapTotal) * 100;
}
