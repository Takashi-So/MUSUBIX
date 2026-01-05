/**
 * Benchmark - Performance measurement utilities
 *
 * @module perf/benchmark
 * @traces DES-PERF-005, REQ-PERF-005
 */

import type { BenchmarkResult, BenchmarkSuiteResult, MemoryStats } from './types.js';

/**
 * Benchmark options
 */
export interface BenchmarkOptions {
  /** Number of iterations */
  iterations?: number;
  /** Warmup iterations (not counted) */
  warmup?: number;
  /** Target threshold in milliseconds */
  threshold?: number;
  /** Whether to force GC between iterations */
  forceGC?: boolean;
}

/**
 * Run a benchmark
 *
 * @param name - Benchmark name
 * @param fn - Function to benchmark
 * @param options - Benchmark options
 * @returns Benchmark result
 */
export async function benchmark(
  name: string,
  fn: () => void | Promise<void>,
  options: BenchmarkOptions = {}
): Promise<BenchmarkResult> {
  const { iterations = 100, warmup = 10, threshold, forceGC = false } = options;

  // Warmup
  for (let i = 0; i < warmup; i++) {
    await fn();
  }

  // Force GC before measurement if available
  if (forceGC && global.gc) {
    global.gc();
  }

  const memoryBefore: MemoryStats = {
    ...process.memoryUsage(),
    timestamp: Date.now(),
  };

  const durations: number[] = [];
  const start = performance.now();

  for (let i = 0; i < iterations; i++) {
    const iterStart = performance.now();
    await fn();
    durations.push(performance.now() - iterStart);
  }

  const totalDuration = performance.now() - start;

  // Force GC after measurement if available
  if (forceGC && global.gc) {
    global.gc();
  }

  const memoryAfter: MemoryStats = {
    ...process.memoryUsage(),
    timestamp: Date.now(),
  };

  const avgDuration = totalDuration / iterations;
  const opsPerSecond = 1000 / avgDuration;
  const passed = threshold ? avgDuration <= threshold : true;

  return {
    name,
    duration: avgDuration,
    opsPerSecond,
    memoryBefore,
    memoryAfter,
    memoryDelta: memoryAfter.heapUsed - memoryBefore.heapUsed,
    passed,
    threshold,
  };
}

/**
 * Run a benchmark suite
 *
 * @param name - Suite name
 * @param benchmarks - Array of benchmark definitions
 * @returns Suite result
 */
export async function benchmarkSuite(
  name: string,
  benchmarks: Array<{
    name: string;
    fn: () => void | Promise<void>;
    options?: BenchmarkOptions;
  }>
): Promise<BenchmarkSuiteResult> {
  const results: BenchmarkResult[] = [];
  const startTime = Date.now();

  for (const b of benchmarks) {
    const result = await benchmark(b.name, b.fn, b.options);
    results.push(result);
  }

  const totalDuration = Date.now() - startTime;
  const passedCount = results.filter((r) => r.passed).length;

  return {
    name,
    totalDuration,
    results,
    passRate: passedCount / results.length,
    timestamp: new Date().toISOString(),
  };
}

/**
 * Measure execution time
 *
 * @param fn - Function to measure
 * @returns Result and duration
 */
export async function measure<R>(
  fn: () => R | Promise<R>
): Promise<{ result: R; duration: number }> {
  const start = performance.now();
  const result = await fn();
  const duration = performance.now() - start;
  return { result, duration };
}

/**
 * Time a function and log result
 *
 * @param label - Label for logging
 * @param fn - Function to time
 * @returns Result
 */
export async function time<R>(
  label: string,
  fn: () => R | Promise<R>
): Promise<R> {
  const { result, duration } = await measure(fn);
  console.log(`${label}: ${duration.toFixed(2)}ms`);
  return result;
}

/**
 * Format benchmark result for display
 */
export function formatBenchmarkResult(result: BenchmarkResult): string {
  const status = result.passed ? '✓' : '✗';
  const thresholdInfo = result.threshold
    ? ` (threshold: ${result.threshold}ms)`
    : '';

  return [
    `${status} ${result.name}`,
    `  Duration: ${result.duration.toFixed(2)}ms${thresholdInfo}`,
    `  Ops/sec:  ${result.opsPerSecond.toFixed(0)}`,
    `  Memory:   ${formatBytes(result.memoryDelta)} delta`,
  ].join('\n');
}

/**
 * Format benchmark suite result for display
 */
export function formatBenchmarkSuiteResult(suite: BenchmarkSuiteResult): string {
  const header = `=== ${suite.name} ===\n`;
  const results = suite.results.map(formatBenchmarkResult).join('\n\n');
  const summary = [
    '',
    '--- Summary ---',
    `Total:     ${suite.totalDuration}ms`,
    `Pass Rate: ${(suite.passRate * 100).toFixed(0)}%`,
    `Timestamp: ${suite.timestamp}`,
  ].join('\n');

  return header + results + summary;
}

/**
 * Format bytes to human-readable string
 */
function formatBytes(bytes: number): string {
  const sign = bytes < 0 ? '-' : '+';
  const abs = Math.abs(bytes);
  const units = ['B', 'KB', 'MB', 'GB'];
  let value = abs;
  let unitIndex = 0;

  while (value >= 1024 && unitIndex < units.length - 1) {
    value /= 1024;
    unitIndex++;
  }

  return `${sign}${value.toFixed(2)} ${units[unitIndex]}`;
}

/**
 * Standard benchmark suite for MUSUBIX
 */
export async function runStandardBenchmarks(): Promise<BenchmarkSuiteResult> {
  return benchmarkSuite('MUSUBIX Standard Benchmarks', [
    {
      name: 'Empty loop (baseline)',
      fn: () => {
        for (let i = 0; i < 1000; i++) {
          // Empty
        }
      },
      options: { iterations: 1000, threshold: 1 },
    },
    {
      name: 'JSON parse/stringify',
      fn: () => {
        const obj = { a: 1, b: 'test', c: [1, 2, 3] };
        JSON.parse(JSON.stringify(obj));
      },
      options: { iterations: 1000, threshold: 1 },
    },
    {
      name: 'Array operations',
      fn: () => {
        const arr = Array.from({ length: 1000 }, (_, i) => i);
        arr.map((x) => x * 2).filter((x) => x % 2 === 0);
      },
      options: { iterations: 100, threshold: 10 },
    },
    {
      name: 'Object spread',
      fn: () => {
        const obj = { a: 1, b: 2, c: 3 };
        const merged = { ...obj, d: 4, e: 5 };
        void merged;
      },
      options: { iterations: 10000, threshold: 0.1 },
    },
  ]);
}
