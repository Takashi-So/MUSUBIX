/**
 * Performance Module - Types and interfaces
 *
 * @module perf/types
 * @traces REQ-PERF-001〜005
 */

/**
 * Cache options for LRU cache
 */
export interface CacheOptions {
  /** Maximum number of entries */
  maxSize: number;
  /** Time-to-live in milliseconds */
  ttlMs: number;
  /** Callback when entry is evicted */
  onEvict?: (key: string, value: unknown) => void;
}

/**
 * Cache statistics
 */
export interface CacheStats {
  /** Current size */
  size: number;
  /** Maximum size */
  maxSize: number;
  /** Hit count */
  hits: number;
  /** Miss count */
  misses: number;
  /** Hit rate (0-1) */
  hitRate: number;
  /** Eviction count */
  evictions: number;
}

/**
 * Memory statistics
 */
export interface MemoryStats {
  /** Heap used in bytes */
  heapUsed: number;
  /** Total heap size in bytes */
  heapTotal: number;
  /** External memory in bytes */
  external: number;
  /** Resident set size in bytes */
  rss: number;
  /** Timestamp */
  timestamp: number;
}

/**
 * Memory report
 */
export interface MemoryReport {
  /** Current memory stats */
  current: MemoryStats;
  /** Peak memory stats */
  peak: MemoryStats;
  /** Average memory stats */
  average: MemoryStats;
  /** Memory trend (increasing/stable/decreasing) */
  trend: 'increasing' | 'stable' | 'decreasing';
}

/**
 * Parallel execution options
 */
export interface ParallelOptions {
  /** Maximum number of concurrent workers */
  maxWorkers?: number;
  /** Task timeout in milliseconds */
  taskTimeout?: number;
  /** Concurrency limit for Promise-based parallelism */
  concurrency?: number;
}

/**
 * Benchmark result
 */
export interface BenchmarkResult {
  /** Benchmark name */
  name: string;
  /** Execution time in milliseconds */
  duration: number;
  /** Operations per second */
  opsPerSecond: number;
  /** Memory before */
  memoryBefore: MemoryStats;
  /** Memory after */
  memoryAfter: MemoryStats;
  /** Memory delta */
  memoryDelta: number;
  /** Passed threshold */
  passed: boolean;
  /** Target threshold */
  threshold?: number;
}

/**
 * Benchmark suite result
 */
export interface BenchmarkSuiteResult {
  /** Suite name */
  name: string;
  /** Total duration */
  totalDuration: number;
  /** Individual results */
  results: BenchmarkResult[];
  /** Pass rate */
  passRate: number;
  /** Timestamp */
  timestamp: string;
}

/**
 * Lazy loading error
 */
export class LazyNotLoadedError extends Error {
  constructor(
    public readonly moduleId: string,
    public readonly property: string | symbol
  ) {
    super(`Module '${moduleId}' not yet loaded. Access to '${String(property)}' requires async loading.`);
    this.name = 'LazyNotLoadedError';
  }
}
