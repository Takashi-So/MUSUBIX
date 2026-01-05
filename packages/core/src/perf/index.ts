/**
 * Performance Module
 *
 * Provides performance optimization utilities:
 * - Lazy loading for deferred module imports
 * - LRU caching for expensive computations
 * - Parallel execution for concurrent operations
 * - Memory monitoring and leak detection
 * - Benchmarking utilities
 *
 * @packageDocumentation
 * @module perf
 * @traces REQ-PERF-001〜005, DES-PERF-001〜005
 */

// Types
export type {
  CacheOptions,
  CacheStats,
  MemoryStats,
  MemoryReport,
  ParallelOptions,
  BenchmarkResult,
  BenchmarkSuiteResult,
} from './types.js';

export { LazyNotLoadedError } from './types.js';

// Lazy Loading
export {
  lazyImport,
  lazyLoad,
  ensureLoaded,
  isLoaded,
  preloadModules,
  clearModuleCache,
  getModuleCacheStats,
  createLazyModule,
} from './lazy-loader.js';

// Caching
export {
  LRUCache,
  memoize,
  memoizeAsync,
  createGlobalCache,
  getGlobalCache,
  clearGlobalCache,
} from './cache.js';

// Parallel Execution
export {
  parallel,
  parallelMap,
  parallelFilter,
  parallelRace,
  parallelSettle,
  chunk,
  batchProcess,
  ParallelExecutor,
  throttle,
  debounce,
} from './parallel.js';

// Memory Monitoring
export {
  MemoryMonitor,
  formatBytes,
  formatMemoryStats,
  formatMemoryReport,
  measureMemory,
  getMemoryMonitor,
  isMemoryHigh,
  getMemoryUsagePercent,
} from './memory.js';

// Benchmarking
export {
  benchmark,
  benchmarkSuite,
  measure,
  time,
  formatBenchmarkResult,
  formatBenchmarkSuiteResult,
  runStandardBenchmarks,
} from './benchmark.js';
export type { BenchmarkOptions } from './benchmark.js';
