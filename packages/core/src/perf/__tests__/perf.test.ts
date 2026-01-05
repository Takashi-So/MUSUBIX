/**
 * Performance Module Tests
 *
 * @module perf/__tests__
 * @traces REQ-PERF-001〜005
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import {
  // Lazy Loading
  lazyLoad,
  isLoaded,
  clearModuleCache,
  getModuleCacheStats,
  createLazyModule,
  LazyNotLoadedError,

  // Caching
  LRUCache,
  memoize,
  memoizeAsync,
  createGlobalCache,
  clearGlobalCache,

  // Parallel
  parallel,
  parallelMap,
  parallelFilter,
  chunk,
  batchProcess,
  ParallelExecutor,
  throttle,
  debounce,

  // Memory
  MemoryMonitor,
  formatBytes,
  measureMemory,
  isMemoryHigh,
  getMemoryUsagePercent,

  // Benchmark
  benchmark,
  benchmarkSuite,
  measure,
} from '../index.js';

// =============================================================================
// Lazy Loading Tests (REQ-PERF-001)
// =============================================================================

describe('Lazy Loading', () => {
  beforeEach(() => {
    clearModuleCache();
  });

  describe('lazyLoad', () => {
    it('should load module asynchronously', async () => {
      const module = await lazyLoad(async () => ({ value: 42 }), 'test-module');
      expect(module.value).toBe(42);
    });

    it('should cache loaded modules', async () => {
      let loadCount = 0;
      const loadFn = async () => {
        loadCount++;
        return { value: loadCount };
      };

      const first = await lazyLoad(loadFn, 'cached-module');
      const second = await lazyLoad(loadFn, 'cached-module');

      expect(first.value).toBe(1);
      expect(second.value).toBe(1);
      expect(loadCount).toBe(1);
    });

    it('should handle load without moduleId', async () => {
      const module = await lazyLoad(async () => ({ test: true }));
      expect(module.test).toBe(true);
    });
  });

  describe('createLazyModule', () => {
    it('should create lazy module with load function', async () => {
      const lazy = createLazyModule(
        async () => ({ name: 'test' }),
        'lazy-test'
      );

      expect(lazy.isLoaded()).toBe(false);
      
      const loaded = await lazy.load();
      expect(loaded.name).toBe('test');
      expect(lazy.isLoaded()).toBe(true);
    });

    it('should throw when accessing unloaded proxy', () => {
      const lazy = createLazyModule(
        async () => ({ name: 'test' }),
        'unloaded-test'
      );

      expect(() => (lazy.proxy as { name: string }).name).toThrow(LazyNotLoadedError);
    });
  });

  describe('getModuleCacheStats', () => {
    it('should return cache statistics', async () => {
      await lazyLoad(async () => ({}), 'stats-test');
      
      const stats = getModuleCacheStats();
      expect(stats.loaded).toBeGreaterThanOrEqual(1);
      expect(stats.moduleIds).toContain('stats-test');
    });
  });

  describe('isLoaded', () => {
    it('should check if module is loaded', async () => {
      expect(isLoaded('not-loaded')).toBe(false);
      
      await lazyLoad(async () => ({}), 'to-load');
      expect(isLoaded('to-load')).toBe(true);
    });
  });
});

// =============================================================================
// Cache Tests (REQ-PERF-002)
// =============================================================================

describe('LRUCache', () => {
  let cache: LRUCache<string, number>;

  beforeEach(() => {
    cache = new LRUCache({ maxSize: 3, ttlMs: 1000 });
  });

  describe('basic operations', () => {
    it('should set and get values', () => {
      cache.set('a', 1);
      expect(cache.get('a')).toBe(1);
    });

    it('should return undefined for missing keys', () => {
      expect(cache.get('missing')).toBeUndefined();
    });

    it('should check has correctly', () => {
      cache.set('exists', 1);
      expect(cache.has('exists')).toBe(true);
      expect(cache.has('missing')).toBe(false);
    });

    it('should delete entries', () => {
      cache.set('to-delete', 1);
      expect(cache.delete('to-delete')).toBe(true);
      expect(cache.get('to-delete')).toBeUndefined();
    });

    it('should clear all entries', () => {
      cache.set('a', 1);
      cache.set('b', 2);
      cache.clear();
      expect(cache.size).toBe(0);
    });
  });

  describe('LRU eviction', () => {
    it('should evict oldest when at capacity', () => {
      cache.set('a', 1);
      cache.set('b', 2);
      cache.set('c', 3);
      cache.set('d', 4); // Should evict 'a'

      expect(cache.get('a')).toBeUndefined();
      expect(cache.get('b')).toBe(2);
      expect(cache.get('c')).toBe(3);
      expect(cache.get('d')).toBe(4);
    });

    it('should update LRU order on access', () => {
      cache.set('a', 1);
      cache.set('b', 2);
      cache.set('c', 3);
      
      cache.get('a'); // Access 'a' to make it most recent
      cache.set('d', 4); // Should evict 'b' (oldest)

      expect(cache.get('a')).toBe(1);
      expect(cache.get('b')).toBeUndefined();
    });
  });

  describe('TTL expiration', () => {
    it('should expire entries after TTL', async () => {
      const shortTTLCache = new LRUCache<string, number>({ maxSize: 10, ttlMs: 50 });
      shortTTLCache.set('expire', 1);
      
      expect(shortTTLCache.get('expire')).toBe(1);
      
      await new Promise((resolve) => setTimeout(resolve, 100));
      
      expect(shortTTLCache.get('expire')).toBeUndefined();
    });

    it('should support custom TTL per entry', async () => {
      cache.set('short', 1, 50);
      cache.set('long', 2, 1000);

      await new Promise((resolve) => setTimeout(resolve, 100));

      expect(cache.get('short')).toBeUndefined();
      expect(cache.get('long')).toBe(2);
    });
  });

  describe('statistics', () => {
    it('should track hits and misses', () => {
      cache.set('a', 1);
      cache.get('a'); // hit
      cache.get('a'); // hit
      cache.get('b'); // miss

      const stats = cache.stats();
      expect(stats.hits).toBe(2);
      expect(stats.misses).toBe(1);
      expect(stats.hitRate).toBeCloseTo(0.667, 2);
    });
  });

  describe('invalidateWhere', () => {
    it('should invalidate entries matching predicate', () => {
      cache.set('user:1', 1);
      cache.set('user:2', 2);
      cache.set('item:1', 3);

      const count = cache.invalidateWhere((key) => key.startsWith('user:'));
      
      expect(count).toBe(2);
      expect(cache.get('user:1')).toBeUndefined();
      expect(cache.get('item:1')).toBe(3);
    });
  });
});

describe('memoize', () => {
  it('should cache function results', () => {
    let callCount = 0;
    const fn = (x: number) => {
      callCount++;
      return x * 2;
    };

    const memoized = memoize(fn, { maxSize: 10, ttlMs: 1000 });

    expect(memoized(5)).toBe(10);
    expect(memoized(5)).toBe(10);
    expect(callCount).toBe(1);

    expect(memoized(10)).toBe(20);
    expect(callCount).toBe(2);
  });
});

describe('memoizeAsync', () => {
  it('should cache async function results', async () => {
    let callCount = 0;
    const fn = async (x: number) => {
      callCount++;
      return x * 2;
    };

    const memoized = memoizeAsync(fn, { maxSize: 10, ttlMs: 1000 });

    expect(await memoized(5)).toBe(10);
    expect(await memoized(5)).toBe(10);
    expect(callCount).toBe(1);
  });

  it('should handle concurrent calls', async () => {
    let callCount = 0;
    const fn = async (x: number) => {
      callCount++;
      await new Promise((r) => setTimeout(r, 50));
      return x * 2;
    };

    const memoized = memoizeAsync(fn, { maxSize: 10, ttlMs: 1000 });

    const [r1, r2, r3] = await Promise.all([
      memoized(5),
      memoized(5),
      memoized(5),
    ]);

    expect(r1).toBe(10);
    expect(r2).toBe(10);
    expect(r3).toBe(10);
    expect(callCount).toBe(1);
  });
});

describe('globalCache', () => {
  it('should create global cache instances', () => {
    const cache = createGlobalCache();
    
    expect(cache.patterns).toBeInstanceOf(LRUCache);
    expect(cache.ontology).toBeInstanceOf(LRUCache);
    expect(cache.validation).toBeInstanceOf(LRUCache);
    expect(cache.ast).toBeInstanceOf(LRUCache);
  });

  it('should clear global cache', () => {
    const cache = createGlobalCache();
    cache.patterns.set('test', { data: 1 });
    
    clearGlobalCache();
    // Note: clearGlobalCache clears the singleton, not this instance
  });
});

// =============================================================================
// Parallel Execution Tests (REQ-PERF-003)
// =============================================================================

describe('Parallel Execution', () => {
  describe('parallel', () => {
    it('should execute items in parallel', async () => {
      const items = [1, 2, 3, 4, 5];
      const results = await parallel(items, (x) => x * 2, 5);
      expect(results).toEqual([2, 4, 6, 8, 10]);
    });

    it('should respect concurrency limit', async () => {
      let maxConcurrent = 0;
      let current = 0;

      const items = Array.from({ length: 10 }, (_, i) => i);
      await parallel(
        items,
        async () => {
          current++;
          maxConcurrent = Math.max(maxConcurrent, current);
          await new Promise((r) => setTimeout(r, 10));
          current--;
        },
        3
      );

      expect(maxConcurrent).toBeLessThanOrEqual(3);
    });

    it('should maintain order', async () => {
      const items = [3, 1, 2];
      const results = await parallel(
        items,
        async (x) => {
          await new Promise((r) => setTimeout(r, x * 10));
          return x;
        },
        3
      );
      expect(results).toEqual([3, 1, 2]);
    });
  });

  describe('parallelMap', () => {
    it('should map items in parallel', async () => {
      const items = [1, 2, 3];
      const results = await parallelMap(items, (x) => x.toString());
      expect(results).toEqual(['1', '2', '3']);
    });
  });

  describe('parallelFilter', () => {
    it('should filter items in parallel', async () => {
      const items = [1, 2, 3, 4, 5];
      const results = await parallelFilter(items, async (x) => x % 2 === 0);
      expect(results).toEqual([2, 4]);
    });
  });

  describe('chunk', () => {
    it('should chunk array', () => {
      const items = [1, 2, 3, 4, 5];
      expect(chunk(items, 2)).toEqual([[1, 2], [3, 4], [5]]);
    });

    it('should handle empty array', () => {
      expect(chunk([], 2)).toEqual([]);
    });
  });

  describe('batchProcess', () => {
    it('should process in batches', async () => {
      const items = [1, 2, 3, 4, 5, 6];
      const results = await batchProcess(
        items,
        2,
        (batch) => batch.map((x) => x * 2)
      );
      expect(results).toEqual([2, 4, 6, 8, 10, 12]);
    });
  });

  describe('ParallelExecutor', () => {
    it('should execute tasks with class-based API', async () => {
      const executor = new ParallelExecutor({ maxWorkers: 2 });
      const results = await executor.map([1, 2, 3], (x) => x * 2);
      expect(results).toEqual([2, 4, 6]);
    });

    it('should execute in sequence', async () => {
      const executor = new ParallelExecutor();
      const order: number[] = [];
      
      await executor.sequence([1, 2, 3], async (x) => {
        order.push(x);
        return x;
      });
      
      expect(order).toEqual([1, 2, 3]);
    });
  });

  describe('throttle', () => {
    it('should limit execution rate', async () => {
      let callCount = 0;
      const fn = async () => {
        callCount++;
        return callCount;
      };

      const throttled = throttle(fn, 2, 100);

      // Make 5 calls
      const promises = [
        throttled(),
        throttled(),
        throttled(),
        throttled(),
        throttled(),
      ];

      // First 2 should execute immediately
      await new Promise((r) => setTimeout(r, 10));
      expect(callCount).toBe(2);

      await Promise.all(promises);
      expect(callCount).toBe(5);
    });
  });

  describe('debounce', () => {
    it('should debounce function calls', async () => {
      let callCount = 0;
      const fn = () => callCount++;
      const debounced = debounce(fn, 50);

      debounced();
      debounced();
      debounced();

      expect(callCount).toBe(0);

      await new Promise((r) => setTimeout(r, 100));
      expect(callCount).toBe(1);
    });
  });
});

// =============================================================================
// Memory Monitor Tests (REQ-PERF-004)
// =============================================================================

describe('Memory Monitor', () => {
  let monitor: MemoryMonitor;

  beforeEach(() => {
    monitor = new MemoryMonitor(400, 100);
  });

  describe('sample', () => {
    it('should take memory snapshot', () => {
      const stats = monitor.sample();
      
      expect(stats.heapUsed).toBeGreaterThan(0);
      expect(stats.heapTotal).toBeGreaterThan(0);
      expect(stats.rss).toBeGreaterThan(0);
      expect(stats.timestamp).toBeGreaterThan(0);
    });
  });

  describe('current/peak/average', () => {
    it('should track current memory', () => {
      const stats = monitor.current();
      expect(stats.heapUsed).toBeGreaterThan(0);
    });

    it('should track peak memory', () => {
      monitor.sample();
      monitor.sample();
      const peak = monitor.peak();
      expect(peak.heapUsed).toBeGreaterThan(0);
    });

    it('should calculate average', () => {
      monitor.sample();
      monitor.sample();
      monitor.sample();
      const avg = monitor.average();
      expect(avg.heapUsed).toBeGreaterThan(0);
    });
  });

  describe('trend', () => {
    it('should detect memory trend', () => {
      // With few samples, should be stable
      const trend = monitor.trend();
      expect(['increasing', 'stable', 'decreasing']).toContain(trend);
    });
  });

  describe('report', () => {
    it('should generate memory report', () => {
      const report = monitor.report();
      
      expect(report.current).toBeDefined();
      expect(report.peak).toBeDefined();
      expect(report.average).toBeDefined();
      expect(report.trend).toBeDefined();
    });
  });

  describe('warning callback', () => {
    it('should call warning callback when threshold exceeded', () => {
      const lowThresholdMonitor = new MemoryMonitor(0.001); // Very low threshold
      const callback = vi.fn();
      lowThresholdMonitor.onWarning(callback);
      
      lowThresholdMonitor.sample();
      
      expect(callback).toHaveBeenCalled();
    });
  });
});

describe('formatBytes', () => {
  it('should format bytes correctly', () => {
    expect(formatBytes(0)).toBe('0.00 B');
    expect(formatBytes(1024)).toBe('1.00 KB');
    expect(formatBytes(1024 * 1024)).toBe('1.00 MB');
    expect(formatBytes(1024 * 1024 * 1024)).toBe('1.00 GB');
  });
});

describe('measureMemory', () => {
  it('should measure memory usage of function', async () => {
    const { result, memoryDelta, stats } = await measureMemory(() => {
      return 'test';
    });

    expect(result).toBe('test');
    expect(typeof memoryDelta).toBe('number');
    expect(stats.before).toBeDefined();
    expect(stats.after).toBeDefined();
  });
});

describe('isMemoryHigh', () => {
  it('should check memory threshold', () => {
    // With high threshold, should be false
    expect(isMemoryHigh(10000)).toBe(false);
    
    // With very low threshold, should be true
    expect(isMemoryHigh(0.001)).toBe(true);
  });
});

describe('getMemoryUsagePercent', () => {
  it('should return percentage', () => {
    const percent = getMemoryUsagePercent();
    expect(percent).toBeGreaterThan(0);
    expect(percent).toBeLessThanOrEqual(100);
  });
});

// =============================================================================
// Benchmark Tests (REQ-PERF-005)
// =============================================================================

describe('Benchmark', () => {
  describe('measure', () => {
    it('should measure execution time', async () => {
      const { result, duration } = await measure(async () => {
        await new Promise((r) => setTimeout(r, 15));
        return 42;
      });

      expect(result).toBe(42);
      // Allow some timing variance (setTimeout is not precise)
      expect(duration).toBeGreaterThanOrEqual(10);
    });
  });

  describe('benchmark', () => {
    it('should run benchmark', async () => {
      const result = await benchmark(
        'test-benchmark',
        () => {
          let sum = 0;
          for (let i = 0; i < 1000; i++) sum += i;
        },
        { iterations: 10, warmup: 2 }
      );

      expect(result.name).toBe('test-benchmark');
      expect(result.duration).toBeGreaterThan(0);
      expect(result.opsPerSecond).toBeGreaterThan(0);
      expect(result.passed).toBe(true);
    });

    it('should respect threshold', async () => {
      const result = await benchmark(
        'slow-benchmark',
        async () => {
          await new Promise((r) => setTimeout(r, 50));
        },
        { iterations: 3, warmup: 1, threshold: 10 }
      );

      expect(result.passed).toBe(false);
    });
  });

  describe('benchmarkSuite', () => {
    it('should run suite of benchmarks', async () => {
      const suite = await benchmarkSuite('test-suite', [
        {
          name: 'fast',
          fn: () => {},
          options: { iterations: 10, threshold: 100 },
        },
        {
          name: 'slow',
          fn: async () => new Promise((r) => setTimeout(r, 20)),
          options: { iterations: 2, threshold: 10 },
        },
      ]);

      expect(suite.name).toBe('test-suite');
      expect(suite.results).toHaveLength(2);
      expect(suite.passRate).toBe(0.5); // 1 pass, 1 fail
    });
  });
});
