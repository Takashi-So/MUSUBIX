# DES-PERF-v1.5.1: Performance Optimization Design

## Overview

Performance Optimizationの設計ドキュメント。

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    Performance Layer                         │
├─────────────┬─────────────┬─────────────┬──────────────────┤
│ LazyLoader  │ CacheManager│ ParallelExec│ MemoryMonitor    │
├─────────────┴─────────────┴─────────────┴──────────────────┤
│                    Core Modules                              │
│   (CLI, Validators, CodeGen, Learning, Symbolic)            │
└─────────────────────────────────────────────────────────────┘
```

## Components

### DES-PERF-001: LazyLoader

**Pattern**: Proxy / Virtual Proxy

```typescript
// packages/core/src/perf/lazy-loader.ts

/**
 * Lazy module loader with proxy pattern
 */
export function lazyImport<T>(
  importFn: () => Promise<T>,
  moduleId: string
): T {
  let cached: T | undefined;
  let loading: Promise<T> | undefined;

  return new Proxy({} as T, {
    get(_, prop) {
      if (!cached) {
        if (!loading) {
          loading = importFn().then(m => { cached = m; return m; });
        }
        throw new LazyNotLoadedError(moduleId, prop);
      }
      return (cached as any)[prop];
    }
  });
}

// Async version with automatic loading
export async function lazyLoad<T>(
  importFn: () => Promise<T>
): Promise<T> {
  return importFn();
}
```

**適用対象**:

| モジュール | 遅延読み込み | 理由 |
|-----------|-------------|------|
| `validators/ears` | ✅ | 要件コマンド時のみ必要 |
| `codegen/*` | ✅ | codegenコマンド時のみ必要 |
| `symbolic/*` | ✅ | 推論時のみ必要 |
| `cli/base` | ❌ | 常に必要 |
| `types/*` | ❌ | 型定義は即時必要 |

### DES-PERF-002: CacheManager

**Pattern**: Cache-Aside / LRU Cache

```typescript
// packages/core/src/perf/cache.ts

export interface CacheOptions {
  maxSize: number;      // 最大エントリ数
  ttlMs: number;        // Time-to-live (ms)
  onEvict?: (key: string, value: unknown) => void;
}

export class LRUCache<K, V> {
  private cache: Map<K, { value: V; expires: number }>;
  private maxSize: number;
  private ttlMs: number;

  constructor(options: CacheOptions) {
    this.cache = new Map();
    this.maxSize = options.maxSize;
    this.ttlMs = options.ttlMs;
  }

  get(key: K): V | undefined {
    const entry = this.cache.get(key);
    if (!entry) return undefined;
    if (Date.now() > entry.expires) {
      this.cache.delete(key);
      return undefined;
    }
    // Move to end (most recently used)
    this.cache.delete(key);
    this.cache.set(key, entry);
    return entry.value;
  }

  set(key: K, value: V): void {
    // Evict oldest if at capacity
    if (this.cache.size >= this.maxSize) {
      const oldest = this.cache.keys().next().value;
      this.cache.delete(oldest);
    }
    this.cache.set(key, {
      value,
      expires: Date.now() + this.ttlMs
    });
  }

  invalidate(key: K): boolean {
    return this.cache.delete(key);
  }

  clear(): void {
    this.cache.clear();
  }

  stats(): CacheStats {
    return {
      size: this.cache.size,
      maxSize: this.maxSize,
      hitRate: this.hitCount / (this.hitCount + this.missCount)
    };
  }
}
```

**キャッシュ設定**:

| キャッシュ名 | maxSize | TTL | 用途 |
|-------------|---------|-----|------|
| `patternCache` | 1000 | 5min | パターン検索結果 |
| `ontologyCache` | 500 | 10min | SPARQLクエリ結果 |
| `validationCache` | 200 | 1min | バリデーション結果 |
| `astCache` | 100 | 30min | AST解析結果 |

### DES-PERF-003: ParallelExecutor

**Pattern**: Thread Pool / Worker Threads

```typescript
// packages/core/src/perf/parallel.ts

import { Worker, isMainThread, parentPort, workerData } from 'worker_threads';

export interface ParallelOptions {
  maxWorkers?: number;    // デフォルト: CPU数
  taskTimeout?: number;   // タスクタイムアウト (ms)
}

export class ParallelExecutor {
  private workers: Worker[] = [];
  private taskQueue: Task[] = [];
  private maxWorkers: number;

  constructor(options: ParallelOptions = {}) {
    this.maxWorkers = options.maxWorkers ?? os.cpus().length;
  }

  /**
   * Execute tasks in parallel
   */
  async map<T, R>(
    items: T[],
    fn: (item: T) => R | Promise<R>
  ): Promise<R[]> {
    // For small arrays, use Promise.all
    if (items.length < this.maxWorkers * 2) {
      return Promise.all(items.map(fn));
    }

    // For larger arrays, use worker threads
    return this.executeWithWorkers(items, fn);
  }

  /**
   * Execute single heavy task in worker
   */
  async runInWorker<T>(
    task: () => T | Promise<T>
  ): Promise<T> {
    // Serialize and run in worker thread
  }
}

// Utility for simple parallel execution
export async function parallel<T, R>(
  items: T[],
  fn: (item: T) => R | Promise<R>,
  concurrency: number = 10
): Promise<R[]> {
  const results: R[] = [];
  const executing: Promise<void>[] = [];

  for (const item of items) {
    const p = Promise.resolve(fn(item)).then(r => {
      results.push(r);
    });
    executing.push(p);

    if (executing.length >= concurrency) {
      await Promise.race(executing);
    }
  }

  await Promise.all(executing);
  return results;
}
```

### DES-PERF-004: MemoryMonitor

**Pattern**: Observer / Health Check

```typescript
// packages/core/src/perf/memory.ts

export interface MemoryStats {
  heapUsed: number;
  heapTotal: number;
  external: number;
  rss: number;
  timestamp: number;
}

export class MemoryMonitor {
  private samples: MemoryStats[] = [];
  private maxSamples: number = 100;
  private warningThreshold: number;

  constructor(warningThresholdMB: number = 400) {
    this.warningThreshold = warningThresholdMB * 1024 * 1024;
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
      timestamp: Date.now()
    };

    this.samples.push(stats);
    if (this.samples.length > this.maxSamples) {
      this.samples.shift();
    }

    if (stats.heapUsed > this.warningThreshold) {
      this.emitWarning(stats);
    }

    return stats;
  }

  /**
   * Force garbage collection (if --expose-gc)
   */
  gc(): void {
    if (global.gc) {
      global.gc();
    }
  }

  /**
   * Get memory report
   */
  report(): MemoryReport {
    return {
      current: this.sample(),
      peak: this.getPeak(),
      average: this.getAverage(),
      trend: this.getTrend()
    };
  }
}
```

### DES-PERF-005: Benchmark CLI

```typescript
// packages/core/src/cli/commands/perf.ts

export function registerPerfCommand(program: Command): void {
  const perf = program
    .command('perf')
    .description('Performance benchmarks and monitoring');

  perf
    .command('benchmark')
    .description('Run all benchmarks')
    .action(runAllBenchmarks);

  perf
    .command('startup')
    .description('Measure startup time')
    .action(measureStartup);

  perf
    .command('memory')
    .description('Show memory usage')
    .action(showMemoryUsage);

  perf
    .command('cache-stats')
    .description('Show cache statistics')
    .action(showCacheStats);
}
```

## File Structure

```
packages/core/src/perf/
├── index.ts              # エクスポート
├── lazy-loader.ts        # 遅延読み込み
├── cache.ts              # LRUキャッシュ
├── parallel.ts           # 並列実行
├── memory.ts             # メモリ監視
├── benchmark.ts          # ベンチマーク実行
└── __tests__/
    ├── lazy-loader.test.ts
    ├── cache.test.ts
    ├── parallel.test.ts
    └── memory.test.ts
```

## Integration Points

### CLI統合

```typescript
// packages/core/src/cli/index.ts
import { registerPerfCommand } from './commands/perf.js';

// ...
registerPerfCommand(program);
```

### グローバルキャッシュ

```typescript
// packages/core/src/index.ts
import { createGlobalCache } from './perf/cache.js';

export const globalCache = createGlobalCache();
```

## Performance Targets

| ベンチマーク | 現状 | 目標 | 方法 |
|-------------|------|------|------|
| `musubix --help` | 800ms | 400ms | Lazy loading |
| 要件分析(100件) | 2000ms | 1000ms | キャッシュ + 並列 |
| パターン検索 | 500ms | 200ms | キャッシュ |
| メモリ(アイドル) | 80MB | 50MB | 遅延読み込み |

---

**Created**: 2026-01-06  
**Status**: Draft  
**Traces**: REQ-PERF-001〜005
