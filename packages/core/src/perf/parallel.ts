/**
 * Parallel Executor - Concurrent task execution
 *
 * @module perf/parallel
 * @traces DES-PERF-003, REQ-PERF-003
 * @pattern Thread Pool / Promise Pool
 */

import * as os from 'os';
import type { ParallelOptions } from './types.js';

/**
 * Execute tasks in parallel with concurrency limit
 *
 * @param items - Items to process
 * @param fn - Function to apply to each item
 * @param concurrency - Maximum concurrent executions
 * @returns Array of results in original order
 *
 * @example
 * ```typescript
 * const files = ['a.ts', 'b.ts', 'c.ts'];
 * const results = await parallel(files, async (file) => {
 *   return await parseFile(file);
 * }, 5);
 * ```
 */
export async function parallel<T, R>(
  items: T[],
  fn: (item: T, index: number) => R | Promise<R>,
  concurrency: number = 10
): Promise<R[]> {
  const results: R[] = new Array(items.length);
  const executing = new Set<Promise<void>>();
  let itemIndex = 0;

  for (const item of items) {
    const currentIndex = itemIndex++;
    
    const promise = (async () => {
      results[currentIndex] = await fn(item, currentIndex);
    })();

    const tracked = promise.then(() => {
      executing.delete(tracked);
    });

    executing.add(tracked);

    if (executing.size >= concurrency) {
      await Promise.race(executing);
    }
  }

  await Promise.all(executing);
  return results;
}

/**
 * Map items in parallel with concurrency limit
 *
 * @param items - Items to map
 * @param fn - Mapping function
 * @param options - Parallel options
 * @returns Mapped results
 */
export async function parallelMap<T, R>(
  items: T[],
  fn: (item: T, index: number) => R | Promise<R>,
  options: ParallelOptions = {}
): Promise<R[]> {
  const concurrency = options.concurrency ?? os.cpus().length;
  return parallel(items, fn, concurrency);
}

/**
 * Filter items in parallel
 *
 * @param items - Items to filter
 * @param predicate - Filter predicate
 * @param options - Parallel options
 * @returns Filtered items
 */
export async function parallelFilter<T>(
  items: T[],
  predicate: (item: T, index: number) => boolean | Promise<boolean>,
  options: ParallelOptions = {}
): Promise<T[]> {
  const concurrency = options.concurrency ?? os.cpus().length;
  
  const results = await parallel(
    items,
    async (item, index) => ({
      item,
      keep: await predicate(item, index),
    }),
    concurrency
  );

  return results.filter((r) => r.keep).map((r) => r.item);
}

/**
 * Execute functions in parallel and return first successful result
 *
 * @param fns - Functions to execute
 * @returns First successful result
 * @throws If all functions fail
 */
export async function parallelRace<R>(
  fns: Array<() => R | Promise<R>>
): Promise<R> {
  return Promise.race(fns.map((fn) => fn()));
}

/**
 * Execute functions in parallel and return all results (settled)
 *
 * @param fns - Functions to execute
 * @returns Array of settled results
 */
export async function parallelSettle<R>(
  fns: Array<() => R | Promise<R>>
): Promise<PromiseSettledResult<R>[]> {
  return Promise.allSettled(fns.map((fn) => fn()));
}

/**
 * Chunk array into smaller arrays
 *
 * @param items - Items to chunk
 * @param size - Chunk size
 * @returns Array of chunks
 */
export function chunk<T>(items: T[], size: number): T[][] {
  const chunks: T[][] = [];
  for (let i = 0; i < items.length; i += size) {
    chunks.push(items.slice(i, i + size));
  }
  return chunks;
}

/**
 * Process items in batches
 *
 * @param items - Items to process
 * @param batchSize - Number of items per batch
 * @param fn - Function to process each batch
 * @param options - Parallel options
 * @returns Flattened results
 */
export async function batchProcess<T, R>(
  items: T[],
  batchSize: number,
  fn: (batch: T[], batchIndex: number) => R[] | Promise<R[]>,
  options: ParallelOptions = {}
): Promise<R[]> {
  const batches = chunk(items, batchSize);
  const concurrency = options.concurrency ?? os.cpus().length;

  const batchResults = await parallel(batches, fn, concurrency);
  return batchResults.flat();
}

/**
 * Parallel executor class for more control
 */
export class ParallelExecutor {
  private readonly maxWorkers: number;
  private readonly taskTimeout: number;
  private activeCount = 0;

  constructor(options: ParallelOptions = {}) {
    this.maxWorkers = options.maxWorkers ?? os.cpus().length;
    this.taskTimeout = options.taskTimeout ?? 30000;
  }

  /**
   * Execute tasks in parallel
   */
  async map<T, R>(
    items: T[],
    fn: (item: T) => R | Promise<R>
  ): Promise<R[]> {
    return parallel(items, fn, this.maxWorkers);
  }

  /**
   * Execute single task with timeout
   */
  async run<R>(fn: () => R | Promise<R>): Promise<R> {
    const result = fn();
    const promise = result instanceof Promise ? result : Promise.resolve(result);
    return this.withTimeout(promise, this.taskTimeout);
  }

  /**
   * Execute tasks in sequence (no parallelism)
   */
  async sequence<T, R>(
    items: T[],
    fn: (item: T) => R | Promise<R>
  ): Promise<R[]> {
    const results: R[] = [];
    for (const item of items) {
      results.push(await fn(item));
    }
    return results;
  }

  /**
   * Add timeout to promise
   */
  private withTimeout<R>(promise: Promise<R>, ms: number): Promise<R> {
    return Promise.race([
      promise,
      new Promise<R>((_, reject) =>
        setTimeout(() => reject(new Error(`Task timeout after ${ms}ms`)), ms)
      ),
    ]);
  }

  /**
   * Get active task count
   */
  get active(): number {
    return this.activeCount;
  }

  /**
   * Get max workers
   */
  get workers(): number {
    return this.maxWorkers;
  }
}

/**
 * Create a throttled function that limits execution rate
 *
 * @param fn - Function to throttle
 * @param limit - Maximum executions per interval
 * @param interval - Interval in milliseconds
 * @returns Throttled function
 */
export function throttle<Args extends unknown[], R>(
  fn: (...args: Args) => R | Promise<R>,
  limit: number,
  interval: number
): (...args: Args) => Promise<R> {
  const queue: Array<{
    args: Args;
    resolve: (value: R) => void;
    reject: (error: Error) => void;
  }> = [];
  let activeCount = 0;
  let lastReset = Date.now();

  async function process(): Promise<void> {
    const now = Date.now();

    // Reset counter if interval passed
    if (now - lastReset >= interval) {
      activeCount = 0;
      lastReset = now;
    }

    // Process queue items within limit
    while (queue.length > 0 && activeCount < limit) {
      const item = queue.shift()!;
      activeCount++;

      try {
        const result = await fn(...item.args);
        item.resolve(result);
      } catch (error) {
        item.reject(error instanceof Error ? error : new Error(String(error)));
      }
    }

    // Schedule next batch if queue not empty
    if (queue.length > 0) {
      const delay = interval - (Date.now() - lastReset);
      setTimeout(process, Math.max(0, delay));
    }
  }

  return (...args: Args): Promise<R> => {
    return new Promise((resolve, reject) => {
      queue.push({ args, resolve, reject });
      process();
    });
  };
}

/**
 * Create a debounced function
 *
 * @param fn - Function to debounce
 * @param wait - Wait time in milliseconds
 * @returns Debounced function
 */
export function debounce<Args extends unknown[], R>(
  fn: (...args: Args) => R,
  wait: number
): (...args: Args) => void {
  let timeout: NodeJS.Timeout | null = null;

  return (...args: Args): void => {
    if (timeout) {
      clearTimeout(timeout);
    }

    timeout = setTimeout(() => {
      fn(...args);
      timeout = null;
    }, wait);
  };
}
