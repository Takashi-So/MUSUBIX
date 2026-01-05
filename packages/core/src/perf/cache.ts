/**
 * LRU Cache - Memory-efficient caching with TTL
 *
 * @module perf/cache
 * @traces DES-PERF-002, REQ-PERF-002
 * @pattern Cache-Aside / LRU
 */

import type { CacheOptions, CacheStats } from './types.js';

/**
 * Cache entry with value and expiration
 */
interface CacheEntry<V> {
  value: V;
  expires: number;
  size?: number;
}

/**
 * LRU Cache with TTL support
 *
 * Least Recently Used cache that automatically evicts old entries
 * and supports time-based expiration.
 */
export class LRUCache<K, V> {
  private cache: Map<K, CacheEntry<V>>;
  private readonly maxSize: number;
  private readonly ttlMs: number;
  private readonly onEvict?: (key: K, value: V) => void;

  // Stats
  private hits = 0;
  private misses = 0;
  private evictions = 0;

  constructor(options: CacheOptions) {
    this.cache = new Map();
    this.maxSize = options.maxSize;
    this.ttlMs = options.ttlMs;
    this.onEvict = options.onEvict as ((key: K, value: V) => void) | undefined;
  }

  /**
   * Get value from cache
   *
   * @param key - Cache key
   * @returns Cached value or undefined if not found/expired
   */
  get(key: K): V | undefined {
    const entry = this.cache.get(key);

    if (!entry) {
      this.misses++;
      return undefined;
    }

    // Check expiration
    if (Date.now() > entry.expires) {
      this.delete(key);
      this.misses++;
      return undefined;
    }

    this.hits++;

    // Move to end (most recently used)
    this.cache.delete(key);
    this.cache.set(key, entry);

    return entry.value;
  }

  /**
   * Set value in cache
   *
   * @param key - Cache key
   * @param value - Value to cache
   * @param ttlMs - Optional custom TTL for this entry
   */
  set(key: K, value: V, ttlMs?: number): void {
    // If key exists, delete to update position
    if (this.cache.has(key)) {
      this.cache.delete(key);
    }

    // Evict oldest if at capacity
    while (this.cache.size >= this.maxSize) {
      const oldest = this.cache.keys().next().value;
      if (oldest !== undefined) {
        this.evict(oldest);
      }
    }

    this.cache.set(key, {
      value,
      expires: Date.now() + (ttlMs ?? this.ttlMs),
    });
  }

  /**
   * Check if key exists and is not expired
   *
   * @param key - Cache key
   * @returns True if key exists and is valid
   */
  has(key: K): boolean {
    const entry = this.cache.get(key);
    if (!entry) return false;

    if (Date.now() > entry.expires) {
      this.delete(key);
      return false;
    }

    return true;
  }

  /**
   * Delete entry from cache
   *
   * @param key - Cache key
   * @returns True if entry was deleted
   */
  delete(key: K): boolean {
    return this.cache.delete(key);
  }

  /**
   * Evict entry and call callback
   */
  private evict(key: K): void {
    const entry = this.cache.get(key);
    if (entry && this.onEvict) {
      this.onEvict(key, entry.value);
    }
    this.cache.delete(key);
    this.evictions++;
  }

  /**
   * Invalidate entry (alias for delete)
   *
   * @param key - Cache key
   * @returns True if entry was invalidated
   */
  invalidate(key: K): boolean {
    return this.delete(key);
  }

  /**
   * Invalidate entries matching predicate
   *
   * @param predicate - Function to test keys
   * @returns Number of entries invalidated
   */
  invalidateWhere(predicate: (key: K) => boolean): number {
    let count = 0;
    for (const key of this.cache.keys()) {
      if (predicate(key)) {
        this.delete(key);
        count++;
      }
    }
    return count;
  }

  /**
   * Clear all entries
   */
  clear(): void {
    this.cache.clear();
    this.resetStats();
  }

  /**
   * Get cache statistics
   */
  stats(): CacheStats {
    const total = this.hits + this.misses;
    return {
      size: this.cache.size,
      maxSize: this.maxSize,
      hits: this.hits,
      misses: this.misses,
      hitRate: total > 0 ? this.hits / total : 0,
      evictions: this.evictions,
    };
  }

  /**
   * Reset statistics
   */
  resetStats(): void {
    this.hits = 0;
    this.misses = 0;
    this.evictions = 0;
  }

  /**
   * Get number of entries
   */
  get size(): number {
    return this.cache.size;
  }

  /**
   * Prune expired entries
   *
   * @returns Number of entries pruned
   */
  prune(): number {
    const now = Date.now();
    let count = 0;

    for (const [key, entry] of this.cache.entries()) {
      if (now > entry.expires) {
        this.delete(key);
        count++;
      }
    }

    return count;
  }

  /**
   * Get all keys
   */
  keys(): IterableIterator<K> {
    return this.cache.keys();
  }

  /**
   * Get all values (non-expired only)
   */
  *values(): IterableIterator<V> {
    const now = Date.now();
    for (const [key, entry] of this.cache.entries()) {
      if (now <= entry.expires) {
        yield entry.value;
      } else {
        this.delete(key);
      }
    }
  }

  /**
   * Get entries as array
   */
  entries(): Array<[K, V]> {
    const result: Array<[K, V]> = [];
    const now = Date.now();

    for (const [key, entry] of this.cache.entries()) {
      if (now <= entry.expires) {
        result.push([key, entry.value]);
      }
    }

    return result;
  }
}

/**
 * Memoize function results with LRU cache
 *
 * @param fn - Function to memoize
 * @param options - Cache options
 * @param keyFn - Optional function to generate cache key from arguments
 * @returns Memoized function
 */
export function memoize<Args extends unknown[], R>(
  fn: (...args: Args) => R,
  options: CacheOptions,
  keyFn?: (...args: Args) => string
): (...args: Args) => R {
  const cache = new LRUCache<string, R>(options);
  const getKey = keyFn ?? ((...args: Args) => JSON.stringify(args));

  return (...args: Args): R => {
    const key = getKey(...args);
    const cached = cache.get(key);

    if (cached !== undefined) {
      return cached;
    }

    const result = fn(...args);
    cache.set(key, result);
    return result;
  };
}

/**
 * Async memoize function results with LRU cache
 *
 * @param fn - Async function to memoize
 * @param options - Cache options
 * @param keyFn - Optional function to generate cache key from arguments
 * @returns Memoized async function
 */
export function memoizeAsync<Args extends unknown[], R>(
  fn: (...args: Args) => Promise<R>,
  options: CacheOptions,
  keyFn?: (...args: Args) => string
): (...args: Args) => Promise<R> {
  const cache = new LRUCache<string, R>(options);
  const pending = new Map<string, Promise<R>>();
  const getKey = keyFn ?? ((...args: Args) => JSON.stringify(args));

  return async (...args: Args): Promise<R> => {
    const key = getKey(...args);
    const cached = cache.get(key);

    if (cached !== undefined) {
      return cached;
    }

    // Check if already computing
    const pendingResult = pending.get(key);
    if (pendingResult) {
      return pendingResult;
    }

    // Compute and cache
    const promise = fn(...args).then((result) => {
      cache.set(key, result);
      pending.delete(key);
      return result;
    });

    pending.set(key, promise);
    return promise;
  };
}

/**
 * Create global cache instances
 */
export function createGlobalCache(): {
  patterns: LRUCache<string, unknown>;
  ontology: LRUCache<string, unknown>;
  validation: LRUCache<string, unknown>;
  ast: LRUCache<string, unknown>;
} {
  return {
    patterns: new LRUCache({ maxSize: 1000, ttlMs: 5 * 60 * 1000 }), // 5 min
    ontology: new LRUCache({ maxSize: 500, ttlMs: 10 * 60 * 1000 }), // 10 min
    validation: new LRUCache({ maxSize: 200, ttlMs: 60 * 1000 }), // 1 min
    ast: new LRUCache({ maxSize: 100, ttlMs: 30 * 60 * 1000 }), // 30 min
  };
}

// Global cache singleton
let globalCacheInstance: ReturnType<typeof createGlobalCache> | null = null;

/**
 * Get or create global cache instance
 */
export function getGlobalCache(): ReturnType<typeof createGlobalCache> {
  if (!globalCacheInstance) {
    globalCacheInstance = createGlobalCache();
  }
  return globalCacheInstance;
}

/**
 * Clear global cache
 */
export function clearGlobalCache(): void {
  if (globalCacheInstance) {
    globalCacheInstance.patterns.clear();
    globalCacheInstance.ontology.clear();
    globalCacheInstance.validation.clear();
    globalCacheInstance.ast.clear();
  }
}
