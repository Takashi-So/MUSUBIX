/**
 * Pattern Cache Module
 *
 * LRU cache with TTL for pattern storage and retrieval.
 *
 * @packageDocumentation
 * @module learning/pattern-cache
 * @see REQ-NFR-002 - Command response performance
 * @see DES-NFR-002 - Performance optimization design
 */

/**
 * Cache entry with metadata
 */
interface CacheEntry<V> {
  value: V;
  createdAt: number;
  accessedAt: number;
  accessCount: number;
  size?: number;
}

/**
 * Cache statistics
 */
export interface CacheStats {
  /** Number of items in cache */
  size: number;
  /** Maximum cache size */
  maxSize: number;
  /** Cache hits */
  hits: number;
  /** Cache misses */
  misses: number;
  /** Hit ratio (0-1) */
  hitRatio: number;
  /** Total memory size (if tracked) */
  totalMemory?: number;
  /** Number of evictions */
  evictions: number;
}

/**
 * Cache options
 */
export interface CacheOptions {
  /** Maximum number of items */
  maxSize?: number;
  /** Time to live in milliseconds */
  ttlMs?: number;
  /** Whether to update TTL on access */
  updateTtlOnAccess?: boolean;
  /** Size calculator for memory-based eviction */
  sizeCalculator?: <V>(value: V) => number;
  /** Maximum total memory size */
  maxMemorySize?: number;
}

/**
 * LRU Cache with TTL support
 *
 * @example
 * ```typescript
 * const cache = new LRUCache<string, Pattern>({
 *   maxSize: 100,
 *   ttlMs: 60000, // 1 minute
 * });
 *
 * cache.set('pattern-1', patternData);
 * const pattern = cache.get('pattern-1');
 * ```
 */
export class LRUCache<K, V> {
  private cache: Map<K, CacheEntry<V>> = new Map();
  private maxSize: number;
  private ttlMs: number | undefined;
  private updateTtlOnAccess: boolean;
  private sizeCalculator?: (value: V) => number;
  private maxMemorySize?: number;
  private currentMemorySize: number = 0;

  // Statistics
  private hits: number = 0;
  private misses: number = 0;
  private evictions: number = 0;

  constructor(options: CacheOptions = {}) {
    this.maxSize = options.maxSize ?? 1000;
    this.ttlMs = options.ttlMs;
    this.updateTtlOnAccess = options.updateTtlOnAccess ?? false;
    this.sizeCalculator = options.sizeCalculator;
    this.maxMemorySize = options.maxMemorySize;
  }

  /**
   * Get a value from the cache
   */
  get(key: K): V | undefined {
    const entry = this.cache.get(key);

    if (!entry) {
      this.misses++;
      return undefined;
    }

    // Check TTL
    if (this.ttlMs && Date.now() - entry.createdAt > this.ttlMs) {
      this.delete(key);
      this.misses++;
      return undefined;
    }

    // Update access info
    entry.accessedAt = Date.now();
    entry.accessCount++;

    if (this.updateTtlOnAccess) {
      entry.createdAt = Date.now();
    }

    // Move to end (most recently used)
    this.cache.delete(key);
    this.cache.set(key, entry);

    this.hits++;
    return entry.value;
  }

  /**
   * Set a value in the cache
   */
  set(key: K, value: V): void {
    // Delete existing entry if present
    if (this.cache.has(key)) {
      this.delete(key);
    }

    const size = this.sizeCalculator ? this.sizeCalculator(value) : undefined;

    // Evict if necessary
    this.evictIfNeeded(size);

    const entry: CacheEntry<V> = {
      value,
      createdAt: Date.now(),
      accessedAt: Date.now(),
      accessCount: 0,
      size,
    };

    this.cache.set(key, entry);

    if (size !== undefined) {
      this.currentMemorySize += size;
    }
  }

  /**
   * Check if a key exists in the cache
   */
  has(key: K): boolean {
    const entry = this.cache.get(key);
    if (!entry) return false;

    // Check TTL
    if (this.ttlMs && Date.now() - entry.createdAt > this.ttlMs) {
      this.delete(key);
      return false;
    }

    return true;
  }

  /**
   * Delete a key from the cache
   */
  delete(key: K): boolean {
    const entry = this.cache.get(key);
    if (!entry) return false;

    if (entry.size !== undefined) {
      this.currentMemorySize -= entry.size;
    }

    return this.cache.delete(key);
  }

  /**
   * Clear the cache
   */
  clear(): void {
    this.cache.clear();
    this.currentMemorySize = 0;
    this.hits = 0;
    this.misses = 0;
    this.evictions = 0;
  }

  /**
   * Get the current size of the cache
   */
  get size(): number {
    return this.cache.size;
  }

  /**
   * Get cache statistics
   */
  getStats(): CacheStats {
    const total = this.hits + this.misses;
    return {
      size: this.cache.size,
      maxSize: this.maxSize,
      hits: this.hits,
      misses: this.misses,
      hitRatio: total > 0 ? this.hits / total : 0,
      totalMemory: this.sizeCalculator ? this.currentMemorySize : undefined,
      evictions: this.evictions,
    };
  }

  /**
   * Get all keys in the cache
   */
  keys(): K[] {
    return Array.from(this.cache.keys());
  }

  /**
   * Get all values in the cache
   */
  values(): V[] {
    return Array.from(this.cache.values()).map((entry) => entry.value);
  }

  /**
   * Get all entries
   */
  entries(): Array<[K, V]> {
    return Array.from(this.cache.entries()).map(([k, v]) => [k, v.value]);
  }

  /**
   * Iterate over cache entries
   */
  forEach(callback: (value: V, key: K) => void): void {
    this.cache.forEach((entry, key) => {
      callback(entry.value, key);
    });
  }

  /**
   * Evict entries if cache is full
   */
  private evictIfNeeded(newEntrySize?: number): void {
    // Evict by count
    while (this.cache.size >= this.maxSize) {
      this.evictOne();
    }

    // Evict by memory
    if (this.maxMemorySize && newEntrySize !== undefined) {
      while (
        this.currentMemorySize + newEntrySize > this.maxMemorySize &&
        this.cache.size > 0
      ) {
        this.evictOne();
      }
    }
  }

  /**
   * Evict the least recently used entry
   */
  private evictOne(): void {
    // Map maintains insertion order, first key is LRU
    const firstKey = this.cache.keys().next().value;
    if (firstKey !== undefined) {
      this.delete(firstKey);
      this.evictions++;
    }
  }

  /**
   * Remove expired entries
   */
  prune(): number {
    if (!this.ttlMs) return 0;

    const now = Date.now();
    let pruned = 0;

    for (const [key, entry] of this.cache) {
      if (now - entry.createdAt > this.ttlMs) {
        this.delete(key);
        pruned++;
      }
    }

    return pruned;
  }
}

/**
 * Pattern-specific cache with category support
 */
export class PatternCache {
  private caches: Map<string, LRUCache<string, unknown>> = new Map();
  private defaultOptions: CacheOptions;

  constructor(options: CacheOptions = {}) {
    this.defaultOptions = {
      maxSize: 100,
      ttlMs: 300000, // 5 minutes default
      ...options,
    };
  }

  /**
   * Get or create a cache for a category
   */
  private getCache<V>(category: string): LRUCache<string, V> {
    if (!this.caches.has(category)) {
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      const cache = new LRUCache<string, V>(this.defaultOptions as any);
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      this.caches.set(category, cache as any);
    }
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    return this.caches.get(category) as any;
  }

  /**
   * Get a pattern from cache
   */
  get<V>(category: string, key: string): V | undefined {
    return this.getCache<V>(category).get(key);
  }

  /**
   * Set a pattern in cache
   */
  set<V>(category: string, key: string, value: V): void {
    this.getCache<V>(category).set(key, value);
  }

  /**
   * Check if a pattern exists in cache
   */
  has(category: string, key: string): boolean {
    return this.getCache(category).has(key);
  }

  /**
   * Delete a pattern from cache
   */
  delete(category: string, key: string): boolean {
    return this.getCache(category).delete(key);
  }

  /**
   * Clear a specific category cache
   */
  clearCategory(category: string): void {
    const cache = this.caches.get(category);
    if (cache) {
      cache.clear();
    }
  }

  /**
   * Clear all caches
   */
  clearAll(): void {
    for (const cache of this.caches.values()) {
      cache.clear();
    }
  }

  /**
   * Get statistics for all categories
   */
  getStats(): Record<string, CacheStats> {
    const stats: Record<string, CacheStats> = {};
    for (const [category, cache] of this.caches) {
      stats[category] = cache.getStats();
    }
    return stats;
  }

  /**
   * Get list of categories
   */
  getCategories(): string[] {
    return Array.from(this.caches.keys());
  }

  /**
   * Prune expired entries from all caches
   */
  pruneAll(): number {
    let total = 0;
    for (const cache of this.caches.values()) {
      total += cache.prune();
    }
    return total;
  }
}

/**
 * Global pattern cache instance
 */
export const globalPatternCache = new PatternCache({
  maxSize: 500,
  ttlMs: 600000, // 10 minutes
});

/**
 * Memoization decorator with cache
 */
export function memoize<Args extends unknown[], R>(
  fn: (...args: Args) => R,
  options: {
    keyFn?: (...args: Args) => string;
    cache?: LRUCache<string, R>;
  } = {}
): (...args: Args) => R {
  const cache = options.cache ?? new LRUCache<string, R>({ maxSize: 100 });
  const keyFn = options.keyFn ?? ((...args: Args) => JSON.stringify(args));

  return (...args: Args): R => {
    const key = keyFn(...args);
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
 * Async memoization decorator with cache
 */
export function memoizeAsync<Args extends unknown[], R>(
  fn: (...args: Args) => Promise<R>,
  options: {
    keyFn?: (...args: Args) => string;
    cache?: LRUCache<string, R>;
  } = {}
): (...args: Args) => Promise<R> {
  const cache = options.cache ?? new LRUCache<string, R>({ maxSize: 100 });
  const keyFn = options.keyFn ?? ((...args: Args) => JSON.stringify(args));
  const pending = new Map<string, Promise<R>>();

  return async (...args: Args): Promise<R> => {
    const key = keyFn(...args);
    const cached = cache.get(key);

    if (cached !== undefined) {
      return cached;
    }

    // Check if already loading
    const pendingResult = pending.get(key);
    if (pendingResult) {
      return pendingResult;
    }

    // Start loading
    const promise = fn(...args).then((result) => {
      cache.set(key, result);
      pending.delete(key);
      return result;
    });

    pending.set(key, promise);
    return promise;
  };
}
