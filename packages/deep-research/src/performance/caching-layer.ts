/**
 * @fileoverview CachingLayer - LRU cache with TTL for search results
 * @module @nahisaho/musubix-deep-research/performance
 * @version 1.0.0
 * 
 * REQ: REQ-DR-NFR-004 (Performance Requirements)
 * TSK: TSK-DR-017 (CachingLayer Implementation)
 * ADR: ADR-v3.4.0-001 (Performance Optimization)
 */

/**
 * Cache entry with TTL
 */
interface CacheEntry<T> {
  /** Cached value */
  value: T;
  /** Expiration timestamp (ms since epoch) */
  expiresAt: number;
  /** Last access timestamp */
  lastAccessedAt: number;
  /** Creation timestamp */
  createdAt: number;
}

/**
 * Cache statistics
 */
export interface CacheStats {
  /** Total cache hits */
  hits: number;
  /** Total cache misses */
  misses: number;
  /** Current cache size */
  size: number;
  /** Maximum cache size */
  maxSize: number;
  /** Hit rate (0-1) */
  hitRate: number;
  /** Total evictions */
  evictions: number;
}

/**
 * Options for CachingLayer
 */
export interface CachingLayerOptions {
  /** Maximum number of entries (default: 100) */
  maxSize?: number;
  /** Time-to-live in milliseconds (default: 300000 = 5 minutes) */
  ttlMs?: number;
  /** Enable auto-cleanup of expired entries (default: true) */
  autoCleanup?: boolean;
  /** Cleanup interval in milliseconds (default: 60000 = 1 minute) */
  cleanupIntervalMs?: number;
}

/**
 * CachingLayer - LRU cache with TTL support
 * 
 * Design Pattern: LRU (Least Recently Used) eviction policy
 * 
 * Features:
 * - LRU eviction when cache is full
 * - TTL-based expiration
 * - Automatic cleanup of expired entries
 * - Hit rate tracking
 * 
 * @example
 * ```typescript
 * const cache = new CachingLayer<string, SearchResult>({
 *   maxSize: 50,
 *   ttlMs: 300000, // 5 minutes
 * });
 * 
 * // Store result
 * cache.set('query:typescript', result);
 * 
 * // Retrieve result
 * const cached = cache.get('query:typescript');
 * if (cached) {
 *   console.log('Cache hit:', cached);
 * }
 * 
 * // Check stats
 * const stats = cache.getStats();
 * console.log(`Hit rate: ${(stats.hitRate * 100).toFixed(1)}%`);
 * ```
 */
export class CachingLayer<K, V> {
  private cache: Map<K, CacheEntry<V>>;
  private readonly maxSize: number;
  private readonly ttlMs: number;
  private hits = 0;
  private misses = 0;
  private evictions = 0;
  private cleanupTimer?: NodeJS.Timeout;

  constructor(options: CachingLayerOptions = {}) {
    this.maxSize = options.maxSize ?? 100;
    this.ttlMs = options.ttlMs ?? 300000; // 5 minutes default
    this.cache = new Map();

    if (this.maxSize < 1) {
      throw new Error('maxSize must be at least 1');
    }

    if (this.ttlMs < 0) {
      throw new Error('ttlMs must be non-negative');
    }

    // Start auto-cleanup if enabled
    if (options.autoCleanup !== false) {
      const cleanupInterval = options.cleanupIntervalMs ?? 60000; // 1 minute default
      this.startCleanup(cleanupInterval);
    }
  }

  /**
   * Get value from cache
   * 
   * @returns Value if found and not expired, undefined otherwise
   */
  get(key: K): V | undefined {
    const entry = this.cache.get(key);

    if (!entry) {
      this.misses++;
      return undefined;
    }

    // Check if expired
    if (this.isExpired(entry)) {
      this.cache.delete(key);
      this.misses++;
      return undefined;
    }

    // Update LRU order by re-inserting
    this.cache.delete(key);
    entry.lastAccessedAt = Date.now();
    this.cache.set(key, entry);

    this.hits++;
    return entry.value;
  }

  /**
   * Set value in cache
   * 
   * If cache is full, evicts least recently used entry.
   */
  set(key: K, value: V, customTtlMs?: number): void {
    const now = Date.now();
    const ttl = customTtlMs ?? this.ttlMs;

    // If key exists, update it
    if (this.cache.has(key)) {
      this.cache.delete(key);
    }
    // If cache is full, evict LRU entry
    else if (this.cache.size >= this.maxSize) {
      const firstKey = this.cache.keys().next().value;
      if (firstKey !== undefined) {
        this.cache.delete(firstKey);
        this.evictions++;
      }
    }

    const entry: CacheEntry<V> = {
      value,
      expiresAt: now + ttl,
      lastAccessedAt: now,
      createdAt: now,
    };

    this.cache.set(key, entry);
  }

  /**
   * Check if key exists in cache (and not expired)
   */
  has(key: K): boolean {
    const entry = this.cache.get(key);
    if (!entry) return false;

    if (this.isExpired(entry)) {
      this.cache.delete(key);
      return false;
    }

    return true;
  }

  /**
   * Delete entry from cache
   * 
   * @returns true if entry existed and was deleted
   */
  delete(key: K): boolean {
    return this.cache.delete(key);
  }

  /**
   * Clear all entries from cache
   */
  clear(): void {
    this.cache.clear();
    this.hits = 0;
    this.misses = 0;
    this.evictions = 0;
  }

  /**
   * Get current cache size
   */
  size(): number {
    return this.cache.size;
  }

  /**
   * Get all keys in cache (excluding expired)
   */
  keys(): K[] {
    const keys: K[] = [];
    for (const [key, entry] of this.cache.entries()) {
      if (!this.isExpired(entry)) {
        keys.push(key);
      }
    }
    return keys;
  }

  /**
   * Get cache statistics
   */
  getStats(): CacheStats {
    const total = this.hits + this.misses;
    return {
      hits: this.hits,
      misses: this.misses,
      size: this.cache.size,
      maxSize: this.maxSize,
      hitRate: total > 0 ? this.hits / total : 0,
      evictions: this.evictions,
    };
  }

  /**
   * Remove expired entries
   * 
   * @returns Number of entries removed
   */
  cleanup(): number {
    let removed = 0;
    for (const [key, entry] of this.cache.entries()) {
      if (this.isExpired(entry)) {
        this.cache.delete(key);
        removed++;
      }
    }
    return removed;
  }

  /**
   * Stop auto-cleanup timer
   */
  dispose(): void {
    if (this.cleanupTimer) {
      clearInterval(this.cleanupTimer);
      this.cleanupTimer = undefined;
    }
  }

  /**
   * Check if entry is expired
   */
  private isExpired(entry: CacheEntry<V>): boolean {
    return Date.now() > entry.expiresAt;
  }

  /**
   * Start automatic cleanup of expired entries
   */
  private startCleanup(intervalMs: number): void {
    this.cleanupTimer = setInterval(() => {
      this.cleanup();
    }, intervalMs);

    // Prevent timer from keeping process alive
    if (this.cleanupTimer.unref) {
      this.cleanupTimer.unref();
    }
  }
}

/**
 * Create a CachingLayer instance
 */
export function createCachingLayer<K, V>(
  options?: CachingLayerOptions
): CachingLayer<K, V> {
  return new CachingLayer<K, V>(options);
}
