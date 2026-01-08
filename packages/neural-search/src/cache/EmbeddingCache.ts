/**
 * EmbeddingCache - LRU Cache for Embeddings
 * @module @nahisaho/musubix-neural-search
 * @see TSK-NS-105
 * @see DES-NS-105
 * @see REQ-NS-105
 *
 * LRUキャッシュ（最大10,000エントリ）
 * - 80%以上のヒット率目標
 * - TTLサポート
 * - バッチ操作
 */

import type { Embedding } from '../types.js';

// =============================================================================
// Types
// =============================================================================

/**
 * Configuration for EmbeddingCache
 */
export interface EmbeddingCacheConfig {
  /** Maximum number of entries (default: 10000) */
  maxSize?: number;
  /** Time-to-live in milliseconds (default: 0 = no expiry) */
  ttlMs?: number;
}

/**
 * Cache entry with metadata
 */
interface CacheEntry {
  /** The embedding value */
  value: Embedding;
  /** Timestamp of when entry was added */
  addedAt: number;
  /** Timestamp of last access */
  lastAccessedAt: number;
}

/**
 * Cache statistics
 */
export interface CacheStatistics {
  /** Current cache size */
  size: number;
  /** Maximum cache size */
  maxSize: number;
  /** Number of cache hits */
  hits: number;
  /** Number of cache misses */
  misses: number;
  /** Hit rate (0-1) */
  hitRate: number;
  /** Number of evictions */
  evictions: number;
}

/**
 * EmbeddingCache interface
 */
export interface EmbeddingCache {
  // Basic operations
  get(key: string): Embedding | undefined;
  set(key: string, value: Embedding): void;
  has(key: string): boolean;
  delete(key: string): boolean;
  clear(): void;
  size(): number;

  // Batch operations
  getMany(keys: string[]): Map<string, Embedding>;
  setMany(entries: Map<string, Embedding>): void;

  // Statistics
  getHitRate(): number;
  getStatistics(): CacheStatistics;
  resetStatistics(): void;

  // Serialization
  toJSON(): string;
  fromJSON(json: string): void;
}

// =============================================================================
// Implementation
// =============================================================================

/**
 * Default EmbeddingCache implementation using LRU eviction
 */
export class DefaultEmbeddingCache implements EmbeddingCache {
  private config: Required<EmbeddingCacheConfig>;
  private cache: Map<string, CacheEntry> = new Map();
  private accessOrder: string[] = [];

  // Statistics
  private hits = 0;
  private misses = 0;
  private evictions = 0;

  constructor(config: EmbeddingCacheConfig = {}) {
    this.config = {
      maxSize: config.maxSize ?? 10000,
      ttlMs: config.ttlMs ?? 0,
    };
  }

  // =========================================================================
  // Basic Operations
  // =========================================================================

  get(key: string): Embedding | undefined {
    const entry = this.cache.get(key);

    if (!entry) {
      this.misses++;
      return undefined;
    }

    // Check TTL
    if (this.isExpired(entry)) {
      this.delete(key);
      this.misses++;
      return undefined;
    }

    // Update access order (move to end = most recently used)
    this.updateAccessOrder(key);
    entry.lastAccessedAt = Date.now();

    this.hits++;
    return entry.value;
  }

  set(key: string, value: Embedding): void {
    // Check if key already exists
    const exists = this.cache.has(key);

    if (!exists && this.cache.size >= this.config.maxSize) {
      this.evictLRU();
    }

    const now = Date.now();
    this.cache.set(key, {
      value,
      addedAt: now,
      lastAccessedAt: now,
    });

    // Update access order
    if (exists) {
      this.updateAccessOrder(key);
    } else {
      this.accessOrder.push(key);
    }
  }

  has(key: string): boolean {
    const entry = this.cache.get(key);
    if (!entry) return false;

    if (this.isExpired(entry)) {
      this.delete(key);
      return false;
    }

    return true;
  }

  delete(key: string): boolean {
    const existed = this.cache.delete(key);
    if (existed) {
      this.removeFromAccessOrder(key);
    }
    return existed;
  }

  clear(): void {
    this.cache.clear();
    this.accessOrder = [];
  }

  size(): number {
    return this.cache.size;
  }

  // =========================================================================
  // Batch Operations
  // =========================================================================

  getMany(keys: string[]): Map<string, Embedding> {
    const results = new Map<string, Embedding>();

    for (const key of keys) {
      const value = this.get(key);
      if (value !== undefined) {
        results.set(key, value);
      }
    }

    return results;
  }

  setMany(entries: Map<string, Embedding>): void {
    for (const [key, value] of entries) {
      this.set(key, value);
    }
  }

  // =========================================================================
  // Statistics
  // =========================================================================

  getHitRate(): number {
    const total = this.hits + this.misses;
    if (total === 0) return 0;
    return this.hits / total;
  }

  getStatistics(): CacheStatistics {
    return {
      size: this.cache.size,
      maxSize: this.config.maxSize,
      hits: this.hits,
      misses: this.misses,
      hitRate: this.getHitRate(),
      evictions: this.evictions,
    };
  }

  resetStatistics(): void {
    this.hits = 0;
    this.misses = 0;
    this.evictions = 0;
  }

  // =========================================================================
  // Serialization
  // =========================================================================

  toJSON(): string {
    return JSON.stringify({
      config: this.config,
      statistics: this.getStatistics(),
      // Don't serialize actual embeddings for size reasons
      entryCount: this.cache.size,
    });
  }

  fromJSON(json: string): void {
    const data = JSON.parse(json);

    if (data.config) {
      this.config = {
        maxSize: data.config.maxSize ?? 10000,
        ttlMs: data.config.ttlMs ?? 0,
      };
    }

    if (data.statistics) {
      this.hits = data.statistics.hits ?? 0;
      this.misses = data.statistics.misses ?? 0;
      this.evictions = data.statistics.evictions ?? 0;
    }
  }

  // =========================================================================
  // Private Methods
  // =========================================================================

  private isExpired(entry: CacheEntry): boolean {
    if (this.config.ttlMs === 0) return false;
    return Date.now() - entry.addedAt > this.config.ttlMs;
  }

  private evictLRU(): void {
    if (this.accessOrder.length === 0) return;

    // Find the least recently used entry that still exists
    while (this.accessOrder.length > 0) {
      const lruKey = this.accessOrder.shift()!;
      if (this.cache.has(lruKey)) {
        this.cache.delete(lruKey);
        this.evictions++;
        break;
      }
    }
  }

  private updateAccessOrder(key: string): void {
    this.removeFromAccessOrder(key);
    this.accessOrder.push(key);
  }

  private removeFromAccessOrder(key: string): void {
    const index = this.accessOrder.indexOf(key);
    if (index > -1) {
      this.accessOrder.splice(index, 1);
    }
  }
}

// =============================================================================
// Factory Function
// =============================================================================

/**
 * Create an EmbeddingCache instance
 * @param config - Optional configuration
 * @returns EmbeddingCache instance
 */
export function createEmbeddingCache(
  config: EmbeddingCacheConfig = {}
): EmbeddingCache {
  return new DefaultEmbeddingCache(config);
}
