/**
 * @fileoverview Caching infrastructure
 * @module @nahisaho/musubix-security/infrastructure/cache
 * @trace REQ-SEC-CACHE-001
 */

import { writeFile, readFile, mkdir, unlink, readdir, stat } from 'node:fs/promises';
import { join, dirname } from 'node:path';
import { createHash } from 'node:crypto';
import type { CacheStrategy } from '../types/index.js';

/**
 * Cache entry
 */
interface CacheEntry<T> {
  key: string;
  value: T;
  createdAt: number;
  expiresAt: number;
  size: number;
}

/**
 * Cache statistics
 */
export interface CacheStats {
  hits: number;
  misses: number;
  size: number;
  entryCount: number;
  hitRate: number;
}

/**
 * Cache options
 */
export interface CacheOptions {
  /** Cache strategy */
  strategy: CacheStrategy;
  /** Cache directory for file strategy */
  cacheDir?: string;
  /** TTL in seconds */
  ttlSeconds?: number;
  /** Maximum cache size in bytes */
  maxSizeBytes?: number;
}

/**
 * Abstract cache interface
 */
export interface ICache<T = unknown> {
  get(key: string): Promise<T | undefined>;
  set(key: string, value: T, ttlSeconds?: number): Promise<void>;
  has(key: string): Promise<boolean>;
  delete(key: string): Promise<boolean>;
  clear(): Promise<void>;
  getStats(): CacheStats | Promise<CacheStats>;
}

/**
 * Memory cache implementation
 */
export class MemoryCache<T = unknown> implements ICache<T> {
  private cache: Map<string, CacheEntry<T>> = new Map();
  private stats = { hits: 0, misses: 0 };
  private maxSizeBytes: number;
  private defaultTtlSeconds: number;
  private currentSize = 0;

  constructor(options: CacheOptions = { strategy: 'memory' }) {
    this.maxSizeBytes = options.maxSizeBytes ?? 100 * 1024 * 1024; // 100MB
    this.defaultTtlSeconds = options.ttlSeconds ?? 3600; // 1 hour
  }

  async get(key: string): Promise<T | undefined> {
    const entry = this.cache.get(key);
    
    if (!entry) {
      this.stats.misses++;
      return undefined;
    }

    // Check expiration
    if (Date.now() > entry.expiresAt) {
      this.cache.delete(key);
      this.currentSize -= entry.size;
      this.stats.misses++;
      return undefined;
    }

    this.stats.hits++;
    return entry.value;
  }

  async set(key: string, value: T, ttlSeconds?: number): Promise<void> {
    const serialized = JSON.stringify(value);
    const size = Buffer.byteLength(serialized);
    const ttl = ttlSeconds ?? this.defaultTtlSeconds;

    // Remove existing entry if present
    const existing = this.cache.get(key);
    if (existing) {
      this.currentSize -= existing.size;
    }

    // Evict entries if needed
    while (this.currentSize + size > this.maxSizeBytes && this.cache.size > 0) {
      this.evictOldest();
    }

    const entry: CacheEntry<T> = {
      key,
      value,
      createdAt: Date.now(),
      expiresAt: Date.now() + ttl * 1000,
      size,
    };

    this.cache.set(key, entry);
    this.currentSize += size;
  }

  async has(key: string): Promise<boolean> {
    const entry = this.cache.get(key);
    if (!entry) return false;
    if (Date.now() > entry.expiresAt) {
      this.cache.delete(key);
      this.currentSize -= entry.size;
      return false;
    }
    return true;
  }

  async delete(key: string): Promise<boolean> {
    const entry = this.cache.get(key);
    if (entry) {
      this.currentSize -= entry.size;
      this.cache.delete(key);
      return true;
    }
    return false;
  }

  async clear(): Promise<void> {
    this.cache.clear();
    this.currentSize = 0;
    this.stats = { hits: 0, misses: 0 };
  }

  getStats(): CacheStats {
    const total = this.stats.hits + this.stats.misses;
    return {
      hits: this.stats.hits,
      misses: this.stats.misses,
      size: this.currentSize,
      entryCount: this.cache.size,
      hitRate: total > 0 ? this.stats.hits / total : 0,
    };
  }

  private evictOldest(): void {
    let oldest: string | undefined;
    let oldestTime = Infinity;

    for (const [key, entry] of this.cache) {
      if (entry.createdAt < oldestTime) {
        oldestTime = entry.createdAt;
        oldest = key;
      }
    }

    if (oldest) {
      const entry = this.cache.get(oldest)!;
      this.currentSize -= entry.size;
      this.cache.delete(oldest);
    }
  }
}

/**
 * File-based cache implementation
 */
export class FileCache<T = unknown> implements ICache<T> {
  private stats = { hits: 0, misses: 0 };
  private cacheDir: string;
  private defaultTtlSeconds: number;
  private initialized = false;

  constructor(options: CacheOptions) {
    if (!options.cacheDir) {
      throw new Error('cacheDir is required for file cache');
    }
    this.cacheDir = options.cacheDir;
    this.defaultTtlSeconds = options.ttlSeconds ?? 3600;
    // maxSizeBytes is stored for future use when implementing cache eviction
  }

  private async ensureDir(): Promise<void> {
    if (this.initialized) return;
    await mkdir(this.cacheDir, { recursive: true });
    this.initialized = true;
  }

  private getCachePath(key: string): string {
    const hash = createHash('sha256').update(key).digest('hex');
    return join(this.cacheDir, `${hash}.json`);
  }

  async get(key: string): Promise<T | undefined> {
    await this.ensureDir();
    const path = this.getCachePath(key);

    try {
      const content = await readFile(path, 'utf-8');
      const entry: CacheEntry<T> = JSON.parse(content);

      if (Date.now() > entry.expiresAt) {
        await unlink(path).catch(() => {});
        this.stats.misses++;
        return undefined;
      }

      this.stats.hits++;
      return entry.value;
    } catch {
      this.stats.misses++;
      return undefined;
    }
  }

  async set(key: string, value: T, ttlSeconds?: number): Promise<void> {
    await this.ensureDir();
    const path = this.getCachePath(key);
    const ttl = ttlSeconds ?? this.defaultTtlSeconds;

    const entry: CacheEntry<T> = {
      key,
      value,
      createdAt: Date.now(),
      expiresAt: Date.now() + ttl * 1000,
      size: 0,
    };

    const content = JSON.stringify(entry, null, 2);
    entry.size = Buffer.byteLength(content);

    await mkdir(dirname(path), { recursive: true });
    await writeFile(path, content, 'utf-8');
  }

  async has(key: string): Promise<boolean> {
    const value = await this.get(key);
    return value !== undefined;
  }

  async delete(key: string): Promise<boolean> {
    const path = this.getCachePath(key);
    try {
      await unlink(path);
      return true;
    } catch {
      return false;
    }
  }

  async clear(): Promise<void> {
    await this.ensureDir();
    try {
      const files = await readdir(this.cacheDir);
      await Promise.all(
        files
          .filter((f) => f.endsWith('.json'))
          .map((f) => unlink(join(this.cacheDir, f)).catch(() => {}))
      );
    } catch {
      // Directory might not exist
    }
    this.stats = { hits: 0, misses: 0 };
  }

  async getStats(): Promise<CacheStats> {
    await this.ensureDir();
    let totalSize = 0;
    let entryCount = 0;

    try {
      const files = await readdir(this.cacheDir);
      for (const file of files) {
        if (file.endsWith('.json')) {
          const stats = await stat(join(this.cacheDir, file)).catch(() => null);
          if (stats) {
            totalSize += stats.size;
            entryCount++;
          }
        }
      }
    } catch {
      // Directory might not exist
    }

    const total = this.stats.hits + this.stats.misses;
    return {
      hits: this.stats.hits,
      misses: this.stats.misses,
      size: totalSize,
      entryCount,
      hitRate: total > 0 ? this.stats.hits / total : 0,
    };
  }
}

/**
 * No-op cache implementation
 */
export class NoopCache<T = unknown> implements ICache<T> {
  async get(_key: string): Promise<T | undefined> {
    return undefined;
  }

  async set(_key: string, _value: T): Promise<void> {
    // No-op
  }

  async has(_key: string): Promise<boolean> {
    return false;
  }

  async delete(_key: string): Promise<boolean> {
    return false;
  }

  async clear(): Promise<void> {
    // No-op
  }

  getStats(): CacheStats {
    return {
      hits: 0,
      misses: 0,
      size: 0,
      entryCount: 0,
      hitRate: 0,
    };
  }
}

/**
 * Create a cache instance based on options
 */
export function createCache<T = unknown>(options: CacheOptions): ICache<T> {
  switch (options.strategy) {
    case 'memory':
      return new MemoryCache<T>(options);
    case 'file':
      return new FileCache<T>(options);
    case 'none':
      return new NoopCache<T>();
    default:
      return new MemoryCache<T>(options);
  }
}

/**
 * Generate a cache key from multiple parts
 */
export function cacheKey(...parts: (string | number | boolean | undefined | null)[]): string {
  return parts
    .filter((p) => p !== undefined && p !== null)
    .map((p) => String(p))
    .join(':');
}

/**
 * Generate a hash for a file's content
 */
export function contentHash(content: string): string {
  return createHash('sha256').update(content).digest('hex').slice(0, 16);
}
