/**
 * @nahisaho/yata-scale - Cache Manager
 * 
 * Multi-tier caching for knowledge graph
 */

import { ok, err, type Result } from 'neverthrow';
import { LRUCache } from 'lru-cache';
import type { Entity, Relationship, CacheConfig, CacheStats } from './types.js';
import { EntityNotFoundError } from './errors.js';

/**
 * L1 Cache - Hot tier (in-memory LRU)
 */
export class L1Cache {
  private cache: LRUCache<string, Entity | Relationship>;
  private hits = 0;
  private misses = 0;
  private evictions = 0;

  constructor(maxEntries: number, ttlMs: number) {
    this.cache = new LRUCache({
      max: maxEntries,
      ttl: ttlMs,
      dispose: () => {
        this.evictions++;
      },
    });
  }

  set(item: Entity | Relationship): void {
    this.cache.set(item.id, item);
  }

  get(id: string): Entity | Relationship | undefined {
    const item = this.cache.get(id);
    if (item) {
      this.hits++;
    } else {
      this.misses++;
    }
    return item;
  }

  delete(id: string): void {
    this.cache.delete(id);
  }

  clear(): void {
    this.cache.clear();
  }

  get size(): number {
    return this.cache.size;
  }

  getStats(): CacheStats {
    const total = this.hits + this.misses;
    return {
      tier: 'l1',
      hits: this.hits,
      misses: this.misses,
      hitRate: total > 0 ? this.hits / total : 0,
      size: this.cache.size,
      maxSize: this.cache.max,
      evictions: this.evictions,
    };
  }
}

/**
 * L2 Cache - Warm tier (compressed in-memory)
 */
export class L2Cache {
  private cache: Map<string, string> = new Map();
  private maxSize: number;
  private currentSize = 0;
  private hits = 0;
  private misses = 0;
  private evictions = 0;
  private accessOrder: string[] = [];

  constructor(maxSize: number, _ttlMs: number) {
    this.maxSize = maxSize;
  }

  async set(item: Entity | Relationship): Promise<void> {
    const serialized = JSON.stringify(item);
    const size = serialized.length;

    while (this.currentSize + size > this.maxSize && this.accessOrder.length > 0) {
      const oldest = this.accessOrder.shift()!;
      const oldData = this.cache.get(oldest);
      if (oldData) {
        this.currentSize -= oldData.length;
        this.cache.delete(oldest);
        this.evictions++;
      }
    }

    this.cache.set(item.id, serialized);
    this.currentSize += size;
    this.accessOrder.push(item.id);
  }

  async get(id: string): Promise<Entity | Relationship | undefined> {
    const data = this.cache.get(id);
    if (data) {
      this.hits++;
      const idx = this.accessOrder.indexOf(id);
      if (idx !== -1) {
        this.accessOrder.splice(idx, 1);
        this.accessOrder.push(id);
      }
      return JSON.parse(data);
    }
    this.misses++;
    return undefined;
  }

  async delete(id: string): Promise<void> {
    const data = this.cache.get(id);
    if (data) {
      this.currentSize -= data.length;
      this.cache.delete(id);
      const idx = this.accessOrder.indexOf(id);
      if (idx !== -1) this.accessOrder.splice(idx, 1);
    }
  }

  async clear(): Promise<void> {
    this.cache.clear();
    this.currentSize = 0;
    this.accessOrder = [];
  }

  get approximateSize(): number {
    return this.currentSize;
  }

  getStats(): CacheStats {
    const total = this.hits + this.misses;
    return {
      tier: 'l2',
      hits: this.hits,
      misses: this.misses,
      hitRate: total > 0 ? this.hits / total : 0,
      size: this.cache.size,
      maxSize: this.maxSize,
      evictions: this.evictions,
    };
  }
}

/**
 * L3 Cache - Cold tier (disk-based simulation)
 */
export class L3Cache {
  private storage: Map<string, string> = new Map();
  private maxEntries: number;
  private hits = 0;
  private misses = 0;
  private evictions = 0;

  constructor(config: { maxEntries: number }) {
    this.maxEntries = config.maxEntries;
  }

  async set(item: Entity | Relationship): Promise<void> {
    while (this.storage.size >= this.maxEntries) {
      const firstKey = this.storage.keys().next().value;
      if (firstKey) {
        this.storage.delete(firstKey);
        this.evictions++;
      }
    }
    this.storage.set(item.id, JSON.stringify(item));
  }

  async get(id: string): Promise<Entity | Relationship | undefined> {
    const data = this.storage.get(id);
    if (data) {
      this.hits++;
      return JSON.parse(data);
    }
    this.misses++;
    return undefined;
  }

  async delete(id: string): Promise<void> {
    this.storage.delete(id);
  }

  async has(id: string): Promise<boolean> {
    return this.storage.has(id);
  }

  async clear(): Promise<void> {
    this.storage.clear();
  }

  async close(): Promise<void> {
    // No-op for in-memory simulation
  }

  getStats(): CacheStats {
    const total = this.hits + this.misses;
    return {
      tier: 'l3',
      hits: this.hits,
      misses: this.misses,
      hitRate: total > 0 ? this.hits / total : 0,
      size: this.storage.size,
      maxSize: this.maxEntries,
      evictions: this.evictions,
    };
  }
}

/**
 * Cache invalidation manager
 */
export class InvalidationManager {
  private pending: Set<string> = new Set();
  private tracked: Set<string> = new Set();
  private listeners: Array<(ids: string[]) => void> = [];
  private batchSize: number;

  constructor(batchSize = 100) {
    this.batchSize = batchSize;
  }

  invalidate(id: string): void {
    this.pending.add(id);
    if (this.pending.size >= this.batchSize) {
      this.flush();
    }
  }

  invalidateByPattern(pattern: string): void {
    const regex = new RegExp(pattern.replace('*', '.*'));
    for (const id of this.tracked) {
      if (regex.test(id)) {
        this.pending.add(id);
      }
    }
  }

  trackEntity(id: string): void {
    this.tracked.add(id);
  }

  flush(): void {
    if (this.pending.size === 0) return;
    const ids = Array.from(this.pending);
    this.pending.clear();
    for (const listener of this.listeners) {
      listener(ids);
    }
  }

  onInvalidation(callback: (ids: string[]) => void): void {
    this.listeners.push(callback);
  }

  removeListener(callback: (ids: string[]) => void): void {
    const idx = this.listeners.indexOf(callback);
    if (idx !== -1) this.listeners.splice(idx, 1);
  }

  get pendingCount(): number {
    return this.pending.size;
  }

  clear(): void {
    this.pending.clear();
  }
}

/**
 * Multi-tier cache manager
 */
export class CacheManager {
  private l1: L1Cache;
  private l2: L2Cache;
  private l3: L3Cache;
  private invalidation: InvalidationManager;

  constructor(config: CacheConfig) {
    this.l1 = new L1Cache(config.l1MaxEntries, config.ttlMs);
    this.l2 = new L2Cache(config.l2MaxSize, config.ttlMs);
    this.l3 = new L3Cache({ maxEntries: config.l3MaxEntries });
    this.invalidation = new InvalidationManager();

    this.invalidation.onInvalidation((ids) => {
      for (const id of ids) {
        this.l1.delete(id);
        this.l2.delete(id);
        this.l3.delete(id);
      }
    });
  }

  async setEntity(entity: Entity): Promise<void> {
    this.l1.set(entity);
    await this.l2.set(entity);
    await this.l3.set(entity);
    this.invalidation.trackEntity(entity.id);
  }

  async getEntity(id: string): Promise<Result<Entity, EntityNotFoundError>> {
    // Try L1
    let entity = this.l1.get(id) as Entity | undefined;
    if (entity) return ok(entity);

    // Try L2
    entity = (await this.l2.get(id)) as Entity | undefined;
    if (entity) {
      this.l1.set(entity);
      return ok(entity);
    }

    // Try L3
    entity = (await this.l3.get(id)) as Entity | undefined;
    if (entity) {
      this.l1.set(entity);
      await this.l2.set(entity);
      return ok(entity);
    }

    return err(new EntityNotFoundError(id));
  }

  async deleteEntity(id: string): Promise<void> {
    this.l1.delete(id);
    await this.l2.delete(id);
    await this.l3.delete(id);
  }

  async setRelationship(rel: Relationship): Promise<void> {
    const key = `rel:${rel.id}`;
    this.l1.set({ ...rel, id: key } as unknown as Entity);
    await this.l2.set({ ...rel, id: key } as unknown as Entity);
  }

  async getRelationship(id: string): Promise<Result<Relationship, EntityNotFoundError>> {
    const key = `rel:${id}`;
    let rel = this.l1.get(key) as unknown as Relationship | undefined;
    if (rel) return ok({ ...rel, id });

    rel = (await this.l2.get(key)) as unknown as Relationship | undefined;
    if (rel) return ok({ ...rel, id });

    return err(new EntityNotFoundError(id));
  }

  async deleteRelationship(id: string): Promise<void> {
    const key = `rel:${id}`;
    this.l1.delete(key);
    await this.l2.delete(key);
  }

  async invalidate(ids: string[]): Promise<void> {
    for (const id of ids) {
      this.invalidation.invalidate(id);
    }
    this.invalidation.flush();
  }

  async warm(entities: Entity[]): Promise<void> {
    for (const entity of entities) {
      await this.setEntity(entity);
    }
  }

  async clear(): Promise<void> {
    this.l1.clear();
    await this.l2.clear();
    await this.l3.clear();
  }

  async close(): Promise<void> {
    await this.l3.close();
  }

  getAllStats(): { l1: CacheStats; l2: CacheStats; l3: CacheStats } {
    return {
      l1: this.l1.getStats(),
      l2: this.l2.getStats(),
      l3: this.l3.getStats(),
    };
  }
}
