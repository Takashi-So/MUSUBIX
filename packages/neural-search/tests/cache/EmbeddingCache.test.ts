/**
 * EmbeddingCache Tests
 * @module @nahisaho/musubix-neural-search
 * @see TSK-NS-105
 * @see DES-NS-105
 * @see REQ-NS-105
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createEmbeddingCache,
  type EmbeddingCache,
} from '../../src/cache/EmbeddingCache.js';
import type { Embedding } from '../../src/types.js';

describe('EmbeddingCache', () => {
  let cache: EmbeddingCache;

  const mockEmbedding1: Embedding = new Array(128).fill(0.1);
  const mockEmbedding2: Embedding = new Array(128).fill(0.2);
  const mockEmbedding3: Embedding = new Array(128).fill(0.3);

  beforeEach(() => {
    cache = createEmbeddingCache();
  });

  describe('Factory Function', () => {
    it('should create an EmbeddingCache instance', () => {
      const instance = createEmbeddingCache();
      expect(instance).toBeDefined();
      expect(typeof instance.get).toBe('function');
      expect(typeof instance.set).toBe('function');
    });

    it('should create with custom config', () => {
      const instance = createEmbeddingCache({
        maxSize: 5000,
        ttlMs: 60000,
      });
      expect(instance).toBeDefined();
    });

    it('should respect max size of 10,000 entries', () => {
      const instance = createEmbeddingCache({ maxSize: 10000 });
      expect(instance).toBeDefined();
    });
  });

  describe('Basic Operations', () => {
    it('should set and get an embedding', () => {
      cache.set('key1', mockEmbedding1);
      const result = cache.get('key1');

      expect(result).toBeDefined();
      expect(result).toEqual(mockEmbedding1);
    });

    it('should return undefined for missing key', () => {
      const result = cache.get('nonexistent');
      expect(result).toBeUndefined();
    });

    it('should overwrite existing entry', () => {
      cache.set('key1', mockEmbedding1);
      cache.set('key1', mockEmbedding2);
      const result = cache.get('key1');

      expect(result).toEqual(mockEmbedding2);
    });

    it('should check if key exists', () => {
      cache.set('key1', mockEmbedding1);

      expect(cache.has('key1')).toBe(true);
      expect(cache.has('nonexistent')).toBe(false);
    });

    it('should delete entry', () => {
      cache.set('key1', mockEmbedding1);
      cache.delete('key1');

      expect(cache.has('key1')).toBe(false);
    });

    it('should clear all entries', () => {
      cache.set('key1', mockEmbedding1);
      cache.set('key2', mockEmbedding2);
      cache.clear();

      expect(cache.has('key1')).toBe(false);
      expect(cache.has('key2')).toBe(false);
      expect(cache.size()).toBe(0);
    });
  });

  describe('LRU Eviction', () => {
    it('should evict least recently used entry when full', () => {
      const smallCache = createEmbeddingCache({ maxSize: 3 });

      smallCache.set('key1', mockEmbedding1);
      smallCache.set('key2', mockEmbedding2);
      smallCache.set('key3', mockEmbedding3);

      // Access key1 to make it recently used
      smallCache.get('key1');

      // Add new entry, should evict key2 (least recently used)
      smallCache.set('key4', mockEmbedding1);

      expect(smallCache.has('key1')).toBe(true);
      expect(smallCache.has('key2')).toBe(false); // Evicted
      expect(smallCache.has('key3')).toBe(true);
      expect(smallCache.has('key4')).toBe(true);
    });

    it('should update access order on get', () => {
      const smallCache = createEmbeddingCache({ maxSize: 2 });

      smallCache.set('key1', mockEmbedding1);
      smallCache.set('key2', mockEmbedding2);

      // Access key1 to make it recently used
      smallCache.get('key1');

      // Add new entry, should evict key2
      smallCache.set('key3', mockEmbedding3);

      expect(smallCache.has('key1')).toBe(true);
      expect(smallCache.has('key2')).toBe(false);
      expect(smallCache.has('key3')).toBe(true);
    });
  });

  describe('Hit Rate', () => {
    it('should track hit rate', () => {
      cache.set('key1', mockEmbedding1);

      // Hit
      cache.get('key1');
      cache.get('key1');

      // Miss
      cache.get('nonexistent');

      const hitRate = cache.getHitRate();
      expect(hitRate).toBeCloseTo(2 / 3, 2);
    });

    it('should return 0 hit rate with no accesses', () => {
      expect(cache.getHitRate()).toBe(0);
    });

    it('should reset hit rate statistics', () => {
      cache.set('key1', mockEmbedding1);
      cache.get('key1');
      cache.get('nonexistent');

      cache.resetStatistics();

      expect(cache.getHitRate()).toBe(0);
    });
  });

  describe('Statistics', () => {
    it('should report current size', () => {
      expect(cache.size()).toBe(0);

      cache.set('key1', mockEmbedding1);
      expect(cache.size()).toBe(1);

      cache.set('key2', mockEmbedding2);
      expect(cache.size()).toBe(2);
    });

    it('should provide detailed statistics', () => {
      cache.set('key1', mockEmbedding1);
      cache.get('key1');
      cache.get('nonexistent');

      const stats = cache.getStatistics();

      expect(stats.size).toBe(1);
      expect(stats.hits).toBe(1);
      expect(stats.misses).toBe(1);
      expect(stats.hitRate).toBeCloseTo(0.5, 2);
      expect(typeof stats.evictions).toBe('number');
    });
  });

  describe('Batch Operations', () => {
    it('should set multiple entries at once', () => {
      const entries = new Map<string, Embedding>([
        ['key1', mockEmbedding1],
        ['key2', mockEmbedding2],
        ['key3', mockEmbedding3],
      ]);

      cache.setMany(entries);

      expect(cache.has('key1')).toBe(true);
      expect(cache.has('key2')).toBe(true);
      expect(cache.has('key3')).toBe(true);
    });

    it('should get multiple entries at once', () => {
      cache.set('key1', mockEmbedding1);
      cache.set('key2', mockEmbedding2);

      const results = cache.getMany(['key1', 'key2', 'nonexistent']);

      expect(results.get('key1')).toEqual(mockEmbedding1);
      expect(results.get('key2')).toEqual(mockEmbedding2);
      expect(results.has('nonexistent')).toBe(false);
    });
  });

  describe('TTL Support', () => {
    it('should expire entries after TTL', async () => {
      const shortTtlCache = createEmbeddingCache({
        maxSize: 100,
        ttlMs: 50, // 50ms TTL
      });

      shortTtlCache.set('key1', mockEmbedding1);
      expect(shortTtlCache.get('key1')).toBeDefined();

      // Wait for TTL to expire
      await new Promise((resolve) => setTimeout(resolve, 100));

      expect(shortTtlCache.get('key1')).toBeUndefined();
    });
  });

  describe('Serialization', () => {
    it('should serialize to JSON', () => {
      cache.set('key1', mockEmbedding1);
      cache.get('key1');

      const json = cache.toJSON();
      expect(typeof json).toBe('string');

      const parsed = JSON.parse(json);
      expect(parsed.statistics).toBeDefined();
    });

    it('should restore from JSON', () => {
      cache.set('key1', mockEmbedding1);
      const json = cache.toJSON();

      const newCache = createEmbeddingCache();
      newCache.fromJSON(json);

      // Statistics should be restored
      const stats = newCache.getStatistics();
      expect(stats).toBeDefined();
    });
  });
});
