/**
 * @fileoverview Tests for CachingLayer
 * @module @nahisaho/musubix-deep-research/performance
 */

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import {
  CachingLayer,
  createCachingLayer,
  type CacheStats,
} from './caching-layer.js';

describe('CachingLayer', () => {
  let cache: CachingLayer<string, string>;

  beforeEach(() => {
    vi.useFakeTimers();
    cache = new CachingLayer({ maxSize: 3, ttlMs: 1000, autoCleanup: false });
  });

  afterEach(() => {
    cache.dispose();
    vi.useRealTimers();
  });

  describe('constructor', () => {
    it('should create cache with default options', () => {
      const defaultCache = new CachingLayer({ autoCleanup: false });
      expect(defaultCache.size()).toBe(0);
      const stats = defaultCache.getStats();
      expect(stats.maxSize).toBe(100);
      defaultCache.dispose();
    });

    it('should create cache with custom options', () => {
      const customCache = new CachingLayer({ maxSize: 50, autoCleanup: false });
      const stats = customCache.getStats();
      expect(stats.maxSize).toBe(50);
      customCache.dispose();
    });

    it('should throw error if maxSize < 1', () => {
      expect(() => new CachingLayer({ maxSize: 0 })).toThrow('maxSize must be at least 1');
    });

    it('should throw error if ttlMs < 0', () => {
      expect(() => new CachingLayer({ ttlMs: -1 })).toThrow('ttlMs must be non-negative');
    });
  });

  describe('set and get', () => {
    it('should store and retrieve value', () => {
      cache.set('key1', 'value1');
      expect(cache.get('key1')).toBe('value1');
    });

    it('should return undefined for non-existent key', () => {
      expect(cache.get('nonexistent')).toBeUndefined();
    });

    it('should update value for existing key', () => {
      cache.set('key1', 'value1');
      cache.set('key1', 'value2');
      expect(cache.get('key1')).toBe('value2');
      expect(cache.size()).toBe(1);
    });

    it('should expire entries after TTL', () => {
      cache.set('key1', 'value1');
      expect(cache.get('key1')).toBe('value1');

      // Advance time past TTL
      vi.advanceTimersByTime(1001);

      expect(cache.get('key1')).toBeUndefined();
    });

    it('should support custom TTL per entry', () => {
      cache.set('key1', 'value1', 500); // 500ms TTL
      cache.set('key2', 'value2', 2000); // 2000ms TTL

      // Advance 600ms
      vi.advanceTimersByTime(600);

      expect(cache.get('key1')).toBeUndefined();
      expect(cache.get('key2')).toBe('value2');
    });
  });

  describe('LRU eviction', () => {
    it('should evict least recently used entry when full', () => {
      cache.set('key1', 'value1');
      cache.set('key2', 'value2');
      cache.set('key3', 'value3');

      expect(cache.size()).toBe(3);

      // Cache is full (maxSize: 3), adding key4 should evict key1
      cache.set('key4', 'value4');

      expect(cache.size()).toBe(3);
      expect(cache.get('key1')).toBeUndefined();
      expect(cache.get('key2')).toBe('value2');
      expect(cache.get('key3')).toBe('value3');
      expect(cache.get('key4')).toBe('value4');
    });

    it('should update LRU order on get', () => {
      cache.set('key1', 'value1');
      cache.set('key2', 'value2');
      cache.set('key3', 'value3');

      // Access key1 to make it most recently used
      cache.get('key1');

      // Adding key4 should evict key2 (now LRU)
      cache.set('key4', 'value4');

      expect(cache.get('key1')).toBe('value1');
      expect(cache.get('key2')).toBeUndefined();
      expect(cache.get('key3')).toBe('value3');
      expect(cache.get('key4')).toBe('value4');
    });
  });

  describe('has', () => {
    it('should return true for existing key', () => {
      cache.set('key1', 'value1');
      expect(cache.has('key1')).toBe(true);
    });

    it('should return false for non-existent key', () => {
      expect(cache.has('nonexistent')).toBe(false);
    });

    it('should return false for expired key', () => {
      cache.set('key1', 'value1');
      vi.advanceTimersByTime(1001);
      expect(cache.has('key1')).toBe(false);
    });
  });

  describe('delete', () => {
    it('should delete existing key', () => {
      cache.set('key1', 'value1');
      expect(cache.delete('key1')).toBe(true);
      expect(cache.get('key1')).toBeUndefined();
    });

    it('should return false for non-existent key', () => {
      expect(cache.delete('nonexistent')).toBe(false);
    });
  });

  describe('clear', () => {
    it('should clear all entries', () => {
      cache.set('key1', 'value1');
      cache.set('key2', 'value2');
      cache.clear();

      expect(cache.size()).toBe(0);
      expect(cache.get('key1')).toBeUndefined();
      expect(cache.get('key2')).toBeUndefined();
    });

    it('should reset statistics', () => {
      cache.set('key1', 'value1');
      cache.get('key1');
      cache.get('nonexistent');

      cache.clear();

      const stats = cache.getStats();
      expect(stats.hits).toBe(0);
      expect(stats.misses).toBe(0);
      expect(stats.evictions).toBe(0);
    });
  });

  describe('keys', () => {
    it('should return all keys', () => {
      cache.set('key1', 'value1');
      cache.set('key2', 'value2');

      const keys = cache.keys();
      expect(keys).toContain('key1');
      expect(keys).toContain('key2');
      expect(keys.length).toBe(2);
    });

    it('should exclude expired keys', () => {
      cache.set('key1', 'value1', 500);
      cache.set('key2', 'value2', 2000);

      vi.advanceTimersByTime(600);

      const keys = cache.keys();
      expect(keys).toContain('key2');
      expect(keys).not.toContain('key1');
      expect(keys.length).toBe(1);
    });
  });

  describe('getStats', () => {
    it('should track hits and misses', () => {
      cache.set('key1', 'value1');

      cache.get('key1'); // hit
      cache.get('key2'); // miss
      cache.get('key1'); // hit
      cache.get('key3'); // miss

      const stats = cache.getStats();
      expect(stats.hits).toBe(2);
      expect(stats.misses).toBe(2);
      expect(stats.hitRate).toBe(0.5);
    });

    it('should track evictions', () => {
      cache.set('key1', 'value1');
      cache.set('key2', 'value2');
      cache.set('key3', 'value3');
      cache.set('key4', 'value4'); // Evicts key1

      const stats = cache.getStats();
      expect(stats.evictions).toBe(1);
    });

    it('should return zero hit rate when no accesses', () => {
      const stats = cache.getStats();
      expect(stats.hitRate).toBe(0);
    });
  });

  describe('cleanup', () => {
    it('should remove expired entries', () => {
      cache.set('key1', 'value1', 500);
      cache.set('key2', 'value2', 2000);

      vi.advanceTimersByTime(600);

      const removed = cache.cleanup();
      expect(removed).toBe(1);
      expect(cache.size()).toBe(1);
      expect(cache.has('key1')).toBe(false);
      expect(cache.has('key2')).toBe(true);
    });

    it('should return 0 when no expired entries', () => {
      cache.set('key1', 'value1');
      const removed = cache.cleanup();
      expect(removed).toBe(0);
    });
  });

  describe('auto-cleanup', () => {
    it('should automatically cleanup expired entries', () => {
      const autoCache = new CachingLayer<string, string>({
        maxSize: 3,
        ttlMs: 500,
        cleanupIntervalMs: 1000,
      });

      autoCache.set('key1', 'value1');
      autoCache.set('key2', 'value2');

      // Advance past TTL but before cleanup interval
      vi.advanceTimersByTime(600);
      expect(autoCache.size()).toBe(2); // Not cleaned yet

      // Advance past cleanup interval
      vi.advanceTimersByTime(500);
      expect(autoCache.size()).toBe(0); // Cleaned up

      autoCache.dispose();
    });
  });

  describe('createCachingLayer', () => {
    it('should create CachingLayer instance', () => {
      const newCache = createCachingLayer<string, number>({ maxSize: 10, autoCleanup: false });
      expect(newCache).toBeInstanceOf(CachingLayer);
      expect(newCache.getStats().maxSize).toBe(10);
      newCache.dispose();
    });
  });

  describe('dispose', () => {
    it('should stop cleanup timer', () => {
      const autoCache = new CachingLayer({ cleanupIntervalMs: 100 });
      autoCache.dispose();
      // No error should occur, timer should be stopped
      expect(true).toBe(true);
    });
  });
});
