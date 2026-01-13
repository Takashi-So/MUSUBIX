/**
 * Pattern Cache module tests
 *
 * @see REQ-NFR-002 - Command response performance
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import {
  LRUCache,
  PatternCache,
  globalPatternCache,
  memoize,
  memoizeAsync,
} from './pattern-cache.js';

describe('LRUCache', () => {
  let cache: LRUCache<string, number>;

  beforeEach(() => {
    cache = new LRUCache({ maxSize: 3 });
  });

  it('should store and retrieve values', () => {
    cache.set('a', 1);
    cache.set('b', 2);

    expect(cache.get('a')).toBe(1);
    expect(cache.get('b')).toBe(2);
  });

  it('should return undefined for missing keys', () => {
    expect(cache.get('missing')).toBeUndefined();
  });

  it('should evict LRU item when full', () => {
    cache.set('a', 1);
    cache.set('b', 2);
    cache.set('c', 3);
    cache.set('d', 4); // Should evict 'a'

    expect(cache.get('a')).toBeUndefined();
    expect(cache.get('b')).toBe(2);
    expect(cache.get('c')).toBe(3);
    expect(cache.get('d')).toBe(4);
  });

  it('should update LRU order on access', () => {
    cache.set('a', 1);
    cache.set('b', 2);
    cache.set('c', 3);

    cache.get('a'); // Access 'a', making it most recently used

    cache.set('d', 4); // Should evict 'b' (now LRU)

    expect(cache.get('a')).toBe(1);
    expect(cache.get('b')).toBeUndefined();
    expect(cache.get('c')).toBe(3);
    expect(cache.get('d')).toBe(4);
  });

  it('should check if key exists', () => {
    cache.set('exists', 1);

    expect(cache.has('exists')).toBe(true);
    expect(cache.has('not-exists')).toBe(false);
  });

  it('should delete keys', () => {
    cache.set('key', 1);

    expect(cache.delete('key')).toBe(true);
    expect(cache.get('key')).toBeUndefined();
    expect(cache.delete('key')).toBe(false);
  });

  it('should clear all entries', () => {
    cache.set('a', 1);
    cache.set('b', 2);

    cache.clear();

    expect(cache.size).toBe(0);
    expect(cache.get('a')).toBeUndefined();
  });

  it('should track statistics', () => {
    cache.set('a', 1);
    cache.get('a'); // Hit
    cache.get('a'); // Hit
    cache.get('missing'); // Miss

    const stats = cache.getStats();

    expect(stats.hits).toBe(2);
    expect(stats.misses).toBe(1);
    expect(stats.hitRatio).toBeCloseTo(0.667, 2);
    expect(stats.size).toBe(1);
  });

  it('should respect TTL', async () => {
    const ttlCache = new LRUCache<string, number>({ maxSize: 10, ttlMs: 50 });

    ttlCache.set('expiring', 1);

    expect(ttlCache.get('expiring')).toBe(1);

    await new Promise((resolve) => setTimeout(resolve, 60));

    expect(ttlCache.get('expiring')).toBeUndefined();
  });

  it('should update TTL on access if configured', async () => {
    const ttlCache = new LRUCache<string, number>({
      maxSize: 10,
      ttlMs: 100,
      updateTtlOnAccess: true,
    });

    ttlCache.set('key', 1);

    await new Promise((resolve) => setTimeout(resolve, 60));

    ttlCache.get('key'); // Should reset TTL

    await new Promise((resolve) => setTimeout(resolve, 60));

    expect(ttlCache.get('key')).toBe(1); // Still valid
  });

  it('should provide keys, values, entries', () => {
    cache.set('a', 1);
    cache.set('b', 2);

    expect(cache.keys()).toEqual(expect.arrayContaining(['a', 'b']));
    expect(cache.values()).toEqual(expect.arrayContaining([1, 2]));
    expect(cache.entries()).toEqual(
      expect.arrayContaining([
        ['a', 1],
        ['b', 2],
      ])
    );
  });

  it('should iterate with forEach', () => {
    cache.set('a', 1);
    cache.set('b', 2);

    const collected: Array<[string, number]> = [];
    cache.forEach((value, key) => {
      collected.push([key, value]);
    });

    expect(collected).toHaveLength(2);
  });

  it('should prune expired entries', async () => {
    const ttlCache = new LRUCache<string, number>({ maxSize: 10, ttlMs: 50 });

    ttlCache.set('a', 1);
    ttlCache.set('b', 2);

    await new Promise((resolve) => setTimeout(resolve, 60));

    ttlCache.set('c', 3); // Add fresh entry

    const pruned = ttlCache.prune();

    expect(pruned).toBe(2);
    expect(ttlCache.size).toBe(1);
    expect(ttlCache.get('c')).toBe(3);
  });

  it('should track evictions', () => {
    cache.set('a', 1);
    cache.set('b', 2);
    cache.set('c', 3);
    cache.set('d', 4); // Evict 'a'
    cache.set('e', 5); // Evict 'b'

    const stats = cache.getStats();

    expect(stats.evictions).toBe(2);
  });

  it('should support memory-based eviction', () => {
    const memCache = new LRUCache<string, string>({
      maxSize: 100,
      maxMemorySize: 50,
      sizeCalculator: (value) => value.length,
    });

    memCache.set('large', 'x'.repeat(40));
    memCache.set('another', 'x'.repeat(30)); // Should evict 'large'

    expect(memCache.get('large')).toBeUndefined();
    expect(memCache.get('another')).toBeDefined();
  });
});

describe('PatternCache', () => {
  let patternCache: PatternCache;

  beforeEach(() => {
    patternCache = new PatternCache({ maxSize: 10 });
  });

  it('should store patterns by category', () => {
    patternCache.set('design', 'singleton', { name: 'Singleton' });
    patternCache.set('code', 'factory', { name: 'Factory' });

    expect(patternCache.get('design', 'singleton')).toEqual({ name: 'Singleton' });
    expect(patternCache.get('code', 'factory')).toEqual({ name: 'Factory' });
  });

  it('should check existence by category', () => {
    patternCache.set('cat', 'key', 'value');

    expect(patternCache.has('cat', 'key')).toBe(true);
    expect(patternCache.has('cat', 'other')).toBe(false);
    expect(patternCache.has('other-cat', 'key')).toBe(false);
  });

  it('should delete by category', () => {
    patternCache.set('cat', 'key', 'value');

    expect(patternCache.delete('cat', 'key')).toBe(true);
    expect(patternCache.has('cat', 'key')).toBe(false);
  });

  it('should clear specific category', () => {
    patternCache.set('cat1', 'a', 1);
    patternCache.set('cat1', 'b', 2);
    patternCache.set('cat2', 'c', 3);

    patternCache.clearCategory('cat1');

    expect(patternCache.has('cat1', 'a')).toBe(false);
    expect(patternCache.has('cat1', 'b')).toBe(false);
    expect(patternCache.has('cat2', 'c')).toBe(true);
  });

  it('should clear all categories', () => {
    patternCache.set('cat1', 'a', 1);
    patternCache.set('cat2', 'b', 2);

    patternCache.clearAll();

    expect(patternCache.has('cat1', 'a')).toBe(false);
    expect(patternCache.has('cat2', 'b')).toBe(false);
  });

  it('should provide stats by category', () => {
    patternCache.set('cat1', 'a', 1);
    patternCache.set('cat1', 'b', 2);
    patternCache.set('cat2', 'c', 3);

    patternCache.get('cat1', 'a'); // Hit
    patternCache.get('cat1', 'missing'); // Miss

    const stats = patternCache.getStats();

    expect(stats).toHaveProperty('cat1');
    expect(stats).toHaveProperty('cat2');
    expect(stats['cat1'].size).toBe(2);
    expect(stats['cat2'].size).toBe(1);
  });

  it('should list categories', () => {
    patternCache.set('design', 'key', 1);
    patternCache.set('code', 'key', 2);

    const categories = patternCache.getCategories();

    expect(categories).toContain('design');
    expect(categories).toContain('code');
  });

  it('should prune all categories', async () => {
    const ttlCache = new PatternCache({ maxSize: 10, ttlMs: 50 });

    ttlCache.set('cat1', 'a', 1);
    ttlCache.set('cat2', 'b', 2);

    await new Promise((resolve) => setTimeout(resolve, 60));

    const pruned = ttlCache.pruneAll();

    expect(pruned).toBe(2);
  });
});

describe('globalPatternCache', () => {
  beforeEach(() => {
    globalPatternCache.clearAll();
  });

  it('should be a singleton PatternCache', () => {
    expect(globalPatternCache).toBeInstanceOf(PatternCache);
  });

  it('should persist across module accesses', () => {
    globalPatternCache.set('test', 'key', 'value');

    expect(globalPatternCache.get('test', 'key')).toBe('value');
  });
});

describe('memoize', () => {
  it('should cache function results', () => {
    const expensive = vi.fn((x: number) => x * 2);
    const memoized = memoize(expensive);

    expect(memoized(5)).toBe(10);
    expect(memoized(5)).toBe(10);
    expect(memoized(5)).toBe(10);

    expect(expensive).toHaveBeenCalledTimes(1);
  });

  it('should cache by arguments', () => {
    const fn = vi.fn((a: number, b: number) => a + b);
    const memoized = memoize(fn);

    expect(memoized(1, 2)).toBe(3);
    expect(memoized(2, 3)).toBe(5);
    expect(memoized(1, 2)).toBe(3);

    expect(fn).toHaveBeenCalledTimes(2);
  });

  it('should use custom key function', () => {
    const fn = vi.fn((obj: { id: number }) => obj.id * 2);
    const memoized = memoize(fn, {
      keyFn: (obj) => String(obj.id),
    });

    expect(memoized({ id: 1 })).toBe(2);
    expect(memoized({ id: 1 })).toBe(2); // Same id, cached

    expect(fn).toHaveBeenCalledTimes(1);
  });
});

describe('memoizeAsync', () => {
  it('should cache async function results', async () => {
    const expensive = vi.fn(async (x: number) => {
      await new Promise((resolve) => setTimeout(resolve, 10));
      return x * 2;
    });
    const memoized = memoizeAsync(expensive);

    expect(await memoized(5)).toBe(10);
    expect(await memoized(5)).toBe(10);

    expect(expensive).toHaveBeenCalledTimes(1);
  });

  it('should handle concurrent calls', async () => {
    const expensive = vi.fn(async (x: number) => {
      await new Promise((resolve) => setTimeout(resolve, 50));
      return x * 2;
    });
    const memoized = memoizeAsync(expensive);

    const [r1, r2, r3] = await Promise.all([
      memoized(5),
      memoized(5),
      memoized(5),
    ]);

    expect(r1).toBe(10);
    expect(r2).toBe(10);
    expect(r3).toBe(10);
    expect(expensive).toHaveBeenCalledTimes(1);
  });
});
