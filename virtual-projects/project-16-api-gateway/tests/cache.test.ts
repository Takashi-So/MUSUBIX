// Tests for Cache
// REQ-CACHE-001, REQ-CACHE-002, REQ-CACHE-003

import { describe, it, expect } from 'vitest';
import {
  createCacheEntry,
  isCacheExpired,
  generateCacheKey,
  createCacheStore,
  getCache,
  setCache,
  invalidateCache,
  invalidateCachePattern,
} from '../src/domain/cache.js';

describe('Cache', () => {
  describe('createCacheEntry', () => {
    it('should create cache entry', () => {
      const now = new Date();
      const entry = createCacheEntry('test-key', { data: 'test' }, 60, 'application/json', now);

      expect(entry.key).toBe('test-key');
      expect(entry.value).toEqual({ data: 'test' });
      expect(entry.contentType).toBe('application/json');
      expect(entry.createdAt).toEqual(now);
      expect(entry.expiresAt.getTime()).toBe(now.getTime() + 60000);
      expect(entry.etag).toBeDefined();
    });

    it('should throw for empty key', () => {
      expect(() => createCacheEntry('', { data: 'test' }, 60)).toThrow('key is required');
    });

    it('should throw for non-positive TTL', () => {
      expect(() => createCacheEntry('test', { data: 'test' }, 0)).toThrow('TTL must be positive');
      expect(() => createCacheEntry('test', { data: 'test' }, -1)).toThrow('TTL must be positive');
    });
  });

  describe('isCacheExpired', () => {
    it('should return false for valid entry', () => {
      const now = new Date();
      const entry = createCacheEntry('test', 'data', 60, 'text/plain', now);

      expect(isCacheExpired(entry, now)).toBe(false);
    });

    it('should return true for expired entry', () => {
      const past = new Date(Date.now() - 120000); // 2 minutes ago
      const entry = createCacheEntry('test', 'data', 60, 'text/plain', past);

      expect(isCacheExpired(entry)).toBe(true);
    });
  });

  describe('generateCacheKey', () => {
    it('should generate key for path only', () => {
      const key = generateCacheKey('GET', '/api/users');
      expect(key).toBe('GET:/api/users');
    });

    it('should include sorted query params', () => {
      const key = generateCacheKey('GET', '/api/users', { page: '1', limit: '10' });
      expect(key).toBe('GET:/api/users?limit=10&page=1');
    });

    it('should handle empty query params', () => {
      const key = generateCacheKey('GET', '/api/users', {});
      expect(key).toBe('GET:/api/users');
    });
  });

  describe('CacheStore', () => {
    it('should get and set cache entries', () => {
      const store = createCacheStore();
      const entry = createCacheEntry('test-key', 'test-value', 60);

      setCache(store, entry);
      const retrieved = getCache(store, 'test-key');

      expect(retrieved).toEqual(entry);
    });

    it('should return null for missing key', () => {
      const store = createCacheStore();
      const retrieved = getCache(store, 'missing');

      expect(retrieved).toBeNull();
    });

    it('should return null and remove expired entry', () => {
      const store = createCacheStore();
      const past = new Date(Date.now() - 120000);
      const entry = createCacheEntry('test-key', 'test-value', 60, 'text/plain', past);

      store.entries.set('test-key', entry);
      const retrieved = getCache(store, 'test-key');

      expect(retrieved).toBeNull();
      expect(store.entries.has('test-key')).toBe(false);
    });

    it('should invalidate by exact key', () => {
      const store = createCacheStore();
      const entry = createCacheEntry('test-key', 'test-value', 60);
      setCache(store, entry);

      const result = invalidateCache(store, 'test-key');

      expect(result).toBe(true);
      expect(getCache(store, 'test-key')).toBeNull();
    });

    it('should return false for missing key invalidation', () => {
      const store = createCacheStore();
      const result = invalidateCache(store, 'missing');

      expect(result).toBe(false);
    });

    it('should invalidate by pattern', () => {
      const store = createCacheStore();
      setCache(store, createCacheEntry('GET:/api/users/1', 'user1', 60));
      setCache(store, createCacheEntry('GET:/api/users/2', 'user2', 60));
      setCache(store, createCacheEntry('GET:/api/products/1', 'product1', 60));

      const count = invalidateCachePattern(store, 'GET:/api/users/*');

      expect(count).toBe(2);
      expect(store.entries.size).toBe(1);
      expect(getCache(store, 'GET:/api/products/1')).not.toBeNull();
    });
  });
});
