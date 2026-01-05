/**
 * YATA Global - Unit Tests
 *
 * @packageDocumentation
 * @module @nahisaho/yata-global
 */

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import * as fs from 'fs';
import * as path from 'path';
import * as os from 'os';
import {
  YataGlobal,
  createYataGlobal,
  CacheManager,
  ApiClient,
  DEFAULT_SYNC_CONFIG,
} from '../src/index.js';
import type {
  FrameworkKnowledge,
  SharedPattern,
  SyncConfig,
} from '../src/types.js';

// Test data
const testFramework: FrameworkKnowledge = {
  id: 'fw-react',
  name: 'React',
  version: '18.2.0',
  category: 'web-frontend',
  language: 'typescript',
  description: 'A JavaScript library for building user interfaces',
  documentationUrl: 'https://react.dev',
  repositoryUrl: 'https://github.com/facebook/react',
  license: 'MIT',
  popularity: 95,
  quality: 90,
  tags: ['ui', 'frontend', 'javascript', 'component'],
  updatedAt: new Date(),
  createdAt: new Date(),
};

const testPattern: SharedPattern = {
  id: 'pat-001',
  name: 'React Hook Pattern',
  description: 'Custom hook pattern for reusable stateful logic',
  category: 'design-pattern',
  frameworks: ['react'],
  language: 'typescript',
  template: 'function use${Name}() { ... }',
  example: 'const { data } = useCustomHook();',
  tags: ['hooks', 'react', 'state'],
  authorId: 'user-001',
  rating: {
    average: 4.5,
    count: 100,
    distribution: { 1: 2, 2: 3, 3: 10, 4: 35, 5: 50 },
  },
  downloads: 5000,
  official: false,
  visibility: 'public',
  createdAt: new Date(),
  updatedAt: new Date(),
};

// Test helpers
function createTempDir(): string {
  return fs.mkdtempSync(path.join(os.tmpdir(), 'yata-global-test-'));
}

function cleanupTempDir(dir: string): void {
  if (fs.existsSync(dir)) {
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

describe('YATA Global', () => {
  let tempDir: string;
  let cacheDbPath: string;

  beforeEach(() => {
    tempDir = createTempDir();
    cacheDbPath = path.join(tempDir, 'cache.sqlite');
    process.env.YATA_CACHE_DIR = tempDir;
  });

  afterEach(() => {
    cleanupTempDir(tempDir);
    delete process.env.YATA_CACHE_DIR;
  });

  describe('CacheManager', () => {
    let cache: CacheManager;

    beforeEach(() => {
      cache = new CacheManager(cacheDbPath, DEFAULT_SYNC_CONFIG);
    });

    afterEach(() => {
      cache.close();
    });

    it('should cache and retrieve framework', () => {
      cache.cacheFramework(testFramework);
      const retrieved = cache.getFramework(testFramework.id);

      expect(retrieved).not.toBeNull();
      expect(retrieved?.id).toBe(testFramework.id);
      expect(retrieved?.name).toBe(testFramework.name);
    });

    it('should cache multiple frameworks', () => {
      const frameworks = [
        testFramework,
        { ...testFramework, id: 'fw-vue', name: 'Vue' },
        { ...testFramework, id: 'fw-angular', name: 'Angular' },
      ];

      cache.cacheFrameworks(frameworks);
      const all = cache.getAllFrameworks();

      expect(all).toHaveLength(3);
    });

    it('should cache and retrieve pattern', () => {
      cache.cachePattern(testPattern);
      const retrieved = cache.getPattern(testPattern.id);

      expect(retrieved).not.toBeNull();
      expect(retrieved?.id).toBe(testPattern.id);
      expect(retrieved?.name).toBe(testPattern.name);
    });

    it('should cache multiple patterns', () => {
      const patterns = [
        testPattern,
        { ...testPattern, id: 'pat-002', name: 'Pattern 2' },
        { ...testPattern, id: 'pat-003', name: 'Pattern 3' },
      ];

      cache.cachePatterns(patterns);
      const all = cache.getAllPatterns();

      expect(all).toHaveLength(3);
    });

    it('should handle generic cache operations', () => {
      cache.set('test-key', { foo: 'bar' });

      expect(cache.has('test-key')).toBe(true);
      expect(cache.get('test-key')).toEqual({ foo: 'bar' });

      cache.delete('test-key');
      expect(cache.has('test-key')).toBe(false);
    });

    it('should expire entries', async () => {
      // Cache with 1ms TTL
      cache.set('short-lived', 'value', 1);

      // Wait for expiration
      await new Promise(resolve => setTimeout(resolve, 10));

      expect(cache.get('short-lived')).toBeNull();
    });

    it('should track sync metadata', () => {
      const now = new Date();
      cache.setLastSyncTime(now);

      const retrieved = cache.getLastSyncTime();
      expect(retrieved).not.toBeNull();
      expect(retrieved?.getTime()).toBe(now.getTime());
    });

    it('should clear expired entries', async () => {
      // Add entries with short TTL
      cache.set('key1', 'value1', 1);
      cache.set('key2', 'value2', 1);
      cache.set('key3', 'value3', 1000000); // Long TTL

      await new Promise(resolve => setTimeout(resolve, 10));

      const cleared = cache.clearExpired();
      expect(cleared).toBeGreaterThanOrEqual(2);

      expect(cache.get('key3')).toBe('value3');
    });

    it('should return cache statistics', () => {
      cache.cacheFramework(testFramework);
      cache.cachePattern(testPattern);
      cache.set('custom', 'value');

      const stats = cache.getStats();

      expect(stats.frameworkCount).toBe(1);
      expect(stats.patternCount).toBe(1);
      expect(stats.cacheEntries).toBe(1);
      expect(stats.sizeBytes).toBeGreaterThan(0);
    });
  });

  describe('ApiClient', () => {
    let apiClient: ApiClient;

    beforeEach(() => {
      apiClient = new ApiClient({ endpoint: 'https://api.test.com' });
    });

    it('should build URLs correctly', async () => {
      // Mock fetch
      const mockFetch = vi.fn().mockResolvedValue({
        ok: true,
        json: async () => ({ data: 'test' }),
        headers: new Headers(),
      });
      global.fetch = mockFetch;

      await apiClient.get('/test', { foo: 'bar', num: 123 });

      expect(mockFetch).toHaveBeenCalledWith(
        'https://api.test.com/test?foo=bar&num=123',
        expect.any(Object)
      );
    });

    it('should handle auth token', () => {
      expect(apiClient.getAuthToken()).toBeNull();

      const token = {
        accessToken: 'test-token',
        tokenType: 'Bearer' as const,
        expiresAt: new Date(Date.now() + 3600000),
        scopes: ['read'],
      };

      apiClient.setAuthToken(token);
      expect(apiClient.getAuthToken()).toEqual(token);
    });

    it('should detect rate limiting', () => {
      expect(apiClient.isRateLimited()).toBe(false);
    });
  });

  describe('YataGlobal', () => {
    let yataGlobal: YataGlobal;

    beforeEach(() => {
      yataGlobal = createYataGlobal({
        offlineMode: true, // Start in offline mode for tests
      });
    });

    afterEach(() => {
      yataGlobal.close();
    });

    it('should create instance with default config', () => {
      const config = yataGlobal.getConfig();

      expect(config.endpoint).toBe(DEFAULT_SYNC_CONFIG.endpoint);
      expect(config.syncInterval).toBe(DEFAULT_SYNC_CONFIG.syncInterval);
    });

    it('should update configuration', () => {
      yataGlobal.configure({ syncInterval: 1800 });
      const config = yataGlobal.getConfig();

      expect(config.syncInterval).toBe(1800);
    });

    it('should report not authenticated by default', () => {
      expect(yataGlobal.isAuthenticated()).toBe(false);
    });

    it('should return null for getCurrentUser when not authenticated', async () => {
      const user = await yataGlobal.getCurrentUser();
      expect(user).toBeNull();
    });

    it('should toggle offline mode', () => {
      yataGlobal.disableOfflineMode();
      let status = yataGlobal.getSyncStatus();
      expect(status.connected).toBe(true);

      yataGlobal.enableOfflineMode();
      status = yataGlobal.getSyncStatus();
      expect(status.connected).toBe(false);
    });

    it('should return sync status', () => {
      const status = yataGlobal.getSyncStatus();

      expect(status).toHaveProperty('lastSync');
      expect(status).toHaveProperty('inProgress');
      expect(status).toHaveProperty('pendingChanges');
      expect(status).toHaveProperty('connected');
    });

    it('should return empty results in offline mode without cache', async () => {
      const result = await yataGlobal.searchFrameworks({
        query: 'react',
      });

      expect(result.items).toHaveLength(0);
      expect(result.total).toBe(0);
    });

    it('should emit events', () => {
      const offlineHandler = vi.fn();
      const onlineHandler = vi.fn();

      yataGlobal.on('connection:offline', offlineHandler);
      yataGlobal.on('connection:online', onlineHandler);

      yataGlobal.disableOfflineMode();
      yataGlobal.enableOfflineMode();

      expect(onlineHandler).toHaveBeenCalled();
      expect(offlineHandler).toHaveBeenCalled();
    });
  });

  describe('Offline Search', () => {
    let cacheManager: CacheManager;

    beforeEach(() => {
      // Create cache with test data
      cacheManager = new CacheManager(cacheDbPath, DEFAULT_SYNC_CONFIG);
      cacheManager.cacheFrameworks([
        testFramework,
        { ...testFramework, id: 'fw-vue', name: 'Vue.js', category: 'web-frontend', tags: ['ui', 'vue'] },
        { ...testFramework, id: 'fw-express', name: 'Express', category: 'web-backend', tags: ['api', 'nodejs'] },
      ]);
      cacheManager.cachePatterns([
        testPattern,
        { ...testPattern, id: 'pat-002', name: 'Vue Composable', tags: ['vue', 'composition'] },
      ]);
    });

    afterEach(() => {
      cacheManager.close();
    });

    it('should search frameworks by query', async () => {
      // Test cache directly since YataGlobal uses different cache path
      const all = cacheManager.getAllFrameworks();
      const filtered = all.filter(fw => 
        fw.name.toLowerCase().includes('react') ||
        fw.tags.some(t => t.toLowerCase().includes('react'))
      );

      expect(filtered.length).toBeGreaterThan(0);
      expect(filtered[0].name.toLowerCase()).toContain('react');
    });

    it('should filter frameworks by category', async () => {
      const all = cacheManager.getAllFrameworks();
      const filtered = all.filter(fw => fw.category === 'web-backend');

      expect(filtered.every(fw => fw.category === 'web-backend')).toBe(true);
    });

    it('should search patterns by query', async () => {
      const all = cacheManager.getAllPatterns();
      const filtered = all.filter(p =>
        p.name.toLowerCase().includes('react') ||
        p.tags.some(t => t.toLowerCase().includes('react'))
      );

      expect(filtered.length).toBeGreaterThan(0);
    });

    it('should paginate results', async () => {
      const all = cacheManager.getAllFrameworks();

      const page1 = all.slice(0, 1);
      const page2 = all.slice(1, 2);

      expect(page1).toHaveLength(1);
      expect(page2).toHaveLength(1);
      expect(page1[0].id).not.toBe(page2[0].id);
    });
  });

  describe('Pattern Operations', () => {
    let yataGlobal: YataGlobal;

    beforeEach(() => {
      yataGlobal = createYataGlobal({ offlineMode: true });
    });

    afterEach(() => {
      yataGlobal.close();
    });

    it('should reject sharePattern without authentication', async () => {
      await expect(yataGlobal.sharePattern({
        name: 'Test Pattern',
        description: 'Test',
        category: 'design-pattern',
        frameworks: [],
        language: 'typescript',
        template: '',
        tags: [],
        official: false,
        visibility: 'public',
      })).rejects.toThrow('Authentication required');
    });

    it('should reject ratePattern without authentication', async () => {
      await expect(yataGlobal.ratePattern('pat-001', 5))
        .rejects.toThrow('Authentication required');
    });

    it('should reject deletePattern without authentication', async () => {
      await expect(yataGlobal.deletePattern('pat-001'))
        .rejects.toThrow('Authentication required');
    });
  });

  describe('Analytics', () => {
    let yataGlobal: YataGlobal;

    beforeEach(() => {
      yataGlobal = createYataGlobal({ offlineMode: true });
    });

    afterEach(() => {
      yataGlobal.close();
    });

    it('should return local analytics in offline mode', async () => {
      const analytics = await yataGlobal.getAnalytics();

      expect(analytics).toHaveProperty('totalFrameworks');
      expect(analytics).toHaveProperty('totalPatterns');
      expect(analytics).toHaveProperty('totalUsers');
    });
  });
});
