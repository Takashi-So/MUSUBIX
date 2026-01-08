/**
 * LibraryStore Tests
 *
 * REQ-LL-002: ライブラリ成長
 * Test-First approach
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { createLibraryStore, type LibraryStore } from '../../src/library/LibraryStore.js';
import type { LearnedPattern, PatternQuery } from '../../src/types.js';

describe('LibraryStore', () => {
  let store: LibraryStore;

  const createTestPattern = (overrides: Partial<LearnedPattern> = {}): LearnedPattern => ({
    id: `PAT-${Date.now()}-${Math.random().toString(36).slice(2, 7)}`,
    name: 'Test Pattern',
    description: 'A test pattern',
    level: 'concrete',
    ast: { type: 'Declaration' },
    confidence: 0.8,
    usageCount: 5,
    tags: ['test'],
    createdAt: new Date(),
    updatedAt: new Date(),
    ...overrides,
  });

  beforeEach(() => {
    store = createLibraryStore();
  });

  describe('createLibraryStore', () => {
    it('should create a LibraryStore instance', () => {
      expect(store).toBeDefined();
      expect(store.add).toBeDefined();
      expect(store.get).toBeDefined();
      expect(store.search).toBeDefined();
      expect(store.getAll).toBeDefined();
      expect(store.update).toBeDefined();
      expect(store.delete).toBeDefined();
      expect(store.count).toBeDefined();
    });
  });

  describe('add', () => {
    it('should add a pattern to the store', async () => {
      const pattern = createTestPattern({ id: 'PAT-001' });
      await store.add(pattern);

      const count = await store.count();
      expect(count).toBe(1);
    });

    it('should allow adding multiple patterns', async () => {
      await store.add(createTestPattern({ id: 'PAT-001' }));
      await store.add(createTestPattern({ id: 'PAT-002' }));
      await store.add(createTestPattern({ id: 'PAT-003' }));

      const count = await store.count();
      expect(count).toBe(3);
    });

    it('should replace pattern with same ID', async () => {
      const pattern1 = createTestPattern({ id: 'PAT-001', name: 'First' });
      const pattern2 = createTestPattern({ id: 'PAT-001', name: 'Second' });

      await store.add(pattern1);
      await store.add(pattern2);

      const count = await store.count();
      expect(count).toBe(1);

      const retrieved = await store.get('PAT-001');
      expect(retrieved?.name).toBe('Second');
    });
  });

  describe('get', () => {
    it('should retrieve a pattern by ID', async () => {
      const pattern = createTestPattern({ id: 'PAT-001', name: 'Test' });
      await store.add(pattern);

      const retrieved = await store.get('PAT-001');

      expect(retrieved).not.toBeNull();
      expect(retrieved?.id).toBe('PAT-001');
      expect(retrieved?.name).toBe('Test');
    });

    it('should return null for non-existent ID', async () => {
      const retrieved = await store.get('non-existent');

      expect(retrieved).toBeNull();
    });
  });

  describe('search', () => {
    beforeEach(async () => {
      await store.add(createTestPattern({
        id: 'PAT-001',
        level: 'concrete',
        confidence: 0.9,
        usageCount: 10,
        tags: ['utility', 'common'],
      }));
      await store.add(createTestPattern({
        id: 'PAT-002',
        level: 'template',
        confidence: 0.7,
        usageCount: 5,
        tags: ['factory'],
      }));
      await store.add(createTestPattern({
        id: 'PAT-003',
        level: 'concept',
        confidence: 0.5,
        usageCount: 2,
        tags: ['utility'],
      }));
    });

    it('should return all patterns with empty query', async () => {
      const results = await store.search({});

      expect(results).toHaveLength(3);
    });

    it('should filter by level', async () => {
      const results = await store.search({ level: 'concrete' });

      expect(results).toHaveLength(1);
      expect(results[0].id).toBe('PAT-001');
    });

    it('should filter by tags', async () => {
      const results = await store.search({ tags: ['utility'] });

      expect(results).toHaveLength(2);
      expect(results.map((p) => p.id)).toContain('PAT-001');
      expect(results.map((p) => p.id)).toContain('PAT-003');
    });

    it('should filter by minimum confidence', async () => {
      const results = await store.search({ minConfidence: 0.8 });

      expect(results).toHaveLength(1);
      expect(results[0].id).toBe('PAT-001');
    });

    it('should filter by minimum usage count', async () => {
      const results = await store.search({ minUsageCount: 5 });

      expect(results).toHaveLength(2);
    });

    it('should apply limit', async () => {
      const results = await store.search({ limit: 2 });

      expect(results).toHaveLength(2);
    });

    it('should combine multiple filters', async () => {
      const query: PatternQuery = {
        tags: ['utility'],
        minConfidence: 0.6,
      };
      const results = await store.search(query);

      expect(results).toHaveLength(1);
      expect(results[0].id).toBe('PAT-001');
    });
  });

  describe('getAll', () => {
    it('should return empty array for empty store', async () => {
      const all = await store.getAll();

      expect(all).toEqual([]);
    });

    it('should return all patterns', async () => {
      await store.add(createTestPattern({ id: 'PAT-001' }));
      await store.add(createTestPattern({ id: 'PAT-002' }));

      const all = await store.getAll();

      expect(all).toHaveLength(2);
    });
  });

  describe('update', () => {
    it('should update pattern fields', async () => {
      await store.add(createTestPattern({ id: 'PAT-001', confidence: 0.5 }));

      await store.update('PAT-001', { confidence: 0.9 });

      const pattern = await store.get('PAT-001');
      expect(pattern?.confidence).toBe(0.9);
    });

    it('should preserve other fields when updating', async () => {
      await store.add(createTestPattern({
        id: 'PAT-001',
        name: 'Original Name',
        confidence: 0.5,
      }));

      await store.update('PAT-001', { confidence: 0.9 });

      const pattern = await store.get('PAT-001');
      expect(pattern?.name).toBe('Original Name');
    });

    it('should do nothing for non-existent ID', async () => {
      await store.update('non-existent', { confidence: 0.9 });

      const count = await store.count();
      expect(count).toBe(0);
    });
  });

  describe('delete', () => {
    it('should remove a pattern', async () => {
      await store.add(createTestPattern({ id: 'PAT-001' }));
      await store.add(createTestPattern({ id: 'PAT-002' }));

      await store.delete('PAT-001');

      const count = await store.count();
      expect(count).toBe(1);

      const deleted = await store.get('PAT-001');
      expect(deleted).toBeNull();
    });

    it('should do nothing for non-existent ID', async () => {
      await store.add(createTestPattern({ id: 'PAT-001' }));

      await store.delete('non-existent');

      const count = await store.count();
      expect(count).toBe(1);
    });
  });

  describe('count', () => {
    it('should return 0 for empty store', async () => {
      const count = await store.count();

      expect(count).toBe(0);
    });

    it('should return correct count after operations', async () => {
      await store.add(createTestPattern({ id: 'PAT-001' }));
      await store.add(createTestPattern({ id: 'PAT-002' }));
      await store.add(createTestPattern({ id: 'PAT-003' }));
      await store.delete('PAT-002');

      const count = await store.count();
      expect(count).toBe(2);
    });
  });
});
