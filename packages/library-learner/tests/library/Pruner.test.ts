/**
 * Pruner Tests
 *
 * REQ-LL-002: ライブラリ成長
 * Test-First approach
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { createPruner, type Pruner } from '../../src/library/Pruner.js';
import { createLibraryStore, type LibraryStore } from '../../src/library/LibraryStore.js';
import type { LearnedPattern } from '../../src/types.js';

describe('Pruner', () => {
  let pruner: Pruner;
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
    pruner = createPruner();
    store = createLibraryStore();
  });

  describe('createPruner', () => {
    it('should create a Pruner instance', () => {
      expect(pruner).toBeDefined();
      expect(pruner.applyDecay).toBeDefined();
      expect(pruner.prune).toBeDefined();
    });
  });

  describe('applyDecay', () => {
    it('should reduce confidence by decay rate', async () => {
      await store.add(createTestPattern({ id: 'PAT-001', confidence: 1.0 }));

      await pruner.applyDecay(store, 0.9);

      const pattern = await store.get('PAT-001');
      expect(pattern?.confidence).toBeCloseTo(0.9, 5);
    });

    it('should apply decay to all patterns', async () => {
      await store.add(createTestPattern({ id: 'PAT-001', confidence: 1.0 }));
      await store.add(createTestPattern({ id: 'PAT-002', confidence: 0.8 }));
      await store.add(createTestPattern({ id: 'PAT-003', confidence: 0.5 }));

      await pruner.applyDecay(store, 0.9);

      const pat1 = await store.get('PAT-001');
      const pat2 = await store.get('PAT-002');
      const pat3 = await store.get('PAT-003');

      expect(pat1?.confidence).toBeCloseTo(0.9, 5);
      expect(pat2?.confidence).toBeCloseTo(0.72, 5);
      expect(pat3?.confidence).toBeCloseTo(0.45, 5);
    });

    it('should do nothing for empty store', async () => {
      await pruner.applyDecay(store, 0.9);

      const count = await store.count();
      expect(count).toBe(0);
    });

    it('should handle zero decay rate', async () => {
      await store.add(createTestPattern({ id: 'PAT-001', confidence: 1.0 }));

      await pruner.applyDecay(store, 0);

      const pattern = await store.get('PAT-001');
      expect(pattern?.confidence).toBe(0);
    });
  });

  describe('prune', () => {
    it('should remove patterns below threshold', async () => {
      await store.add(createTestPattern({ id: 'PAT-001', confidence: 0.9 }));
      await store.add(createTestPattern({ id: 'PAT-002', confidence: 0.3 }));
      await store.add(createTestPattern({ id: 'PAT-003', confidence: 0.1 }));

      const report = await pruner.prune(store, 0.5);

      expect(report.patternsPruned).toBe(2);
      expect(report.prunedIds).toContain('PAT-002');
      expect(report.prunedIds).toContain('PAT-003');

      const count = await store.count();
      expect(count).toBe(1);
    });

    it('should return empty report when no patterns match', async () => {
      await store.add(createTestPattern({ id: 'PAT-001', confidence: 0.9 }));
      await store.add(createTestPattern({ id: 'PAT-002', confidence: 0.8 }));

      const report = await pruner.prune(store, 0.5);

      expect(report.patternsPruned).toBe(0);
      expect(report.prunedIds).toEqual([]);
    });

    it('should return report for empty store', async () => {
      const report = await pruner.prune(store, 0.5);

      expect(report.patternsPruned).toBe(0);
      expect(report.prunedIds).toEqual([]);
      expect(report.duration).toBeGreaterThanOrEqual(0);
    });

    it('should track duration', async () => {
      await store.add(createTestPattern({ id: 'PAT-001', confidence: 0.1 }));

      const report = await pruner.prune(store, 0.5);

      expect(typeof report.duration).toBe('number');
      expect(report.duration).toBeGreaterThanOrEqual(0);
    });

    it('should prune all patterns when threshold is 1.0', async () => {
      await store.add(createTestPattern({ id: 'PAT-001', confidence: 0.9 }));
      await store.add(createTestPattern({ id: 'PAT-002', confidence: 0.99 }));

      const report = await pruner.prune(store, 1.0);

      expect(report.patternsPruned).toBe(2);
      const count = await store.count();
      expect(count).toBe(0);
    });
  });
});
