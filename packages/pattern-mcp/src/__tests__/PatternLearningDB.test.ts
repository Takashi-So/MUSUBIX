/**
 * PatternLearningDB Tests
 *
 * @see TSK-FR-042 - PatternLearningDBユニットテスト
 */
import { describe, it, expect, beforeEach } from 'vitest';

import {
  type LearnedPattern,
  type PatternStatus,
  type LearningSource,
  type PatternQuery,
  type PatternLearningDBConfig,
  createLearnedPattern,
  resetPatternIdCounter,
  calculatePatternStats,
  DEFAULT_PATTERN_LEARNING_CONFIG,
} from '../learning/db-types.js';

import {
  type IPatternLearningDB,
  PatternLearningDB,
  createPatternLearningDB,
} from '../learning/PatternLearningDB.js';

import type { Pattern, DesignPattern } from '../types.js';

// テスト用のモックパターン
function createMockPattern(name: string): Pattern {
  return {
    id: `PAT-${name}`,
    name,
    language: 'typescript',
    ast: { type: 'Program', children: [], startPosition: { row: 0, column: 0 }, endPosition: { row: 0, column: 0 } },
    holes: [],
    frequency: 1,
    createdAt: new Date().toISOString(),
    updatedAt: new Date().toISOString(),
  };
}

function createMockDesignPattern(name: string): DesignPattern {
  return {
    id: `DPAT-${name}`,
    name,
    category: 'structural',
    domain: ['general'],
    description: `${name} pattern`,
    problem: 'Test problem',
    solution: 'Test solution',
    applicability: ['test'],
    consequences: { positive: ['good'], negative: ['bad'] },
    implementation: '// code',
    confidence: 0.8,
  };
}

describe('PatternLearningDB', () => {
  beforeEach(() => {
    resetPatternIdCounter();
  });

  // ============================================================
  // Type Tests
  // ============================================================
  describe('createLearnedPattern', () => {
    it('should create a learned pattern with auto-generated ID', () => {
      const pattern = createMockPattern('test');
      const learned = createLearnedPattern({
        pattern,
        source: 'code-observation',
      });

      expect(learned.id).toBe('LP-00001');
      expect(learned.pattern).toBe(pattern);
      expect(learned.source).toBe('code-observation');
      expect(learned.status).toBe('candidate');
    });

    it('should be immutable', () => {
      const learned = createLearnedPattern({
        pattern: createMockPattern('test'),
        source: 'feedback',
      });

      expect(() => {
        (learned as any).confidence = 1.0;
      }).toThrow();
    });

    it('should use provided confidence', () => {
      const learned = createLearnedPattern({
        pattern: createMockPattern('test'),
        source: 'manual',
        confidence: 0.9,
      });

      expect(learned.confidence).toBe(0.9);
    });
  });

  describe('calculatePatternStats', () => {
    it('should calculate stats correctly', () => {
      const patterns = [
        { ...createLearnedPattern({ pattern: createMockPattern('a'), source: 'code-observation' }), status: 'verified' as PatternStatus, confidence: 0.8 },
        { ...createLearnedPattern({ pattern: createMockPattern('b'), source: 'feedback' }), status: 'candidate' as PatternStatus, confidence: 0.6 },
        { ...createLearnedPattern({ pattern: createMockPattern('c'), source: 'manual' }), status: 'deprecated' as PatternStatus, confidence: 0.4 },
      ];

      const stats = calculatePatternStats(patterns);

      expect(stats.totalPatterns).toBe(3);
      expect(stats.byStatus.verified).toBe(1);
      expect(stats.byStatus.candidate).toBe(1);
      expect(stats.byStatus.deprecated).toBe(1);
      expect(stats.avgConfidence).toBeCloseTo(0.6, 2);
    });

    it('should handle empty patterns', () => {
      const stats = calculatePatternStats([]);

      expect(stats.totalPatterns).toBe(0);
      expect(stats.avgConfidence).toBe(0);
    });
  });

  // ============================================================
  // PatternLearningDB Tests
  // ============================================================
  describe('add', () => {
    it('should add a pattern', async () => {
      const db = createPatternLearningDB();

      const result = await db.add({
        pattern: createMockPattern('test'),
        source: 'code-observation',
      });

      expect(result.id).toBeDefined();
      expect(result.status).toBe('candidate');
    });

    it('should add design patterns', async () => {
      const db = createPatternLearningDB();

      const result = await db.add({
        pattern: createMockDesignPattern('Singleton'),
        source: 'manual',
        confidence: 0.95,
      });

      expect(result.pattern.name).toBe('Singleton');
      expect(result.confidence).toBe(0.95);
    });

    it('should respect max patterns limit', async () => {
      const db = createPatternLearningDB({
        ...DEFAULT_PATTERN_LEARNING_CONFIG,
        maxPatterns: 3,
      });

      for (let i = 0; i < 5; i++) {
        await db.add({
          pattern: createMockPattern(`pattern-${i}`),
          source: 'code-observation',
        });
      }

      const all = await db.list();
      expect(all).toHaveLength(3);
    });
  });

  describe('get', () => {
    it('should get pattern by ID', async () => {
      const db = createPatternLearningDB();

      const added = await db.add({
        pattern: createMockPattern('test'),
        source: 'feedback',
      });

      const retrieved = await db.get(added.id);

      expect(retrieved).not.toBeNull();
      expect(retrieved?.id).toBe(added.id);
    });

    it('should return null for unknown ID', async () => {
      const db = createPatternLearningDB();

      const result = await db.get('LP-99999');

      expect(result).toBeNull();
    });
  });

  describe('update', () => {
    it('should update pattern status', async () => {
      const db = createPatternLearningDB();

      const added = await db.add({
        pattern: createMockPattern('test'),
        source: 'code-observation',
      });

      const updated = await db.update(added.id, { status: 'verified' });

      expect(updated?.status).toBe('verified');
    });

    it('should update confidence', async () => {
      const db = createPatternLearningDB();

      const added = await db.add({
        pattern: createMockPattern('test'),
        source: 'feedback',
        confidence: 0.5,
      });

      const updated = await db.update(added.id, { confidence: 0.9 });

      expect(updated?.confidence).toBe(0.9);
    });

    it('should return null for unknown ID', async () => {
      const db = createPatternLearningDB();

      const result = await db.update('LP-99999', { status: 'verified' });

      expect(result).toBeNull();
    });
  });

  describe('delete', () => {
    it('should delete pattern', async () => {
      const db = createPatternLearningDB();

      const added = await db.add({
        pattern: createMockPattern('test'),
        source: 'manual',
      });

      const deleted = await db.delete(added.id);

      expect(deleted).toBe(true);
      expect(await db.get(added.id)).toBeNull();
    });

    it('should return false for unknown ID', async () => {
      const db = createPatternLearningDB();

      const result = await db.delete('LP-99999');

      expect(result).toBe(false);
    });
  });

  describe('query', () => {
    it('should filter by status', async () => {
      const db = createPatternLearningDB();

      const p1 = await db.add({ pattern: createMockPattern('a'), source: 'code-observation' });
      const p2 = await db.add({ pattern: createMockPattern('b'), source: 'feedback' });
      await db.update(p1.id, { status: 'verified' });

      const verified = await db.query({ status: 'verified' });

      expect(verified).toHaveLength(1);
      expect(verified[0].status).toBe('verified');
    });

    it('should filter by source', async () => {
      const db = createPatternLearningDB();

      await db.add({ pattern: createMockPattern('a'), source: 'code-observation' });
      await db.add({ pattern: createMockPattern('b'), source: 'feedback' });
      await db.add({ pattern: createMockPattern('c'), source: 'manual' });

      const fromFeedback = await db.query({ source: 'feedback' });

      expect(fromFeedback).toHaveLength(1);
      expect(fromFeedback[0].source).toBe('feedback');
    });

    it('should filter by minConfidence', async () => {
      const db = createPatternLearningDB();

      await db.add({ pattern: createMockPattern('low'), source: 'code-observation', confidence: 0.3 });
      await db.add({ pattern: createMockPattern('high'), source: 'code-observation', confidence: 0.9 });

      const highConfidence = await db.query({ minConfidence: 0.7 });

      expect(highConfidence).toHaveLength(1);
      expect(highConfidence[0].confidence).toBeGreaterThanOrEqual(0.7);
    });

    it('should support limit and offset', async () => {
      const db = createPatternLearningDB();

      for (let i = 0; i < 10; i++) {
        await db.add({ pattern: createMockPattern(`p${i}`), source: 'manual' });
      }

      const page1 = await db.query({ limit: 3, offset: 0 });
      const page2 = await db.query({ limit: 3, offset: 3 });

      expect(page1).toHaveLength(3);
      expect(page2).toHaveLength(3);
      expect(page1[0].id).not.toBe(page2[0].id);
    });
  });

  describe('recordUsage', () => {
    it('should increment usage count', async () => {
      const db = createPatternLearningDB();

      const added = await db.add({
        pattern: createMockPattern('test'),
        source: 'code-observation',
      });

      await db.recordUsage(added.id);
      await db.recordUsage(added.id);

      const updated = await db.get(added.id);
      expect(updated?.usageCount).toBe(2);
    });

    it('should update lastUsedAt', async () => {
      const db = createPatternLearningDB();
      const before = Date.now();

      const added = await db.add({
        pattern: createMockPattern('test'),
        source: 'feedback',
      });

      await db.recordUsage(added.id);

      const updated = await db.get(added.id);
      expect(updated?.lastUsedAt).toBeGreaterThanOrEqual(before);
    });
  });

  describe('getStats', () => {
    it('should return statistics', async () => {
      const db = createPatternLearningDB();

      await db.add({ pattern: createMockPattern('a'), source: 'code-observation', confidence: 0.8 });
      await db.add({ pattern: createMockPattern('b'), source: 'feedback', confidence: 0.6 });

      const stats = await db.getStats();

      expect(stats.totalPatterns).toBe(2);
      expect(stats.bySource['code-observation']).toBe(1);
      expect(stats.bySource['feedback']).toBe(1);
    });
  });

  describe('clear', () => {
    it('should clear all patterns', async () => {
      const db = createPatternLearningDB();

      await db.add({ pattern: createMockPattern('a'), source: 'code-observation' });
      await db.add({ pattern: createMockPattern('b'), source: 'feedback' });

      await db.clear();

      const all = await db.list();
      expect(all).toHaveLength(0);
    });
  });
});
