/**
 * IterativeCompressor Tests
 * @module @nahisaho/musubix-library-learner
 * @see TSK-LL-103
 * @see DES-LL-103
 * @see REQ-LL-103 30%+ size reduction, 95% coverage retention
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createIterativeCompressor,
  type IterativeCompressor,
} from '../IterativeCompressor.js';
import type { LearnedPattern, ConcretePattern } from '../../types.js';

describe('IterativeCompressor', () => {
  let compressor: IterativeCompressor;

  // Helper to create mock patterns
  const createPattern = (
    id: string,
    name: string,
    similarity: number
  ): LearnedPattern => ({
    id,
    name,
    level: 1,
    content: {
      id,
      ast: { type: 'Expression', value: similarity },
      occurrenceCount: 5,
      locations: [],
    } as ConcretePattern,
    usageCount: 10,
    confidence: 0.8,
    createdAt: new Date(),
    lastUsedAt: new Date(),
    tags: [`group-${Math.floor(similarity * 10)}`],
  });

  beforeEach(() => {
    compressor = createIterativeCompressor();
  });

  describe('Factory Function', () => {
    it('should create an IterativeCompressor instance', () => {
      const instance = createIterativeCompressor();
      expect(instance).toBeDefined();
      expect(typeof instance.compress).toBe('function');
    });

    it('should create with custom config', () => {
      const instance = createIterativeCompressor({
        similarityThreshold: 0.85,
        minPatterns: 50,
        targetReduction: 0.4,
      });
      expect(instance).toBeDefined();
    });
  });

  describe('shouldCompress', () => {
    it('should return false for less than 100 patterns', () => {
      const patterns = Array.from({ length: 50 }, (_, i) =>
        createPattern(`PAT-${i}`, `Pattern ${i}`, 0.5)
      );

      expect(compressor.shouldCompress(patterns)).toBe(false);
    });

    it('should return true for 100+ patterns', () => {
      const patterns = Array.from({ length: 100 }, (_, i) =>
        createPattern(`PAT-${i}`, `Pattern ${i}`, (i % 10) / 10)
      );

      expect(compressor.shouldCompress(patterns)).toBe(true);
    });

    it('should respect custom minimum threshold', () => {
      const customCompressor = createIterativeCompressor({ minPatterns: 50 });
      const patterns = Array.from({ length: 60 }, (_, i) =>
        createPattern(`PAT-${i}`, `Pattern ${i}`, 0.5)
      );

      expect(customCompressor.shouldCompress(patterns)).toBe(true);
    });
  });

  describe('compress', () => {
    it('should reduce pattern count by 30%+', async () => {
      // Create 150 patterns with some similar ones
      const patterns: LearnedPattern[] = [];
      for (let group = 0; group < 15; group++) {
        for (let i = 0; i < 10; i++) {
          patterns.push(
            createPattern(
              `PAT-${group}-${i}`,
              `Pattern ${group}-${i}`,
              group * 0.1 + i * 0.01
            )
          );
        }
      }

      const result = await compressor.compress(patterns);

      expect(result.compressedPatterns).toBeDefined();
      expect(result.compressedPatterns.length).toBeLessThan(patterns.length);

      const reduction =
        1 - result.compressedPatterns.length / patterns.length;
      expect(reduction).toBeGreaterThanOrEqual(0.3);
    });

    it('should maintain 95%+ coverage', async () => {
      const patterns = Array.from({ length: 120 }, (_, i) =>
        createPattern(`PAT-${i}`, `Pattern ${i}`, (i % 5) / 10)
      );

      const result = await compressor.compress(patterns);

      expect(result.coverageRetained).toBeGreaterThanOrEqual(0.95);
    });

    it('should return compression report', async () => {
      const patterns = Array.from({ length: 100 }, (_, i) =>
        createPattern(`PAT-${i}`, `Pattern ${i}`, (i % 10) / 10)
      );

      const result = await compressor.compress(patterns);

      expect(result.originalCount).toBe(100);
      expect(result.compressedCount).toBeDefined();
      expect(result.mergedGroups).toBeDefined();
      expect(result.coverageRetained).toBeDefined();
      expect(result.compressionRatio).toBeDefined();
    });

    it('should handle empty patterns array', async () => {
      const result = await compressor.compress([]);

      expect(result.compressedPatterns).toEqual([]);
      expect(result.originalCount).toBe(0);
      expect(result.compressedCount).toBe(0);
    });

    it('should handle patterns with no similar groups', async () => {
      // Each pattern completely unique
      const patterns = Array.from({ length: 100 }, (_, i) =>
        createPattern(`PAT-${i}`, `Unique Pattern ${i}`, i / 100)
      );

      const result = await compressor.compress(patterns);

      // Should still compress some based on other criteria
      expect(result.compressedPatterns).toBeDefined();
    });
  });

  describe('Similarity Calculation', () => {
    it('should identify similar patterns correctly', () => {
      const pattern1 = createPattern('PAT-1', 'ValidateInput', 0.5);
      const pattern2 = createPattern('PAT-2', 'ValidateForm', 0.5);
      const pattern3 = createPattern('PAT-3', 'SendEmail', 0.9);

      const similarity12 = compressor.calculateSimilarity(pattern1, pattern2);
      const similarity13 = compressor.calculateSimilarity(pattern1, pattern3);

      // Similar patterns should have higher similarity
      expect(similarity12).toBeGreaterThan(similarity13);
    });

    it('should return 1.0 for identical patterns', () => {
      const pattern = createPattern('PAT-1', 'TestPattern', 0.5);

      const similarity = compressor.calculateSimilarity(pattern, pattern);

      expect(similarity).toBe(1.0);
    });
  });

  describe('Merge Patterns', () => {
    it('should merge similar patterns into one', async () => {
      const similarPatterns = [
        createPattern('PAT-1', 'ValidateInput', 0.5),
        createPattern('PAT-2', 'ValidateForm', 0.5),
        createPattern('PAT-3', 'ValidateData', 0.5),
      ];

      const merged = await compressor.mergePatterns(similarPatterns);

      expect(merged).toBeDefined();
      expect(merged.usageCount).toBe(30); // Combined usage
      expect(merged.confidence).toBeGreaterThanOrEqual(
        Math.max(...similarPatterns.map((p) => p.confidence))
      );
    });

    it('should preserve highest confidence after merge', async () => {
      const patterns = [
        { ...createPattern('PAT-1', 'Test1', 0.5), confidence: 0.7 },
        { ...createPattern('PAT-2', 'Test2', 0.5), confidence: 0.9 },
        { ...createPattern('PAT-3', 'Test3', 0.5), confidence: 0.8 },
      ];

      const merged = await compressor.mergePatterns(patterns);

      expect(merged.confidence).toBe(0.9);
    });
  });

  describe('Statistics', () => {
    it('should track compression statistics', async () => {
      const patterns = Array.from({ length: 100 }, (_, i) =>
        createPattern(`PAT-${i}`, `Pattern ${i}`, (i % 10) / 10)
      );

      await compressor.compress(patterns);
      const stats = compressor.getStatistics();

      expect(stats.totalCompressions).toBeGreaterThanOrEqual(1);
      expect(stats.averageReduction).toBeGreaterThanOrEqual(0);
      expect(stats.lastCompressionTime).toBeDefined();
    });

    it('should reset statistics', async () => {
      const patterns = Array.from({ length: 100 }, (_, i) =>
        createPattern(`PAT-${i}`, `Pattern ${i}`, 0.5)
      );

      await compressor.compress(patterns);
      compressor.resetStatistics();
      const stats = compressor.getStatistics();

      expect(stats.totalCompressions).toBe(0);
    });
  });

  describe('Configuration', () => {
    it('should get current config', () => {
      const config = compressor.getConfig();

      expect(config.similarityThreshold).toBeDefined();
      expect(config.minPatterns).toBeDefined();
      expect(config.targetReduction).toBeDefined();
    });

    it('should update config', () => {
      compressor.updateConfig({ similarityThreshold: 0.9 });
      const config = compressor.getConfig();

      expect(config.similarityThreshold).toBe(0.9);
    });
  });

  describe('Serialization', () => {
    it('should serialize to JSON', () => {
      const json = compressor.toJSON();
      expect(typeof json).toBe('string');

      const parsed = JSON.parse(json);
      expect(parsed.config).toBeDefined();
      expect(parsed.statistics).toBeDefined();
    });

    it('should deserialize from JSON', () => {
      const json = JSON.stringify({
        config: {
          similarityThreshold: 0.9,
          minPatterns: 200,
          targetReduction: 0.5,
        },
        statistics: {
          totalCompressions: 5,
          averageReduction: 0.4,
          lastCompressionTime: new Date().toISOString(),
        },
      });

      expect(() => compressor.fromJSON(json)).not.toThrow();

      const config = compressor.getConfig();
      expect(config.similarityThreshold).toBe(0.9);
    });
  });
});
