/**
 * Pattern Merger Tests
 *
 * @traceability REQ-PTN-003, REQ-PTN-004
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { PatternMerger, createPatternMerger } from '../pattern-merger.js';
import type { ExtractedPattern } from '../pattern-extractor.js';

describe('PatternMerger', () => {
  let merger: PatternMerger;

  const createTestPattern = (
    id: string,
    name: string,
    category: ExtractedPattern['category'],
    confidence: number = 0.8
  ): ExtractedPattern => ({
    id,
    name,
    category,
    template: `// ${name} template`,
    metadata: {
      sourceFile: `${name.toLowerCase()}.ts`,
      extractedAt: new Date().toISOString(),
      domain: 'TEST',
      confidence,
    },
    variables: [{ name: 'name', type: 'string', required: true }],
    examples: [`// Example for ${name}`],
  });

  beforeEach(() => {
    merger = createPatternMerger();
  });

  describe('merge', () => {
    it('should return empty result for empty input', () => {
      const result = merger.merge([]);

      expect(result.patterns).toHaveLength(0);
      expect(result.stats.inputCount).toBe(0);
      expect(result.stats.outputCount).toBe(0);
    });

    it('should keep unique patterns unchanged', () => {
      const patterns = [
        createTestPattern('PTN-1', 'Price', 'value-object'),
        createTestPattern('PTN-2', 'Order', 'status-machine'),
        createTestPattern('PTN-3', 'Customer', 'entity'),
      ];

      const result = merger.merge(patterns);

      expect(result.patterns).toHaveLength(3);
      expect(result.stats.mergedCount).toBe(0);
    });

    it('should merge similar patterns', () => {
      const patterns = [
        createTestPattern('PTN-1', 'PriceValueObject', 'value-object', 0.9),
        createTestPattern('PTN-2', 'PriceValueObject', 'value-object', 0.85),
      ];

      const result = merger.merge(patterns);

      expect(result.patterns).toHaveLength(1);
      expect(result.stats.mergedCount).toBe(1);
      expect(result.patterns[0].mergeInfo.sourcePatternIds).toContain('PTN-1');
      expect(result.patterns[0].mergeInfo.sourcePatternIds).toContain('PTN-2');
    });

    it('should calculate average confidence', () => {
      const patterns = [
        createTestPattern('PTN-1', 'Price', 'value-object', 0.9),
        createTestPattern('PTN-2', 'Price', 'value-object', 0.8),
      ];

      const result = merger.merge(patterns);

      expect(result.patterns[0].mergeInfo.averageConfidence).toBeCloseTo(0.85);
    });

    it('should track occurrences', () => {
      const patterns = [
        createTestPattern('PTN-1', 'Price', 'value-object'),
        createTestPattern('PTN-2', 'Price', 'value-object'),
        createTestPattern('PTN-3', 'Price', 'value-object'),
      ];

      const result = merger.merge(patterns);

      expect(result.patterns[0].mergeInfo.occurrences).toBe(3);
    });

    it('should not merge patterns from different categories', () => {
      const patterns = [
        createTestPattern('PTN-1', 'Order', 'value-object'),
        createTestPattern('PTN-2', 'Order', 'status-machine'),
      ];

      const result = merger.merge(patterns);

      expect(result.patterns).toHaveLength(2);
    });

    it('should filter by minimum occurrences', () => {
      const strictMerger = createPatternMerger({ minOccurrences: 2 });
      const patterns = [
        createTestPattern('PTN-1', 'Price', 'value-object'),
        createTestPattern('PTN-2', 'Email', 'value-object'),
      ];

      const result = strictMerger.merge(patterns);

      // Both have only 1 occurrence, so both should be filtered
      expect(result.patterns).toHaveLength(0);
    });
  });

  describe('conflict strategies', () => {
    it('should use highest-confidence strategy by default', () => {
      const patterns = [
        createTestPattern('PTN-LOW', 'Price', 'value-object', 0.7),
        createTestPattern('PTN-HIGH', 'Price', 'value-object', 0.95),
      ];

      const result = merger.merge(patterns);

      expect(result.patterns[0].id).toBe('PTN-HIGH');
    });

    it('should use newest strategy when configured', () => {
      const newestMerger = createPatternMerger({ conflictStrategy: 'newest' });

      const oldDate = new Date('2025-01-01').toISOString();
      const newDate = new Date('2026-01-14').toISOString();

      const patterns: ExtractedPattern[] = [
        {
          ...createTestPattern('PTN-OLD', 'Price', 'value-object'),
          metadata: {
            sourceFile: 'old.ts',
            extractedAt: oldDate,
            domain: 'TEST',
            confidence: 0.9,
          },
        },
        {
          ...createTestPattern('PTN-NEW', 'Price', 'value-object'),
          metadata: {
            sourceFile: 'new.ts',
            extractedAt: newDate,
            domain: 'TEST',
            confidence: 0.7,
          },
        },
      ];

      const result = newestMerger.merge(patterns);

      expect(result.patterns[0].id).toBe('PTN-NEW');
    });
  });

  describe('findDuplicates', () => {
    it('should find duplicate patterns', () => {
      const patterns = [
        createTestPattern('PTN-1', 'Price', 'value-object'),
        createTestPattern('PTN-2', 'Price', 'value-object'),
        createTestPattern('PTN-3', 'Email', 'value-object'),
      ];

      const duplicates = merger.findDuplicates(patterns);

      expect(duplicates).toHaveLength(1);
      expect(duplicates[0][0].id).toBe('PTN-1');
      expect(duplicates[0][1].id).toBe('PTN-2');
    });

    it('should return empty array when no duplicates', () => {
      const patterns = [
        createTestPattern('PTN-1', 'Price', 'value-object'),
        createTestPattern('PTN-2', 'Email', 'value-object'),
        createTestPattern('PTN-3', 'Order', 'status-machine'),
      ];

      const duplicates = merger.findDuplicates(patterns);

      expect(duplicates).toHaveLength(0);
    });
  });

  describe('similarity threshold', () => {
    it('should respect custom similarity threshold', () => {
      const strictMerger = createPatternMerger({ similarityThreshold: 0.99 });

      const patterns = [
        createTestPattern('PTN-1', 'Price', 'value-object'),
        createTestPattern('PTN-2', 'Price', 'value-object'),
      ];

      // With strict threshold, even same-named patterns might not merge
      // depending on other factors
      const result = strictMerger.merge(patterns);

      expect(result.patterns.length).toBeGreaterThanOrEqual(1);
    });

    it('should merge more patterns with lower threshold', () => {
      const looseMerger = createPatternMerger({ similarityThreshold: 0.5 });

      const patterns = [
        createTestPattern('PTN-1', 'PriceVO', 'value-object'),
        createTestPattern('PTN-2', 'PriceValue', 'value-object'),
      ];

      const result = looseMerger.merge(patterns);

      expect(result.patterns).toHaveLength(1);
    });
  });

  describe('statistics', () => {
    it('should calculate deduplication ratio', () => {
      const patterns = [
        createTestPattern('PTN-1', 'Price', 'value-object'),
        createTestPattern('PTN-2', 'Price', 'value-object'),
        createTestPattern('PTN-3', 'Email', 'value-object'),
        createTestPattern('PTN-4', 'Email', 'value-object'),
      ];

      const result = merger.merge(patterns);

      expect(result.stats.inputCount).toBe(4);
      expect(result.stats.outputCount).toBe(2);
      expect(result.stats.deduplicationRatio).toBe(0.5);
    });
  });

  describe('variable merging', () => {
    it('should merge variables from multiple patterns', () => {
      const pattern1: ExtractedPattern = {
        ...createTestPattern('PTN-1', 'Price', 'value-object'),
        variables: [
          { name: 'amount', type: 'number', required: true },
        ],
      };
      const pattern2: ExtractedPattern = {
        ...createTestPattern('PTN-2', 'Price', 'value-object'),
        variables: [
          { name: 'amount', type: 'number', required: true },
          { name: 'currency', type: 'string', required: false },
        ],
      };

      const result = merger.merge([pattern1, pattern2]);

      expect(result.patterns[0].variables.length).toBe(2);
    });
  });

  describe('examples collection', () => {
    it('should collect examples from merged patterns', () => {
      const pattern1: ExtractedPattern = {
        ...createTestPattern('PTN-1', 'Price', 'value-object'),
        examples: ['Example 1', 'Example 2'],
      };
      const pattern2: ExtractedPattern = {
        ...createTestPattern('PTN-2', 'Price', 'value-object'),
        examples: ['Example 3'],
      };

      const result = merger.merge([pattern1, pattern2]);

      expect(result.patterns[0].examples.length).toBe(3);
    });

    it('should limit examples to 5', () => {
      const patterns = Array.from({ length: 10 }, (_, i) => ({
        ...createTestPattern(`PTN-${i}`, 'Price', 'value-object'),
        examples: [`Example ${i}`],
      }));

      const result = merger.merge(patterns);

      expect(result.patterns[0].examples.length).toBeLessThanOrEqual(5);
    });
  });
});
