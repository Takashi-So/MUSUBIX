/**
 * HierarchyManager Unit Tests
 *
 * @module @nahisaho/musubix-library-learner
 * @see TSK-LL-101
 * @see DES-LL-101
 * @see REQ-LL-101
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import {
  HierarchyManager,
  createHierarchyManager,
  DefaultHierarchyManager,
  HierarchyResult,
  HierarchyMetrics,
  AbstractionLevel,
  PromotionRecord,
} from '../../src/hierarchy/HierarchyManager.js';
import type { CodeCorpus, HierarchyPattern, PatternId } from '../../src/types.js';

describe('HierarchyManager', () => {
  let manager: HierarchyManager;

  beforeEach(() => {
    manager = createHierarchyManager();
  });

  // ==========================================================================
  // Interface Tests
  // ==========================================================================

  describe('createHierarchyManager', () => {
    it('should create a HierarchyManager instance', () => {
      expect(manager).toBeDefined();
      expect(manager).toBeInstanceOf(DefaultHierarchyManager);
    });

    it('should accept custom configuration', () => {
      const customManager = createHierarchyManager({
        maxLevels: 5,
        promotionThreshold: 0.8,
      });
      expect(customManager).toBeDefined();
      expect(customManager.getDepth()).toBe(0); // Initially empty
    });
  });

  // ==========================================================================
  // addLevel Tests
  // ==========================================================================

  describe('addLevel', () => {
    it('should add a new abstraction level', () => {
      const level: AbstractionLevel = {
        id: 1,
        name: 'concrete',
        description: 'Token-level patterns',
      };
      manager.addLevel(level);
      expect(manager.getDepth()).toBe(1);
    });

    it('should support multiple levels', () => {
      const levels: AbstractionLevel[] = [
        { id: 1, name: 'concrete', description: 'Token-level' },
        { id: 2, name: 'parameterized', description: 'Expression-level' },
        { id: 3, name: 'abstract', description: 'Function-level' },
      ];
      levels.forEach((level) => manager.addLevel(level));
      expect(manager.getDepth()).toBe(3);
    });

    it('should prevent duplicate level IDs', () => {
      const level: AbstractionLevel = { id: 1, name: 'concrete', description: '' };
      manager.addLevel(level);
      expect(() => manager.addLevel(level)).toThrow(/duplicate/i);
    });
  });

  // ==========================================================================
  // extractHierarchy Tests
  // ==========================================================================

  describe('extractHierarchy', () => {
    const mockCorpus: CodeCorpus = {
      id: 'test-corpus',
      files: [
        {
          path: 'test.ts',
          content: `
            function add(a: number, b: number) { return a + b; }
            function sub(a: number, b: number) { return a - b; }
            function mul(a: number, b: number) { return a * b; }
          `,
          language: 'typescript',
        },
      ],
    };

    it('should extract hierarchical abstractions from corpus', async () => {
      const result = await manager.extractHierarchy(mockCorpus);
      expect(result).toBeDefined();
      expect(result.levels).toBeInstanceOf(Map);
    });

    it('should extract at least 3 levels of abstraction', async () => {
      const result = await manager.extractHierarchy(mockCorpus);
      expect(result.levels.size).toBeGreaterThanOrEqual(3);
    });

    it('should return patterns for each level', async () => {
      const result = await manager.extractHierarchy(mockCorpus);
      for (const [level, patterns] of result.levels) {
        expect(Array.isArray(patterns)).toBe(true);
      }
    });

    it('should include promotion records', async () => {
      const result = await manager.extractHierarchy(mockCorpus);
      expect(result.promotions).toBeDefined();
      expect(Array.isArray(result.promotions)).toBe(true);
    });

    it('should include metrics', async () => {
      const result = await manager.extractHierarchy(mockCorpus);
      expect(result.metrics).toBeDefined();
      expect(result.metrics.extractionTimeMs).toBeGreaterThanOrEqual(0);
      expect(result.metrics.patternsPerLevel).toBeDefined();
      expect(result.metrics.compressionRatio).toBeGreaterThanOrEqual(0);
    });

    it('should complete within 10 seconds per 1000 LOC', async () => {
      // 1000 LOC corpus simulation
      const largeCorpus: CodeCorpus = {
        id: 'large-corpus',
        files: Array.from({ length: 10 }, (_, i) => ({
          path: `file${i}.ts`,
          content: Array.from({ length: 100 }, () => 
            'function foo(x: number): number { return x * 2; }\n'
          ).join(''),
          language: 'typescript' as const,
        })),
      };

      const startTime = Date.now();
      await manager.extractHierarchy(largeCorpus);
      const elapsed = Date.now() - startTime;

      // 10 seconds = 10000ms
      expect(elapsed).toBeLessThan(10000);
    });
  });

  // ==========================================================================
  // shouldPromote Tests
  // ==========================================================================

  describe('shouldPromote', () => {
    it('should return true for patterns meeting promotion criteria', () => {
      const pattern: HierarchyPattern = {
        id: 'pattern-1' as PatternId,
        level: 1,
        occurrenceCount: 10,
        confidence: 0.9,
        ast: { type: 'Identifier', name: 'x' },
        sourceLocations: [],
      };
      expect(manager.shouldPromote(pattern)).toBe(true);
    });

    it('should return false for patterns not meeting criteria', () => {
      const pattern: HierarchyPattern = {
        id: 'pattern-2' as PatternId,
        level: 1,
        occurrenceCount: 1,
        confidence: 0.3,
        ast: { type: 'Identifier', name: 'y' },
        sourceLocations: [],
      };
      expect(manager.shouldPromote(pattern)).toBe(false);
    });

    it('should use configurable threshold', () => {
      const strictManager = createHierarchyManager({
        promotionThreshold: 0.95,
        minOccurrences: 20,
      });
      const pattern: HierarchyPattern = {
        id: 'pattern-3' as PatternId,
        level: 1,
        occurrenceCount: 10,
        confidence: 0.9,
        ast: { type: 'Identifier', name: 'z' },
        sourceLocations: [],
      };
      expect(strictManager.shouldPromote(pattern)).toBe(false);
    });
  });

  // ==========================================================================
  // getDepth Tests
  // ==========================================================================

  describe('getDepth', () => {
    it('should return 0 for empty manager', () => {
      expect(manager.getDepth()).toBe(0);
    });

    it('should return correct depth after adding levels', () => {
      manager.addLevel({ id: 1, name: 'L1', description: '' });
      manager.addLevel({ id: 2, name: 'L2', description: '' });
      expect(manager.getDepth()).toBe(2);
    });

    it('should update after extraction', async () => {
      const corpus: CodeCorpus = {
        id: 'test',
        files: [{ path: 't.ts', content: 'const x = 1;', language: 'typescript' }],
      };
      await manager.extractHierarchy(corpus);
      expect(manager.getDepth()).toBeGreaterThanOrEqual(3);
    });
  });

  // ==========================================================================
  // getLevels Tests
  // ==========================================================================

  describe('getLevels', () => {
    it('should return all registered levels', () => {
      const levels: AbstractionLevel[] = [
        { id: 1, name: 'concrete', description: '' },
        { id: 2, name: 'parameterized', description: '' },
        { id: 3, name: 'abstract', description: '' },
      ];
      levels.forEach((l) => manager.addLevel(l));

      const result = manager.getLevels();
      expect(result).toHaveLength(3);
      expect(result.map((l) => l.name)).toEqual(['concrete', 'parameterized', 'abstract']);
    });
  });

  // ==========================================================================
  // Integration with PatternMiner
  // ==========================================================================

  describe('integration with PatternMiner', () => {
    it('should delegate mining to PatternMiner', async () => {
      const mockMiner = {
        mine: vi.fn().mockResolvedValue([]),
      };
      const managerWithMiner = createHierarchyManager({
        patternMiner: mockMiner as any,
      });

      const corpus: CodeCorpus = {
        id: 'test',
        files: [{ path: 't.ts', content: 'const x = 1;', language: 'typescript' }],
      };

      await managerWithMiner.extractHierarchy(corpus);
      expect(mockMiner.mine).toHaveBeenCalled();
    });
  });
});
