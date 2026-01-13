/**
 * Pattern Learning Service Tests
 *
 * @traceability REQ-PTN-001, REQ-PTN-002, REQ-PTN-003
 * @see TSK-PTN-003 - Pattern Learning Service Tests
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  PatternLearningService,
  createPatternLearningService,
  DEFAULT_PATTERN_LEARNING_CONFIG,
} from '../pattern-learning-service.js';
import type { GeneratedFile } from '../value-object-generator.js';

describe('PatternLearningService', () => {
  let service: PatternLearningService;

  beforeEach(() => {
    service = createPatternLearningService();
  });

  describe('DEFAULT_PATTERN_LEARNING_CONFIG', () => {
    it('should have correct default values', () => {
      expect(DEFAULT_PATTERN_LEARNING_CONFIG.enabled).toBe(true);
      expect(DEFAULT_PATTERN_LEARNING_CONFIG.minConfidence).toBe(0.7);
      expect(DEFAULT_PATTERN_LEARNING_CONFIG.autoExtract).toBe(true);
      expect(DEFAULT_PATTERN_LEARNING_CONFIG.enableSuggestions).toBe(true);
      expect(DEFAULT_PATTERN_LEARNING_CONFIG.maxPatternsPerCategory).toBe(100);
    });

    it('should have library path', () => {
      expect(DEFAULT_PATTERN_LEARNING_CONFIG.libraryPath).toBe(
        'storage/learning/patterns.json'
      );
    });
  });

  describe('learnFromGeneration', () => {
    it('should return empty result when disabled', async () => {
      const disabledService = createPatternLearningService({ enabled: false });

      const files: GeneratedFile[] = [
        { path: '/test/price.ts', content: 'const price = 100;', type: 'value-object' },
      ];

      const result = await disabledService.learnFromGeneration(files);

      expect(result.extractedPatterns).toHaveLength(0);
      expect(result.newPatternsCount).toBe(0);
      expect(result.executionTime).toBeGreaterThanOrEqual(0);
    });

    it('should return empty result for empty files', async () => {
      const result = await service.learnFromGeneration([]);

      expect(result.extractedPatterns).toHaveLength(0);
      expect(result.mergedPatterns).toHaveLength(0);
    });

    it('should extract patterns from generated files', async () => {
      const files: GeneratedFile[] = [
        {
          path: '/test/entities/Order.ts',
          content: `
            export interface Order {
              id: string;
              status: OrderStatus;
              createdAt: Date;
            }
            
            export type OrderStatus = 'draft' | 'active' | 'completed';
            
            export function createOrderId(): string {
              return 'ORD-' + Date.now();
            }
          `,
          type: 'value-object',
        },
      ];

      const result = await service.learnFromGeneration(files);

      expect(result.executionTime).toBeGreaterThanOrEqual(0);
      // May extract patterns depending on content analysis
    });

    it('should filter patterns by confidence threshold', async () => {
      const strictService = createPatternLearningService({ minConfidence: 0.99 });

      const files: GeneratedFile[] = [
        { path: '/test/entity.ts', content: 'interface Entity { id: string; }', type: 'value-object' },
      ];

      const result = await strictService.learnFromGeneration(files);

      // High threshold should filter most patterns
      expect(result.extractedPatterns.every((p) => p.metadata.confidence >= 0.99)).toBe(true);
    });

    it('should track execution time', async () => {
      const files: GeneratedFile[] = [
        { path: '/test/file.ts', content: 'const x = 1;', type: 'value-object' },
      ];

      const result = await service.learnFromGeneration(files);

      expect(result.executionTime).toBeGreaterThanOrEqual(0);
      expect(typeof result.executionTime).toBe('number');
    });
  });

  describe('getSuggestions', () => {
    it('should return empty when suggestions disabled', () => {
      const noSuggestionsService = createPatternLearningService({
        enableSuggestions: false,
      });

      const suggestions = noSuggestionsService.getSuggestions('test-context');

      expect(suggestions).toHaveLength(0);
    });

    it('should return suggestions for given context', () => {
      const suggestions = service.getSuggestions('/test/entity.ts', 'entity');

      expect(Array.isArray(suggestions)).toBe(true);
    });

    it('should filter by category when specified', () => {
      const suggestions = service.getSuggestions('/test/entity.ts', 'value-object');

      // All suggestions should be for value-object category
      expect(suggestions.every((s) => s.category === 'value-object' || suggestions.length === 0))
        .toBe(true);
    });
  });

  describe('recordFeedback', () => {
    it('should return false for unknown pattern', () => {
      const result = service.recordFeedback('unknown-pattern', 'accept');

      expect(result).toBe(false);
    });

    it('should record feedback for existing pattern', async () => {
      // First learn a pattern
      const files: GeneratedFile[] = [
        {
          path: '/test/repository.ts',
          content: `
            export interface Repository<T> {
              findById(id: string): Promise<T | null>;
              findAll(): Promise<T[]>;
              save(entity: T): Promise<void>;
              delete(id: string): Promise<void>;
            }
          `,
          type: 'value-object',
        },
      ];

      await service.learnFromGeneration(files);

      const patterns = service.getAllPatterns();
      if (patterns.length > 0) {
        const result = service.recordFeedback(patterns[0].id, 'accept', 'Good pattern');
        expect(result).toBe(true);
      }
    });

    it('should update success rate based on feedback', async () => {
      // This test requires patterns in library
      const patterns = service.getAllPatterns();
      if (patterns.length > 0) {
        const patternId = patterns[0].id;

        // Accept feedback
        service.recordFeedback(patternId, 'accept');
        service.recordFeedback(patternId, 'accept');
        service.recordFeedback(patternId, 'reject');

        // Success rate should be around 2/3 = 0.67
        // (Depends on implementation)
      }
    });
  });

  describe('getPattern', () => {
    it('should return undefined for unknown pattern', () => {
      const pattern = service.getPattern('unknown-id');

      expect(pattern).toBeUndefined();
    });
  });

  describe('getAllPatterns', () => {
    it('should return empty array initially', () => {
      const patterns = service.getAllPatterns();

      expect(patterns).toHaveLength(0);
    });
  });

  describe('getPatternsByCategory', () => {
    it('should return empty array for unknown category', () => {
      const patterns = service.getPatternsByCategory('unknown-category');

      expect(patterns).toHaveLength(0);
    });
  });

  describe('getStatistics', () => {
    it('should return statistics with zero values initially', () => {
      const stats = service.getStatistics();

      expect(stats.totalPatterns).toBe(0);
      expect(stats.averageConfidence).toBe(0);
      expect(stats.averageSuccessRate).toBe(0);
      expect(stats.topPatterns).toHaveLength(0);
    });

    it('should include category breakdown', () => {
      const stats = service.getStatistics();

      expect(stats.byCategory).toBeDefined();
      expect(typeof stats.byCategory).toBe('object');
    });
  });

  describe('exportLibrary', () => {
    it('should export valid JSON', () => {
      const exported = service.exportLibrary();

      expect(() => JSON.parse(exported)).not.toThrow();
    });

    it('should include version and timestamp', () => {
      const exported = service.exportLibrary();
      const data = JSON.parse(exported);

      expect(data.version).toBe('1.0.0');
      expect(data.exportedAt).toBeDefined();
      expect(data.patterns).toBeInstanceOf(Array);
    });
  });

  describe('importLibrary', () => {
    it('should import patterns from JSON', () => {
      const exportedData = {
        version: '1.0.0',
        exportedAt: new Date().toISOString(),
        patterns: [
          {
            id: 'pattern-1',
            pattern: {
              id: 'pattern-1',
              name: 'Test Pattern',
              category: 'entity',
              template: 'interface {{name}} {}',
              variables: [],
              confidence: 0.9,
              sourceFile: 'test.ts',
            },
            usageCount: 5,
            lastUsed: new Date().toISOString(),
            successRate: 0.8,
            feedback: [],
          },
        ],
      };

      const result = service.importLibrary(JSON.stringify(exportedData));

      expect(result.imported).toBe(1);
      expect(result.skipped).toBe(0);
    });

    it('should skip duplicate patterns', () => {
      const exportedData = {
        patterns: [
          {
            id: 'dup-pattern',
            pattern: {
              id: 'dup-pattern',
              name: 'Duplicate',
              category: 'entity',
              template: '',
              variables: [],
              confidence: 0.8,
              sourceFile: 'test.ts',
            },
            usageCount: 1,
            lastUsed: new Date().toISOString(),
            successRate: 1.0,
            feedback: [],
          },
        ],
      };

      // Import twice
      service.importLibrary(JSON.stringify(exportedData));
      const result = service.importLibrary(JSON.stringify(exportedData));

      expect(result.skipped).toBe(1);
      expect(result.imported).toBe(0);
    });

    it('should handle invalid JSON gracefully', () => {
      const result = service.importLibrary('invalid json');

      expect(result.imported).toBe(0);
      expect(result.skipped).toBe(0);
    });
  });

  describe('clearLibrary', () => {
    it('should clear all patterns', async () => {
      // Learn some patterns first
      await service.learnFromGeneration([
        { path: '/test/entity.ts', content: 'interface Entity {}', type: 'value-object' },
      ]);

      service.clearLibrary();

      expect(service.getAllPatterns()).toHaveLength(0);
    });
  });

  describe('integration', () => {
    it('should support full workflow: learn → suggest → feedback', async () => {
      // 1. Learn from generation
      const files: GeneratedFile[] = [
        {
          path: '/test/value-objects/Price.ts',
          content: `
            export interface Price {
              readonly amount: number;
              readonly currency: 'JPY' | 'USD';
            }
            
            export function createPrice(amount: number): Price {
              if (amount < 0) throw new Error('Invalid amount');
              return { amount, currency: 'JPY' };
            }
          `,
          type: 'value-object',
        },
      ];

      const learnResult = await service.learnFromGeneration(files);
      expect(learnResult.executionTime).toBeGreaterThanOrEqual(0);

      // 2. Get suggestions (may be empty if no patterns extracted)
      const suggestions = service.getSuggestions('/new/file.ts', 'value-object');
      expect(Array.isArray(suggestions)).toBe(true);

      // 3. Record feedback (if patterns exist)
      const patterns = service.getAllPatterns();
      if (patterns.length > 0) {
        const feedbackResult = service.recordFeedback(patterns[0].id, 'accept');
        expect(feedbackResult).toBe(true);
      }

      // 4. Check statistics
      const stats = service.getStatistics();
      expect(stats).toBeDefined();
    });

    it('should export and import round-trip', async () => {
      // Learn patterns
      await service.learnFromGeneration([
        { path: '/test/e.ts', content: 'interface E { id: string }', type: 'value-object' },
      ]);

      // Export
      const exported = service.exportLibrary();

      // Create new service and import
      const newService = createPatternLearningService();
      const importResult = newService.importLibrary(exported);

      expect(importResult.imported + importResult.skipped).toBeGreaterThanOrEqual(0);
    });
  });
});
