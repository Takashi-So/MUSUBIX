/**
 * ModalFusion Tests
 * @module @nahisaho/musubix-neural-search
 * @see TSK-NS-106
 * @see DES-NS-106
 * @see REQ-NS-106
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createModalFusion,
  type ModalFusion,
  type FusionStrategy,
} from '../../src/fusion/ModalFusion.js';
import type { Embedding } from '../../src/types.js';

describe('ModalFusion', () => {
  let fusion: ModalFusion;

  const textEmbedding: Embedding = new Array(64).fill(0.1);
  const codeEmbedding: Embedding = new Array(64).fill(0.2);

  beforeEach(() => {
    fusion = createModalFusion();
  });

  describe('Factory Function', () => {
    it('should create a ModalFusion instance', () => {
      const instance = createModalFusion();
      expect(instance).toBeDefined();
      expect(typeof instance.fuse).toBe('function');
    });

    it('should create with custom config', () => {
      const instance = createModalFusion({
        defaultStrategy: 'attention',
        textWeight: 0.6,
        codeWeight: 0.4,
      });
      expect(instance).toBeDefined();
    });
  });

  describe('Concat Strategy', () => {
    it('should concatenate embeddings', () => {
      const result = fusion.fuse(textEmbedding, codeEmbedding, 'concat');

      expect(result).toBeDefined();
      expect(result.length).toBe(textEmbedding.length + codeEmbedding.length);
    });

    it('should preserve original values in concat', () => {
      const result = fusion.fuse(textEmbedding, codeEmbedding, 'concat');

      // First half should be text embedding
      expect(result.slice(0, textEmbedding.length)).toEqual(textEmbedding);
      // Second half should be code embedding
      expect(result.slice(textEmbedding.length)).toEqual(codeEmbedding);
    });
  });

  describe('Weighted Sum Strategy', () => {
    it('should compute weighted sum', () => {
      const result = fusion.fuse(textEmbedding, codeEmbedding, 'weighted_sum');

      expect(result).toBeDefined();
      expect(result.length).toBe(textEmbedding.length);
    });

    it('should apply default weights (0.5/0.5)', () => {
      const equalWeightFusion = createModalFusion({
        textWeight: 0.5,
        codeWeight: 0.5,
      });

      const result = equalWeightFusion.fuse(
        textEmbedding,
        codeEmbedding,
        'weighted_sum'
      );

      // Result should be average: (0.1 + 0.2) / 2 = 0.15
      expect(result[0]).toBeCloseTo(0.15, 5);
    });

    it('should apply custom weights', () => {
      const customFusion = createModalFusion({
        textWeight: 0.7,
        codeWeight: 0.3,
      });

      const result = customFusion.fuse(
        textEmbedding,
        codeEmbedding,
        'weighted_sum'
      );

      // Result should be: 0.1 * 0.7 + 0.2 * 0.3 = 0.07 + 0.06 = 0.13
      expect(result[0]).toBeCloseTo(0.13, 5);
    });
  });

  describe('Attention Strategy', () => {
    it('should apply attention-based fusion', () => {
      const result = fusion.fuse(textEmbedding, codeEmbedding, 'attention');

      expect(result).toBeDefined();
      expect(result.length).toBe(textEmbedding.length);
    });

    it('should produce valid embedding values', () => {
      const result = fusion.fuse(textEmbedding, codeEmbedding, 'attention');

      for (const val of result) {
        expect(typeof val).toBe('number');
        expect(isNaN(val)).toBe(false);
      }
    });
  });

  describe('Default Strategy', () => {
    it('should use default strategy when not specified', () => {
      const result = fusion.fuse(textEmbedding, codeEmbedding);

      expect(result).toBeDefined();
      expect(result.length).toBeGreaterThan(0);
    });

    it('should respect configured default strategy', () => {
      const concatFusion = createModalFusion({ defaultStrategy: 'concat' });
      const result = concatFusion.fuse(textEmbedding, codeEmbedding);

      expect(result.length).toBe(textEmbedding.length + codeEmbedding.length);
    });
  });

  describe('Edge Cases', () => {
    it('should handle empty embeddings', () => {
      const empty: Embedding = [];
      const result = fusion.fuse(empty, empty, 'concat');

      expect(result).toEqual([]);
    });

    it('should handle different length embeddings in concat', () => {
      const short: Embedding = [0.1, 0.2];
      const long: Embedding = [0.3, 0.4, 0.5, 0.6];

      const result = fusion.fuse(short, long, 'concat');
      expect(result.length).toBe(short.length + long.length);
    });

    it('should handle different length embeddings in weighted_sum', () => {
      const short: Embedding = [0.1, 0.2];
      const long: Embedding = [0.3, 0.4, 0.5, 0.6];

      // Should use minimum length
      const result = fusion.fuse(short, long, 'weighted_sum');
      expect(result.length).toBe(Math.min(short.length, long.length));
    });
  });

  describe('Batch Operations', () => {
    it('should fuse multiple pairs', () => {
      const pairs = [
        { text: textEmbedding, code: codeEmbedding },
        { text: codeEmbedding, code: textEmbedding },
      ];

      const results = fusion.fuseBatch(pairs, 'weighted_sum');

      expect(results).toHaveLength(2);
      expect(results[0].length).toBe(textEmbedding.length);
    });
  });

  describe('Strategy Info', () => {
    it('should list available strategies', () => {
      const strategies = fusion.getAvailableStrategies();

      expect(strategies).toContain('concat');
      expect(strategies).toContain('weighted_sum');
      expect(strategies).toContain('attention');
      expect(strategies.length).toBe(3);
    });

    it('should get current config', () => {
      const config = fusion.getConfig();

      expect(config.defaultStrategy).toBeDefined();
      expect(typeof config.textWeight).toBe('number');
      expect(typeof config.codeWeight).toBe('number');
    });
  });

  describe('Serialization', () => {
    it('should serialize to JSON', () => {
      const json = fusion.toJSON();
      expect(typeof json).toBe('string');

      const parsed = JSON.parse(json);
      expect(parsed.config).toBeDefined();
    });

    it('should deserialize from JSON', () => {
      const json = JSON.stringify({
        config: {
          defaultStrategy: 'attention',
          textWeight: 0.6,
          codeWeight: 0.4,
        },
      });

      expect(() => fusion.fromJSON(json)).not.toThrow();

      const config = fusion.getConfig();
      expect(config.defaultStrategy).toBe('attention');
      expect(config.textWeight).toBe(0.6);
    });
  });
});
