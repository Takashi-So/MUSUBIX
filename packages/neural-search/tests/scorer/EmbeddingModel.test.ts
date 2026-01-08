/**
 * Embedding Model Tests
 * @module @nahisaho/musubix-neural-search
 * Traces to: REQ-NS-001 (分岐スコアリング)
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { EmbeddingModel } from '../../src/scorer/EmbeddingModel.js';
import { EmbeddingError } from '../../src/errors.js';

describe('EmbeddingModel', () => {
  let model: EmbeddingModel;

  beforeEach(() => {
    model = new EmbeddingModel();
  });

  describe('embedCode', () => {
    it('should embed code to fixed dimension', async () => {
      const code = 'function add(a, b) { return a + b; }';
      const embedding = await model.embedCode(code);

      expect(embedding).toBeInstanceOf(Float32Array);
      expect(embedding.length).toBe(128); // Default dimension
    });

    it('should produce normalized embeddings', async () => {
      const code = 'const x = 42;';
      const embedding = await model.embedCode(code);

      // Check L2 norm is approximately 1
      let norm = 0;
      for (let i = 0; i < embedding.length; i++) {
        norm += embedding[i] * embedding[i];
      }
      norm = Math.sqrt(norm);

      expect(norm).toBeCloseTo(1.0, 2);
    });

    it('should throw error for empty code', async () => {
      await expect(model.embedCode('')).rejects.toThrow(EmbeddingError);
      await expect(model.embedCode('')).rejects.toThrow('Code cannot be empty');
    });

    it('should produce deterministic embeddings', async () => {
      const code = 'let sum = 0;';
      const emb1 = await model.embedCode(code);
      const emb2 = await model.embedCode(code);

      for (let i = 0; i < emb1.length; i++) {
        expect(emb1[i]).toBeCloseTo(emb2[i], 10);
      }
    });

    it('should produce different embeddings for different code', async () => {
      const code1 = 'function add(a, b) { return a + b; }';
      const code2 = 'function multiply(x, y) { return x * y; }';

      const emb1 = await model.embedCode(code1);
      const emb2 = await model.embedCode(code2);

      // They should not be identical
      let same = true;
      for (let i = 0; i < emb1.length; i++) {
        if (Math.abs(emb1[i] - emb2[i]) > 0.01) {
          same = false;
          break;
        }
      }
      expect(same).toBe(false);
    });
  });

  describe('embedSpec', () => {
    it('should embed specification', async () => {
      const spec = 'Create a function that adds two numbers';
      const embedding = await model.embedSpec(spec);

      expect(embedding).toBeInstanceOf(Float32Array);
      expect(embedding.length).toBe(128);
    });

    it('should throw error for empty spec', async () => {
      await expect(model.embedSpec('')).rejects.toThrow(EmbeddingError);
    });
  });

  describe('similarity', () => {
    it('should return 1.0 for identical embeddings', async () => {
      const code = 'const x = 1;';
      const emb = await model.embedCode(code);

      const sim = model.similarity(emb, emb);
      expect(sim).toBeCloseTo(1.0, 5);
    });

    it('should return high similarity for similar code', async () => {
      const code1 = 'function add(a, b) { return a + b; }';
      const code2 = 'function add(x, y) { return x + y; }';

      const emb1 = await model.embedCode(code1);
      const emb2 = await model.embedCode(code2);

      const sim = model.similarity(emb1, emb2);
      expect(sim).toBeGreaterThan(0.5);
    });

    it('should return lower similarity for different code', async () => {
      const code1 = 'function add(a, b) { return a + b; }';
      const code2 = 'class Database { constructor() {} }';

      const emb1 = await model.embedCode(code1);
      const emb2 = await model.embedCode(code2);

      const sim = model.similarity(emb1, emb2);
      expect(sim).toBeLessThan(0.9);
    });

    it('should throw error for mismatched dimensions', () => {
      const emb1 = new Float32Array([1, 0]);
      const emb2 = new Float32Array([1, 0, 0]);

      expect(() => model.similarity(emb1, emb2)).toThrow(EmbeddingError);
    });

    it('should handle zero vectors', () => {
      const emb1 = new Float32Array([0, 0, 0]);
      const emb2 = new Float32Array([0, 0, 0]);

      const sim = model.similarity(emb1, emb2);
      expect(sim).toBe(0);
    });
  });

  describe('embedBatch', () => {
    it('should embed multiple texts', async () => {
      const texts = ['code 1', 'code 2', 'code 3'];
      const embeddings = await model.embedBatch(texts);

      expect(embeddings).toHaveLength(3);
      embeddings.forEach((emb) => {
        expect(emb.length).toBe(128);
      });
    });

    it('should handle empty batch', async () => {
      const embeddings = await model.embedBatch([]);
      expect(embeddings).toHaveLength(0);
    });
  });

  describe('configuration', () => {
    it('should use custom dimension', async () => {
      const customModel = new EmbeddingModel({ dimension: 64 });
      const embedding = await customModel.embedCode('test');

      expect(embedding.length).toBe(64);
    });

    it('should return config', () => {
      const config = model.getConfig();

      expect(config.modelName).toBe('simple-hash');
      expect(config.dimension).toBe(128);
      expect(config.maxLength).toBe(512);
      expect(config.poolingStrategy).toBe('mean');
    });
  });
});
