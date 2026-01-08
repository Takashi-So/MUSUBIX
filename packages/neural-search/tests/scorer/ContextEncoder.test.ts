/**
 * Context Encoder Tests
 * @module @nahisaho/musubix-neural-search
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { ContextEncoder } from '../../src/scorer/ContextEncoder.js';
import { EmbeddingModel } from '../../src/scorer/EmbeddingModel.js';
import type { SearchContext, SearchState } from '../../src/types.js';

describe('ContextEncoder', () => {
  let encoder: ContextEncoder;
  let embeddingModel: EmbeddingModel;

  beforeEach(() => {
    embeddingModel = new EmbeddingModel();
    encoder = new ContextEncoder(embeddingModel);
  });

  // Helper to create context
  async function createContext(
    spec: string,
    constraints: string[] = [],
    history: SearchState[] = []
  ): Promise<SearchContext> {
    const specEmbedding = await embeddingModel.embedSpec(spec);
    return {
      specification: spec,
      specEmbedding,
      constraints,
      history,
    };
  }

  describe('encode', () => {
    it('should encode search context', async () => {
      const context = await createContext('Create a function that adds numbers');

      const encoded = await encoder.encode(context);

      expect(encoded.embedding).toBeDefined();
      expect(encoded.embedding.length).toBe(128);
      expect(encoded.features).toBeDefined();
      expect(encoded.tokens).toBeGreaterThan(0);
    });

    it('should include constraints in encoding', async () => {
      const context = await createContext(
        'Create a function',
        ['Must be pure', 'No side effects']
      );

      const encoded = await encoder.encode(context);

      expect(encoded.features.constraintCount).toBe(2);
    });

    it('should consider history in encoding', async () => {
      const history: SearchState[] = [
        { id: 's1', code: 'const x = 1;', depth: 1, metadata: {} },
        { id: 's2', code: 'const y = 2;', depth: 2, metadata: {} },
      ];
      const context = await createContext('Create a function', [], history);

      const encoded = await encoder.encode(context);

      expect(encoded.features.complexityEstimate).toBeGreaterThan(0);
    });
  });

  describe('encodeSpec', () => {
    it('should encode specification only', async () => {
      const encoded = await encoder.encodeSpec('Create a class that manages users');

      expect(encoded.embedding).toBeDefined();
      expect(encoded.embedding.length).toBe(128);
      expect(encoded.features.specLength).toBeGreaterThan(0);
    });

    it('should estimate tokens', async () => {
      const shortSpec = 'Short';
      const longSpec = 'This is a much longer specification that should have more tokens';

      const shortEncoded = await encoder.encodeSpec(shortSpec);
      const longEncoded = await encoder.encodeSpec(longSpec);

      expect(longEncoded.tokens).toBeGreaterThan(shortEncoded.tokens);
    });
  });

  describe('features', () => {
    it('should extract spec length', async () => {
      const spec = 'Create a function';
      const encoded = await encoder.encodeSpec(spec);

      expect(encoded.features.specLength).toBe(spec.length);
    });

    it('should detect domain signals', async () => {
      const encoded = await encoder.encodeSpec(
        'Create an async function that queries the database API'
      );

      expect(encoded.features.domainSignals).toContain('function');
      expect(encoded.features.domainSignals).toContain('async');
      expect(encoded.features.domainSignals).toContain('database');
      expect(encoded.features.domainSignals).toContain('api');
    });

    it('should detect OOP signals', async () => {
      const encoded = await encoder.encodeSpec('Create a class with an interface');

      expect(encoded.features.domainSignals).toContain('oop');
    });

    it('should detect testing signals', async () => {
      const encoded = await encoder.encodeSpec('Write a test spec for the component');

      expect(encoded.features.domainSignals).toContain('testing');
    });

    it('should estimate complexity', async () => {
      const simpleContext = await createContext('Simple');
      const complexContext = await createContext(
        'Complex specification with many requirements and detailed explanations',
        ['Constraint 1', 'Constraint 2', 'Constraint 3'],
        [
          { id: 's1', code: 'code', depth: 1, metadata: {} },
          { id: 's2', code: 'code', depth: 2, metadata: {} },
        ]
      );

      const simpleEncoded = await encoder.encode(simpleContext);
      const complexEncoded = await encoder.encode(complexContext);

      expect(complexEncoded.features.complexityEstimate).toBeGreaterThan(
        simpleEncoded.features.complexityEstimate
      );
    });
  });

  describe('patterns', () => {
    it('should update patterns', () => {
      encoder.updatePatterns(['Repository', 'Factory', 'Service']);

      const patterns = encoder.getPatterns();
      expect(patterns).toContain('Repository');
      expect(patterns).toContain('Factory');
      expect(patterns).toContain('Service');
    });

    it('should detect learned patterns in spec', async () => {
      encoder.updatePatterns(['Repository']);

      const encoded = await encoder.encodeSpec('Create a UserRepository for data access');

      expect(encoded.features.domainSignals).toContain('pattern:Repository');
    });

    it('should not duplicate patterns', () => {
      encoder.updatePatterns(['Pattern']);
      encoder.updatePatterns(['Pattern']);

      const patterns = encoder.getPatterns();
      expect(patterns.filter((p) => p === 'Pattern')).toHaveLength(1);
    });
  });
});
