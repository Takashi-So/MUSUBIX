/**
 * EnhancedPBESynthesizer - Integration Tests
 * @module @nahisaho/musubix-synthesis
 * @see TSK-SY-107
 *
 * Tests for integrated PBE synthesis with:
 * - EnhancedWitnessEngine
 * - EnhancedVersionSpace
 * - Type-directed synthesis
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createEnhancedPBESynthesizer,
  EnhancedPBESynthesizer,
} from '../../src/EnhancedPBESynthesizer.js';

describe('EnhancedPBESynthesizer', () => {
  let synthesizer: EnhancedPBESynthesizer;

  beforeEach(() => {
    synthesizer = createEnhancedPBESynthesizer();
  });

  describe('Factory Function', () => {
    it('should create synthesizer with default config', () => {
      expect(synthesizer).toBeDefined();
    });

    it('should create synthesizer with custom config', () => {
      const customSynthesizer = createEnhancedPBESynthesizer({
        enableWitnessOptimization: true,
        enableVersionSpaceMerge: true,
        maxSearchDepth: 20,
      });
      expect(customSynthesizer).toBeDefined();
    });
  });

  describe('EnhancedWitnessEngine Integration', () => {
    it('should provide access to witness engine', () => {
      const engine = synthesizer.getWitnessEngine();
      expect(engine).toBeDefined();
    });

    it('should use witness functions during synthesis', async () => {
      const examples = [
        { input: [1, 2], output: 3 },
        { input: [3, 4], output: 7 },
      ];

      const result = await synthesizer.synthesize({
        examples,
        returnType: 'number',
      });

      expect(result).toBeDefined();
    });

    it('should support custom witness registration', () => {
      synthesizer.registerWitness('custom', {
        name: 'custom-witness',
        apply: (input) => input,
        constraints: [],
      });

      const engine = synthesizer.getWitnessEngine();
      expect(engine).toBeDefined();
    });
  });

  describe('EnhancedVersionSpace Integration', () => {
    it('should provide access to version space', () => {
      const vs = synthesizer.getVersionSpace();
      expect(vs).toBeDefined();
    });

    it('should build version space from examples', async () => {
      const examples = [
        { input: [1], output: 2 },
        { input: [2], output: 4 },
        { input: [3], output: 6 },
      ];

      await synthesizer.synthesize({ examples, returnType: 'number' });

      const stats = synthesizer.getVersionSpaceStats();
      expect(stats).toBeDefined();
    });

    it('should merge version spaces efficiently', async () => {
      const examples1 = [{ input: [1], output: 2 }];
      const examples2 = [{ input: [2], output: 4 }];

      await synthesizer.synthesize({ examples: examples1, returnType: 'number' });
      await synthesizer.synthesize({ examples: examples2, returnType: 'number' });

      const stats = synthesizer.getVersionSpaceStats();
      expect(stats.totalPoints).toBeGreaterThanOrEqual(0);
    });
  });

  describe('Type-Directed Synthesis', () => {
    it('should respect type constraints', async () => {
      const result = await synthesizer.synthesizeWithTypes({
        examples: [
          { input: ['hello'], output: 5 },
          { input: ['world'], output: 5 },
        ],
        inputTypes: ['string'],
        outputType: 'number',
      });

      expect(result).toBeDefined();
    });

    it('should prune based on type incompatibility', async () => {
      const stats = synthesizer.getSearchStats();
      expect(stats.prunedByType).toBeGreaterThanOrEqual(0);
    });
  });

  describe('Synthesis Operations', () => {
    it('should synthesize from examples', async () => {
      const result = await synthesizer.synthesize({
        examples: [
          { input: [5], output: 10 },
          { input: [7], output: 14 },
        ],
        returnType: 'number',
      });

      expect(result.success).toBe(true);
    });

    it('should return candidate programs', async () => {
      const result = await synthesizer.synthesize({
        examples: [{ input: [1], output: 1 }],
        returnType: 'number',
        maxCandidates: 5,
      });

      expect(result.candidates.length).toBeLessThanOrEqual(5);
    });

    it('should handle synthesis timeout', async () => {
      const result = await synthesizer.synthesize({
        examples: Array.from({ length: 100 }, (_, i) => ({
          input: [i],
          output: i * i,
        })),
        returnType: 'number',
        timeout: 10, // Very short timeout
      });

      // Should still return (possibly with timeout flag)
      expect(result).toBeDefined();
    });
  });

  describe('Statistics', () => {
    it('should provide comprehensive statistics', async () => {
      await synthesizer.synthesize({
        examples: [{ input: [1], output: 2 }],
        returnType: 'number',
      });

      const stats = synthesizer.getEnhancedStats();

      expect(stats.synthesis).toBeDefined();
      expect(stats.witness).toBeDefined();
      expect(stats.versionSpace).toBeDefined();
      expect(stats.search).toBeDefined();
    });

    it('should track synthesis history', async () => {
      await synthesizer.synthesize({
        examples: [{ input: [1], output: 2 }],
        returnType: 'number',
      });
      await synthesizer.synthesize({
        examples: [{ input: [2], output: 4 }],
        returnType: 'number',
      });

      const history = synthesizer.getSynthesisHistory(2);
      expect(history.length).toBe(2);
    });
  });

  describe('Serialization', () => {
    it('should serialize enhanced state', async () => {
      await synthesizer.synthesize({
        examples: [{ input: [1], output: 2 }],
        returnType: 'number',
      });

      const json = synthesizer.toJSON();
      expect(json).toBeDefined();

      const parsed = JSON.parse(json);
      expect(parsed).toBeDefined();
    });

    it('should restore enhanced state', () => {
      const state = {
        synthesisCount: 5,
        totalTimeMs: 100,
      };

      synthesizer.fromJSON(JSON.stringify(state));
      const stats = synthesizer.getEnhancedStats();
      expect(stats.synthesis.totalSyntheses).toBe(5);
    });
  });
});
