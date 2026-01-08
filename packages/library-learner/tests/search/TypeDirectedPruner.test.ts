/**
 * TypeDirectedPruner Unit Tests
 *
 * @module @nahisaho/musubix-library-learner
 * @see TSK-LL-102
 * @see DES-LL-102
 * @see REQ-LL-102
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import {
  TypeDirectedPruner,
  createTypeDirectedPruner,
  DefaultTypeDirectedPruner,
  type PruneResult,
  type PruneCandidate,
  type TypeDirectedPrunerConfig,
} from '../../src/search/TypeDirectedPruner.js';
import type { ASTNode } from '../../src/types.js';

describe('TypeDirectedPruner', () => {
  let pruner: TypeDirectedPruner;

  beforeEach(() => {
    pruner = createTypeDirectedPruner();
  });

  // ==========================================================================
  // Interface Tests
  // ==========================================================================

  describe('createTypeDirectedPruner', () => {
    it('should create a TypeDirectedPruner instance', () => {
      expect(pruner).toBeDefined();
      expect(pruner).toBeInstanceOf(DefaultTypeDirectedPruner);
    });

    it('should accept custom configuration', () => {
      const customPruner = createTypeDirectedPruner({
        maxCandidates: 500,
        typeWeight: 0.8,
      });
      expect(customPruner).toBeDefined();
    });
  });

  // ==========================================================================
  // prune Tests
  // ==========================================================================

  describe('prune', () => {
    it('should reduce search space by at least 70%', async () => {
      const candidates = generateCandidates(100);
      const targetType = { kind: 'function', params: ['number'], returns: 'number' };

      const result = await pruner.prune(candidates, targetType);

      // 100 candidates -> at most 30 remaining (70% reduction)
      expect(result.candidates.length).toBeLessThanOrEqual(30);
      expect(result.reductionRatio).toBeGreaterThanOrEqual(0.7);
    });

    it('should preserve type-compatible candidates', async () => {
      const candidates: PruneCandidate[] = [
        {
          id: 'add',
          ast: mockAST('function', ['number', 'number'], 'number'),
          typeSignature: { kind: 'function', params: ['number', 'number'], returns: 'number' },
          score: 0.9,
        },
        {
          id: 'concat',
          ast: mockAST('function', ['string', 'string'], 'string'),
          typeSignature: { kind: 'function', params: ['string', 'string'], returns: 'string' },
          score: 0.8,
        },
      ];
      const targetType = { kind: 'function', params: ['number', 'number'], returns: 'number' };

      const result = await pruner.prune(candidates, targetType);

      expect(result.candidates.some((c) => c.id === 'add')).toBe(true);
    });

    it('should guarantee 100% type safety', async () => {
      const candidates: PruneCandidate[] = [
        {
          id: 'incompatible',
          ast: mockAST('function', ['string'], 'boolean'),
          typeSignature: { kind: 'function', params: ['string'], returns: 'boolean' },
          score: 0.95,
        },
      ];
      const targetType = { kind: 'function', params: ['number'], returns: 'number' };

      const result = await pruner.prune(candidates, targetType);

      // All returned candidates must be type-compatible
      for (const candidate of result.candidates) {
        expect(pruner.isTypeCompatible(candidate.typeSignature, targetType)).toBe(true);
      }
    });

    it('should score candidates based on type similarity', async () => {
      const candidates: PruneCandidate[] = [
        {
          id: 'exact',
          ast: mockAST('function', ['number'], 'number'),
          typeSignature: { kind: 'function', params: ['number'], returns: 'number' },
          score: 0.5,
        },
        {
          id: 'partial',
          ast: mockAST('function', ['number'], 'any'),
          typeSignature: { kind: 'function', params: ['number'], returns: 'any' },
          score: 0.5,
        },
      ];
      const targetType = { kind: 'function', params: ['number'], returns: 'number' };

      const result = await pruner.prune(candidates, targetType);

      // Exact match should have higher final score
      const exactCandidate = result.candidates.find((c) => c.id === 'exact');
      const partialCandidate = result.candidates.find((c) => c.id === 'partial');

      if (exactCandidate && partialCandidate) {
        expect(exactCandidate.finalScore).toBeGreaterThan(partialCandidate.finalScore);
      }
    });
  });

  // ==========================================================================
  // isTypeCompatible Tests
  // ==========================================================================

  describe('isTypeCompatible', () => {
    it('should return true for exact match', () => {
      const type1 = { kind: 'function', params: ['number'], returns: 'number' };
      const type2 = { kind: 'function', params: ['number'], returns: 'number' };
      expect(pruner.isTypeCompatible(type1, type2)).toBe(true);
    });

    it('should return true for any type', () => {
      const type1 = { kind: 'any' };
      const type2 = { kind: 'function', params: ['number'], returns: 'number' };
      expect(pruner.isTypeCompatible(type1, type2)).toBe(true);
    });

    it('should return false for incompatible types', () => {
      const type1 = { kind: 'function', params: ['string'], returns: 'string' };
      const type2 = { kind: 'function', params: ['number'], returns: 'number' };
      expect(pruner.isTypeCompatible(type1, type2)).toBe(false);
    });

    it('should handle generic types', () => {
      const type1 = { kind: 'function', params: ['T'], returns: 'T' };
      const type2 = { kind: 'function', params: ['number'], returns: 'number' };
      expect(pruner.isTypeCompatible(type1, type2)).toBe(true);
    });
  });

  // ==========================================================================
  // calculateTypeScore Tests
  // ==========================================================================

  describe('calculateTypeScore', () => {
    it('should return 1.0 for exact match', () => {
      const type1 = { kind: 'function', params: ['number'], returns: 'number' };
      const type2 = { kind: 'function', params: ['number'], returns: 'number' };
      expect(pruner.calculateTypeScore(type1, type2)).toBe(1.0);
    });

    it('should return lower score for partial match', () => {
      const type1 = { kind: 'function', params: ['number'], returns: 'any' };
      const type2 = { kind: 'function', params: ['number'], returns: 'number' };
      const score = pruner.calculateTypeScore(type1, type2);
      expect(score).toBeGreaterThan(0);
      expect(score).toBeLessThan(1.0);
    });

    it('should return 0 for completely incompatible types', () => {
      const type1 = { kind: 'string' };
      const type2 = { kind: 'function', params: ['number'], returns: 'number' };
      expect(pruner.calculateTypeScore(type1, type2)).toBe(0);
    });
  });

  // ==========================================================================
  // Performance Tests
  // ==========================================================================

  describe('performance', () => {
    it('should process 1000 candidates in under 100ms', async () => {
      const candidates = generateCandidates(1000);
      const targetType = { kind: 'function', params: ['number'], returns: 'number' };

      const startTime = Date.now();
      await pruner.prune(candidates, targetType);
      const elapsed = Date.now() - startTime;

      expect(elapsed).toBeLessThan(100);
    });
  });

  // ==========================================================================
  // Integration Tests
  // ==========================================================================

  describe('integration with search', () => {
    it('should work with synthesis pipeline', async () => {
      const candidates = generateCandidates(50);
      const targetType = { kind: 'function', params: ['number', 'number'], returns: 'number' };

      const result = await pruner.prune(candidates, targetType);

      expect(result.candidates).toBeDefined();
      expect(result.reductionRatio).toBeGreaterThanOrEqual(0);
      expect(result.prunedCount).toBe(candidates.length - result.candidates.length);
    });
  });
});

// =============================================================================
// Test Helpers
// =============================================================================

function generateCandidates(count: number): PruneCandidate[] {
  const types = ['number', 'string', 'boolean', 'any'];
  const candidates: PruneCandidate[] = [];

  for (let i = 0; i < count; i++) {
    const paramType = types[i % types.length];
    const returnType = types[(i + 1) % types.length];

    candidates.push({
      id: `candidate-${i}`,
      ast: mockAST('function', [paramType], returnType),
      typeSignature: { kind: 'function', params: [paramType], returns: returnType },
      score: Math.random(),
    });
  }

  return candidates;
}

function mockAST(kind: string, params: string[], returns: string): ASTNode {
  return {
    type: kind,
    params: params.map((p) => ({ type: 'Parameter', name: p })),
    returns: { type: 'ReturnType', name: returns },
  } as unknown as ASTNode;
}
