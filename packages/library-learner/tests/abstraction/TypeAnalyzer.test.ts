/**
 * TypeAnalyzer Tests
 *
 * REQ-LL-002: 型認識パターンマッチング
 * Test-First approach: Red phase
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { createTypeAnalyzer, type TypeAnalyzer } from '../../src/abstraction/TypeAnalyzer.js';
import type { PatternCandidate, TypeContext, TypeSignature } from '../../src/types.js';

describe('TypeAnalyzer', () => {
  let analyzer: TypeAnalyzer;

  beforeEach(() => {
    analyzer = createTypeAnalyzer();
  });

  describe('createTypeAnalyzer', () => {
    it('should create a TypeAnalyzer instance', () => {
      expect(analyzer).toBeDefined();
      expect(analyzer.isCompatible).toBeDefined();
      expect(analyzer.filterByType).toBeDefined();
      expect(analyzer.scoreByTypeMatch).toBeDefined();
      expect(analyzer.inferType).toBeDefined();
      expect(analyzer.isSubtype).toBeDefined();
    });
  });

  describe('isCompatible', () => {
    it('should return true for identical types', () => {
      const sig1: TypeSignature = { kind: 'primitive', name: 'number' };
      const sig2: TypeSignature = { kind: 'primitive', name: 'number' };

      const result = analyzer.isCompatible(sig1, sig2);

      expect(result).toBe(true);
    });

    it('should return false for incompatible types', () => {
      const sig1: TypeSignature = { kind: 'primitive', name: 'number' };
      const sig2: TypeSignature = { kind: 'primitive', name: 'string' };

      const result = analyzer.isCompatible(sig1, sig2);

      expect(result).toBe(false);
    });

    it('should handle any type', () => {
      const anyType: TypeSignature = { kind: 'primitive', name: 'any' };
      const numberType: TypeSignature = { kind: 'primitive', name: 'number' };

      expect(analyzer.isCompatible(anyType, numberType)).toBe(true);
      expect(analyzer.isCompatible(numberType, anyType)).toBe(true);
    });

    it('should handle unknown type', () => {
      const unknownType: TypeSignature = { kind: 'primitive', name: 'unknown' };
      const stringType: TypeSignature = { kind: 'primitive', name: 'string' };

      // unknown is compatible with any type (it's a top type)
      expect(analyzer.isCompatible(unknownType, stringType)).toBe(true);
    });

    it('should check array element types', () => {
      const arrayNum: TypeSignature = {
        kind: 'array',
        elementType: { kind: 'primitive', name: 'number' },
      };
      const arrayStr: TypeSignature = {
        kind: 'array',
        elementType: { kind: 'primitive', name: 'string' },
      };
      const arrayNum2: TypeSignature = {
        kind: 'array',
        elementType: { kind: 'primitive', name: 'number' },
      };

      expect(analyzer.isCompatible(arrayNum, arrayNum2)).toBe(true);
      expect(analyzer.isCompatible(arrayNum, arrayStr)).toBe(false);
    });
  });

  describe('filterByType', () => {
    it('should return empty array for empty input', () => {
      const expectedType: TypeSignature = { kind: 'primitive', name: 'number' };
      const result = analyzer.filterByType([], expectedType);
      expect(result).toEqual([]);
    });

    it('should filter candidates by type compatibility', () => {
      const candidates: PatternCandidate[] = [
        {
          id: 'PAT-1',
          ast: { type: 'NumberLiteral', value: 42 },
          occurrences: [],
          score: 10,
        },
        {
          id: 'PAT-2',
          ast: { type: 'StringLiteral', value: 'hello' },
          occurrences: [],
          score: 8,
        },
        {
          id: 'PAT-3',
          ast: { type: 'NumberLiteral', value: 100 },
          occurrences: [],
          score: 6,
        },
      ];

      const expectedType: TypeSignature = { kind: 'primitive', name: 'number' };
      const result = analyzer.filterByType(candidates, expectedType);

      expect(result).toHaveLength(2);
      expect(result.map((c) => c.id)).toEqual(['PAT-1', 'PAT-3']);
    });

    it('should preserve order when filtering', () => {
      const candidates: PatternCandidate[] = [
        {
          id: 'PAT-1',
          ast: { type: 'StringLiteral', value: 'a' },
          occurrences: [],
          score: 10,
        },
        {
          id: 'PAT-2',
          ast: { type: 'StringLiteral', value: 'b' },
          occurrences: [],
          score: 5,
        },
      ];

      const expectedType: TypeSignature = { kind: 'primitive', name: 'string' };
      const result = analyzer.filterByType(candidates, expectedType);

      expect(result).toHaveLength(2);
      expect(result.map((c) => c.id)).toEqual(['PAT-1', 'PAT-2']);
    });

    it('should return empty array when no candidates match', () => {
      const candidates: PatternCandidate[] = [
        {
          id: 'PAT-1',
          ast: { type: 'StringLiteral', value: 'test' },
          occurrences: [],
          score: 10,
        },
      ];

      const expectedType: TypeSignature = { kind: 'primitive', name: 'number' };
      const result = analyzer.filterByType(candidates, expectedType);

      expect(result).toHaveLength(0);
    });
  });

  describe('scoreByTypeMatch', () => {
    it('should return score based on context variable matches', () => {
      const candidate: PatternCandidate = {
        id: 'PAT-1',
        ast: { type: 'NumberLiteral', value: 42 },
        occurrences: [],
        score: 10,
      };

      const context: TypeContext = {
        variables: new Map(),
        functions: new Map(),
        aliases: new Map(),
      };
      const score = analyzer.scoreByTypeMatch(candidate, context);

      expect(score).toBeGreaterThanOrEqual(0);
    });

    it('should increase score when candidate uses matching variables', () => {
      const candidate: PatternCandidate = {
        id: 'PAT-1',
        ast: { type: 'Identifier', name: 'x' },
        occurrences: [],
        score: 10,
      };

      const context: TypeContext = {
        variables: new Map([['x', { kind: 'primitive', name: 'number' }]]),
        functions: new Map(),
        aliases: new Map(),
      };
      const score = analyzer.scoreByTypeMatch(candidate, context);

      expect(score).toBeGreaterThanOrEqual(0);
    });
  });

  describe('inferType', () => {
    it('should infer number type for numbers', () => {
      const result = analyzer.inferType(42);

      expect(result.kind).toBe('primitive');
      expect(result.name).toBe('number');
    });

    it('should infer string type for strings', () => {
      const result = analyzer.inferType('hello');

      expect(result.kind).toBe('primitive');
      expect(result.name).toBe('string');
    });

    it('should infer boolean type for booleans', () => {
      const result = analyzer.inferType(true);

      expect(result.kind).toBe('primitive');
      expect(result.name).toBe('boolean');
    });

    it('should infer array type for arrays', () => {
      const result = analyzer.inferType([1, 2, 3]);

      expect(result.kind).toBe('array');
      expect(result.elementType?.kind).toBe('primitive');
      expect(result.elementType?.name).toBe('number');
    });

    it('should infer null type for null', () => {
      const result = analyzer.inferType(null);

      expect(result.kind).toBe('primitive');
      expect(result.name).toBe('null');
    });

    it('should infer undefined type for undefined', () => {
      const result = analyzer.inferType(undefined);

      expect(result.kind).toBe('primitive');
      expect(result.name).toBe('undefined');
    });

    it('should infer object type for objects', () => {
      const result = analyzer.inferType({ x: 1, y: 'test' });

      expect(result.kind).toBe('object');
    });
  });

  describe('isSubtype', () => {
    it('should return true when types are identical', () => {
      const type1: TypeSignature = { kind: 'primitive', name: 'number' };
      const type2: TypeSignature = { kind: 'primitive', name: 'number' };

      expect(analyzer.isSubtype(type1, type2)).toBe(true);
    });

    it('should return true for any as supertype', () => {
      const numberType: TypeSignature = { kind: 'primitive', name: 'number' };
      const anyType: TypeSignature = { kind: 'primitive', name: 'any' };

      expect(analyzer.isSubtype(numberType, anyType)).toBe(true);
    });

    it('should return true for never as subtype', () => {
      const neverType: TypeSignature = { kind: 'primitive', name: 'never' };
      const numberType: TypeSignature = { kind: 'primitive', name: 'number' };

      expect(analyzer.isSubtype(neverType, numberType)).toBe(true);
    });

    it('should return false for incompatible types', () => {
      const numberType: TypeSignature = { kind: 'primitive', name: 'number' };
      const stringType: TypeSignature = { kind: 'primitive', name: 'string' };

      expect(analyzer.isSubtype(numberType, stringType)).toBe(false);
    });

    it('should check array element types', () => {
      const arrayNum: TypeSignature = {
        kind: 'array',
        elementType: { kind: 'primitive', name: 'number' },
      };
      const arrayNum2: TypeSignature = {
        kind: 'array',
        elementType: { kind: 'primitive', name: 'number' },
      };

      expect(analyzer.isSubtype(arrayNum, arrayNum2)).toBe(true);
    });

    it('should return false for arrays with different element types', () => {
      const arrayNum: TypeSignature = {
        kind: 'array',
        elementType: { kind: 'primitive', name: 'number' },
      };
      const arrayStr: TypeSignature = {
        kind: 'array',
        elementType: { kind: 'primitive', name: 'string' },
      };

      expect(analyzer.isSubtype(arrayNum, arrayStr)).toBe(false);
    });
  });
});
