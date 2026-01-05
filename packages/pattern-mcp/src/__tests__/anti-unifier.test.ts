/**
 * @fileoverview Anti-unifier tests
 * @traceability TSK-PATTERN-001
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { AntiUnifier } from '../extractor/anti-unifier.js';
import type { ASTNode } from '../types.js';

describe('AntiUnifier', () => {
  let antiUnifier: AntiUnifier;

  beforeEach(() => {
    antiUnifier = new AntiUnifier();
    antiUnifier.resetCounter();
  });

  const createNode = (
    type: string,
    children: ASTNode[] = [],
    value?: string
  ): ASTNode => ({
    type,
    children,
    value,
    startPosition: { row: 0, column: 0 },
    endPosition: { row: 0, column: 0 },
  });

  describe('antiUnify', () => {
    it('should unify identical nodes', () => {
      const node1 = createNode('Identifier', [], 'x');
      const node2 = createNode('Identifier', [], 'x');

      const result = antiUnifier.antiUnify(node1, node2);

      expect(result.pattern.type).toBe('Identifier');
      expect(result.holes).toHaveLength(0);
    });

    it('should create hole for differing types', () => {
      const node1 = createNode('Identifier', [], 'x');
      const node2 = createNode('NumericLiteral', [], '42');

      const result = antiUnifier.antiUnify(node1, node2);

      expect(result.pattern.type).toBe('Hole');
      expect(result.holes).toHaveLength(1);
    });

    it('should create hole for differing values', () => {
      const node1 = createNode('Identifier', [], 'foo');
      const node2 = createNode('Identifier', [], 'bar');

      const result = antiUnifier.antiUnify(node1, node2);

      expect(result.pattern.type).toBe('Hole');
      expect(result.holes).toHaveLength(1);
    });

    it('should preserve common structure', () => {
      const node1 = createNode('BinaryExpression', [
        createNode('Identifier', [], 'x'),
        createNode('PlusToken'),
        createNode('NumericLiteral', [], '1'),
      ]);
      const node2 = createNode('BinaryExpression', [
        createNode('Identifier', [], 'y'),
        createNode('PlusToken'),
        createNode('NumericLiteral', [], '2'),
      ]);

      const result = antiUnifier.antiUnify(node1, node2);

      expect(result.pattern.type).toBe('BinaryExpression');
      expect(result.pattern.children).toHaveLength(3);
      // First child (identifier) and third child (literal) should be holes
      expect(result.holes.length).toBeGreaterThanOrEqual(2);
    });
  });

  describe('antiUnifyAll', () => {
    it('should handle single node', () => {
      const node = createNode('Identifier', [], 'x');

      const result = antiUnifier.antiUnifyAll([node]);

      expect(result.pattern.type).toBe('Identifier');
      expect(result.holes).toHaveLength(0);
    });

    it('should unify multiple nodes', () => {
      const nodes = [
        createNode('Identifier', [], 'a'),
        createNode('Identifier', [], 'b'),
        createNode('Identifier', [], 'c'),
      ];

      const result = antiUnifier.antiUnifyAll(nodes);

      // All have same type but different values
      expect(result.pattern.type).toBe('Hole');
    });
  });

  describe('calculateSimilarity', () => {
    it('should return 1 for identical structures', () => {
      const node = createNode('Identifier', [], 'x');

      const similarity = antiUnifier.calculateSimilarity(node, node);

      expect(similarity).toBeCloseTo(1, 1);
    });

    it('should return lower score for different structures', () => {
      const node1 = createNode('Identifier', [], 'x');
      const node2 = createNode('BinaryExpression', [
        createNode('Identifier'),
        createNode('PlusToken'),
        createNode('NumericLiteral'),
      ]);

      const similarity = antiUnifier.calculateSimilarity(node1, node2);

      expect(similarity).toBeLessThan(0.5);
    });

    it('should return high score for similar structures', () => {
      const node1 = createNode('BinaryExpression', [
        createNode('Identifier', [], 'x'),
        createNode('PlusToken'),
        createNode('NumericLiteral', [], '1'),
      ]);
      const node2 = createNode('BinaryExpression', [
        createNode('Identifier', [], 'y'),
        createNode('PlusToken'),
        createNode('NumericLiteral', [], '2'),
      ]);

      const similarity = antiUnifier.calculateSimilarity(node1, node2);

      expect(similarity).toBeGreaterThan(0.3);
    });
  });
});
