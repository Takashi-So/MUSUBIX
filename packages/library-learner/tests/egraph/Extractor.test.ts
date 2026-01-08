/**
 * Extractor Tests
 *
 * REQ-LL-004: E-graph最適化
 * Test-First approach
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { createExtractor, type Extractor } from '../../src/egraph/Extractor.js';
import { createEGraph, type EGraph } from '../../src/egraph/EGraph.js';
import type { CostFunction, ENode } from '../../src/types.js';

describe('Extractor', () => {
  let extractor: Extractor;
  let egraph: EGraph;

  const simpleCostFn: CostFunction = (node: ENode, _childCosts: number[]) => {
    // Simple cost: length of operator name
    return node.op.length;
  };

  beforeEach(() => {
    extractor = createExtractor();
    egraph = createEGraph();
  });

  describe('createExtractor', () => {
    it('should create an Extractor instance', () => {
      expect(extractor).toBeDefined();
      expect(extractor.extract).toBeDefined();
      expect(extractor.extractFromClass).toBeDefined();
    });
  });

  describe('extract', () => {
    it('should return empty result for empty e-graph', () => {
      const result = extractor.extract(egraph, simpleCostFn);

      expect(result).toBeDefined();
      expect(result.cost).toBe(Infinity);
    });

    it('should extract optimal expression from e-graph', () => {
      egraph.add({ op: 'x', children: [] });

      const result = extractor.extract(egraph, simpleCostFn);

      expect(result).toBeDefined();
      expect(result.ast).toBeDefined();
      expect(result.cost).toBeLessThan(Infinity);
    });

    it('should select lowest cost node', () => {
      const id1 = egraph.add({ op: 'long_operator', children: [] });
      const id2 = egraph.add({ op: 'x', children: [] });
      egraph.merge(id1, id2);

      const result = extractor.extractFromClass(egraph, id1, simpleCostFn);

      expect(result.ast.type).toBe('x');
      expect(result.cost).toBe(1);
    });
  });

  describe('extractFromClass', () => {
    it('should extract from specific e-class', () => {
      const id = egraph.add({ op: 'test', children: [] });

      const result = extractor.extractFromClass(egraph, id, simpleCostFn);

      expect(result.root).toBe(id);
      expect(result.ast.type).toBe('test');
    });

    it('should return empty for invalid class ID', () => {
      const result = extractor.extractFromClass(egraph, 999, simpleCostFn);

      expect(result.cost).toBe(Infinity);
    });

    it('should use provided cost function', () => {
      const customCostFn: CostFunction = (node: ENode) => {
        return node.op === 'preferred' ? 0 : 100;
      };

      const id1 = egraph.add({ op: 'other', children: [] });
      const id2 = egraph.add({ op: 'preferred', children: [] });
      egraph.merge(id1, id2);

      const result = extractor.extractFromClass(egraph, id1, customCostFn);

      expect(result.ast.type).toBe('preferred');
      expect(result.cost).toBe(0);
    });

    it('should handle e-class with multiple nodes', () => {
      const id1 = egraph.add({ op: 'aaa', children: [] });
      const id2 = egraph.add({ op: 'b', children: [] });
      const id3 = egraph.add({ op: 'cc', children: [] });
      egraph.merge(id1, id2);
      egraph.merge(id2, id3);

      const result = extractor.extractFromClass(egraph, id1, simpleCostFn);

      expect(result.ast.type).toBe('b'); // Shortest operator name
      expect(result.cost).toBe(1);
    });
  });
});
