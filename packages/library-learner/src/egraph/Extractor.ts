/**
 * Extractor - Extract optimal expressions from e-graphs
 *
 * REQ-LL-004: E-graph最適化
 * DES-PHASE2-001: E-Graph Optimizer / Extractor
 *
 * @stub This is a stub implementation. Full implementation in M3.
 */

import type { EClassId, CostFunction, OptimalExpression } from '../types.js';
import type { EGraph } from './EGraph.js';

/**
 * Extractor interface
 */
export interface Extractor {
  /** Extract the optimal expression from an e-graph */
  extract(graph: EGraph, costFn: CostFunction): OptimalExpression;

  /** Extract from a specific e-class */
  extractFromClass(graph: EGraph, classId: EClassId, costFn: CostFunction): OptimalExpression;
}

/**
 * Default Extractor implementation (stub)
 */
class ExtractorImpl implements Extractor {
  extract(graph: EGraph, costFn: CostFunction): OptimalExpression {
    const classes = graph.getAllClasses();
    if (classes.length === 0) {
      return {
        root: -1,
        ast: { type: 'Empty' },
        cost: Infinity,
      };
    }

    // Find the root (class with no parents)
    const root = classes.find((c) => c.parents.size === 0) ?? classes[0];
    return this.extractFromClass(graph, root.id, costFn);
  }

  extractFromClass(graph: EGraph, classId: EClassId, costFn: CostFunction): OptimalExpression {
    const eclass = graph.getEClass(classId);
    if (!eclass || eclass.nodes.length === 0) {
      return {
        root: classId,
        ast: { type: 'Empty' },
        cost: Infinity,
      };
    }

    // Find the lowest cost node
    let bestNode = eclass.nodes[0];
    let bestCost = costFn(bestNode, []);

    for (const node of eclass.nodes) {
      const cost = costFn(node, []);
      if (cost < bestCost) {
        bestCost = cost;
        bestNode = node;
      }
    }

    return {
      root: classId,
      ast: {
        type: bestNode.op,
        children: [],
      },
      cost: bestCost,
    };
  }
}

/**
 * Factory function to create an Extractor
 */
export function createExtractor(): Extractor {
  return new ExtractorImpl();
}
