/**
 * EGraphBuilder - Build e-graphs from patterns
 *
 * REQ-LL-004: E-graph最適化
 * DES-PHASE2-001: E-Graph Optimizer / EGraphBuilder
 *
 * @stub This is a stub implementation. Full implementation in M3.
 */

import type { LearnedPattern, EqualityRule } from '../types.js';
import type { EGraph } from './EGraph.js';
import { createEGraph } from './EGraph.js';

/**
 * EGraphBuilder interface
 */
export interface EGraphBuilder {
  /** Build an e-graph from patterns */
  build(patterns: LearnedPattern[]): EGraph;

  /** Apply rules until saturation */
  saturate(graph: EGraph, rules: EqualityRule[]): EGraph;
}

/**
 * Default EGraphBuilder implementation (stub)
 */
class EGraphBuilderImpl implements EGraphBuilder {
  build(patterns: LearnedPattern[]): EGraph {
    const graph = createEGraph();

    for (const pattern of patterns) {
      // Add pattern as a node
      graph.add({
        op: pattern.name,
        children: [],
      });
    }

    return graph;
  }

  saturate(graph: EGraph, _rules: EqualityRule[]): EGraph {
    // Stub: return graph unchanged
    // Full implementation would apply rules until fixpoint
    return graph;
  }
}

/**
 * Factory function to create an EGraphBuilder
 */
export function createEGraphBuilder(): EGraphBuilder {
  return new EGraphBuilderImpl();
}
