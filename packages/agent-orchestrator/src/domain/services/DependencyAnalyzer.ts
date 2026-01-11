/**
 * DependencyAnalyzer Domain Service
 * 
 * Analyzes dependencies between tasks
 * 
 * @see REQ-PAD-001 - Dependency Analysis
 * @see DES-PAD-001 - DependencyAnalyzer
 */

import type { SubagentSpec } from '../entities/SubagentSpec.js';

/**
 * Dependency graph node
 */
export interface DependencyNode {
  /** Node ID (spec ID) */
  readonly id: string;
  /** Dependencies (IDs this node depends on) */
  readonly dependencies: readonly string[];
  /** Dependents (IDs that depend on this node) */
  readonly dependents: readonly string[];
}

/**
 * Dependency graph
 */
export interface DependencyGraph {
  /** All nodes */
  readonly nodes: ReadonlyMap<string, DependencyNode>;
  /** Execution levels (parallel groups) */
  readonly levels: readonly (readonly string[])[];
  /** Has circular dependencies */
  readonly hasCircular: boolean;
  /** Circular dependency path if found */
  readonly circularPath?: readonly string[];
}

/**
 * Dependency analyzer interface
 */
export interface IDependencyAnalyzer {
  /**
   * Build dependency graph from specs
   * @param specs - Subagent specifications
   * @returns Dependency graph
   */
  buildGraph(specs: SubagentSpec[]): DependencyGraph;

  /**
   * Get independent specs (no dependencies)
   * @param specs - Subagent specifications
   * @returns Independent specs
   */
  getIndependentSpecs(specs: SubagentSpec[]): SubagentSpec[];

  /**
   * Get execution order (topological sort)
   * @param graph - Dependency graph
   * @returns Ordered spec IDs
   */
  getExecutionOrder(graph: DependencyGraph): string[];

  /**
   * Check for circular dependencies
   * @param specs - Subagent specifications
   * @returns Circular path or null
   */
  findCircularDependencies(specs: SubagentSpec[]): string[] | null;
}

/**
 * Create a dependency analyzer
 * 
 * @returns IDependencyAnalyzer implementation
 */
export function createDependencyAnalyzer(): IDependencyAnalyzer {
  /**
   * Build nodes from specs
   */
  function buildNodes(specs: SubagentSpec[]): Map<string, DependencyNode> {
    const nodes = new Map<string, DependencyNode>();

    // First pass: create all nodes
    for (const spec of specs) {
      nodes.set(spec.id, {
        id: spec.id,
        dependencies: [...spec.dependencies],
        dependents: [],
      });
    }

    // Second pass: populate dependents
    for (const spec of specs) {
      for (const depId of spec.dependencies) {
        const depNode = nodes.get(depId);
        if (depNode) {
          nodes.set(depId, {
            ...depNode,
            dependents: [...depNode.dependents, spec.id],
          });
        }
      }
    }

    return nodes;
  }

  /**
   * Detect circular dependencies using DFS
   */
  function detectCircular(
    nodes: Map<string, DependencyNode>
  ): string[] | null {
    const visited = new Set<string>();
    const recursionStack = new Set<string>();
    const path: string[] = [];

    function dfs(nodeId: string): string[] | null {
      visited.add(nodeId);
      recursionStack.add(nodeId);
      path.push(nodeId);

      const node = nodes.get(nodeId);
      if (node) {
        for (const depId of node.dependencies) {
          if (!visited.has(depId)) {
            const result = dfs(depId);
            if (result) return result;
          } else if (recursionStack.has(depId)) {
            // Found circular dependency
            const cycleStart = path.indexOf(depId);
            return [...path.slice(cycleStart), depId];
          }
        }
      }

      path.pop();
      recursionStack.delete(nodeId);
      return null;
    }

    for (const nodeId of nodes.keys()) {
      if (!visited.has(nodeId)) {
        const circular = dfs(nodeId);
        if (circular) return circular;
      }
    }

    return null;
  }

  /**
   * Build execution levels using Kahn's algorithm
   */
  function buildLevels(nodes: Map<string, DependencyNode>): string[][] {
    const levels: string[][] = [];
    const inDegree = new Map<string, number>();
    const remaining = new Set<string>();

    // Calculate initial in-degrees
    for (const [id, node] of nodes) {
      inDegree.set(id, node.dependencies.length);
      remaining.add(id);
    }

    while (remaining.size > 0) {
      // Find nodes with no remaining dependencies
      const level: string[] = [];
      for (const id of remaining) {
        if ((inDegree.get(id) ?? 0) === 0) {
          level.push(id);
        }
      }

      if (level.length === 0) {
        // Circular dependency - break
        break;
      }

      levels.push(level);

      // Remove processed nodes and update in-degrees
      for (const id of level) {
        remaining.delete(id);
        const node = nodes.get(id);
        if (node) {
          for (const depId of node.dependents) {
            const current = inDegree.get(depId) ?? 0;
            inDegree.set(depId, current - 1);
          }
        }
      }
    }

    return levels;
  }

  return {
    buildGraph(specs: SubagentSpec[]): DependencyGraph {
      const nodes = buildNodes(specs);
      const circular = detectCircular(nodes);
      const levels = circular ? [] : buildLevels(nodes);

      return Object.freeze({
        nodes,
        levels: Object.freeze(levels.map((l) => Object.freeze(l))),
        hasCircular: circular !== null,
        circularPath: circular ? Object.freeze(circular) : undefined,
      });
    },

    getIndependentSpecs(specs: SubagentSpec[]): SubagentSpec[] {
      return specs.filter((spec) => spec.dependencies.length === 0);
    },

    getExecutionOrder(graph: DependencyGraph): string[] {
      if (graph.hasCircular) {
        throw new Error(
          `Cannot determine execution order: circular dependency detected: ${graph.circularPath?.join(' → ')}`
        );
      }

      return graph.levels.flat();
    },

    findCircularDependencies(specs: SubagentSpec[]): string[] | null {
      const nodes = buildNodes(specs);
      return detectCircular(nodes);
    },
  };
}
