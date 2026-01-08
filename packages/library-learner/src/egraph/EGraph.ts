/**
 * EGraph - Equality Graph data structure
 *
 * REQ-LL-004: E-graph最適化
 * DES-PHASE2-001: E-Graph Optimizer / EGraph
 *
 * @stub This is a stub implementation. Full implementation in M3.
 */

import type { ENode, EClass, EClassId } from '../types.js';

/**
 * EGraph interface
 */
export interface EGraph {
  /** Add a node to the e-graph */
  add(node: ENode): EClassId;

  /** Merge two e-classes */
  merge(id1: EClassId, id2: EClassId): EClassId;

  /** Get an e-class by ID */
  getEClass(id: EClassId): EClass | undefined;

  /** Get all e-classes */
  getAllClasses(): EClass[];

  /** Find the canonical ID for an e-class */
  find(id: EClassId): EClassId;
}

/**
 * Default EGraph implementation (stub)
 */
class EGraphImpl implements EGraph {
  private classes = new Map<EClassId, EClass>();
  private unionFind = new Map<EClassId, EClassId>();
  private nextId = 0;

  add(node: ENode): EClassId {
    const id = this.nextId++;
    const eclass: EClass = {
      id,
      nodes: [node],
      parents: new Set(),
    };
    this.classes.set(id, eclass);
    this.unionFind.set(id, id);
    return id;
  }

  merge(id1: EClassId, id2: EClassId): EClassId {
    const root1 = this.find(id1);
    const root2 = this.find(id2);

    if (root1 === root2) {
      return root1;
    }

    // Merge root2 into root1
    const class1 = this.classes.get(root1);
    const class2 = this.classes.get(root2);

    if (class1 && class2) {
      class1.nodes.push(...class2.nodes);
      for (const parent of class2.parents) {
        class1.parents.add(parent);
      }
      this.unionFind.set(root2, root1);
    }

    return root1;
  }

  getEClass(id: EClassId): EClass | undefined {
    const root = this.find(id);
    return this.classes.get(root);
  }

  getAllClasses(): EClass[] {
    // Return only root classes
    const roots = new Set<EClassId>();
    for (const id of this.classes.keys()) {
      roots.add(this.find(id));
    }
    return Array.from(roots).map((id) => this.classes.get(id)!).filter(Boolean);
  }

  find(id: EClassId): EClassId {
    // Handle unregistered IDs
    if (!this.unionFind.has(id)) {
      return id;
    }

    let root = id;
    let parent = this.unionFind.get(root);
    while (parent !== undefined && parent !== root) {
      root = parent;
      parent = this.unionFind.get(root);
    }

    // Path compression
    let current = id;
    while (current !== root) {
      const next = this.unionFind.get(current);
      if (next === undefined) break;
      this.unionFind.set(current, root);
      current = next;
    }

    return root;
  }
}

/**
 * Factory function to create an EGraph
 */
export function createEGraph(): EGraph {
  return new EGraphImpl();
}
