/**
 * EGraph Tests
 *
 * REQ-LL-004: E-graph最適化
 * Test-First approach
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { createEGraph, type EGraph } from '../../src/egraph/EGraph.js';
import type { ENode } from '../../src/types.js';

describe('EGraph', () => {
  let egraph: EGraph;

  beforeEach(() => {
    egraph = createEGraph();
  });

  describe('createEGraph', () => {
    it('should create an EGraph instance', () => {
      expect(egraph).toBeDefined();
      expect(egraph.add).toBeDefined();
      expect(egraph.merge).toBeDefined();
      expect(egraph.getEClass).toBeDefined();
      expect(egraph.getAllClasses).toBeDefined();
      expect(egraph.find).toBeDefined();
    });
  });

  describe('add', () => {
    it('should add a node and return an e-class ID', () => {
      const node: ENode = { op: 'add', children: [] };
      const id = egraph.add(node);

      expect(typeof id).toBe('number');
      expect(id).toBeGreaterThanOrEqual(0);
    });

    it('should assign different IDs to different nodes', () => {
      const id1 = egraph.add({ op: 'add', children: [] });
      const id2 = egraph.add({ op: 'mul', children: [] });

      expect(id1).not.toBe(id2);
    });

    it('should create an e-class for the node', () => {
      const node: ENode = { op: 'const', children: [] };
      const id = egraph.add(node);

      const eclass = egraph.getEClass(id);
      expect(eclass).toBeDefined();
      expect(eclass?.nodes).toContainEqual(node);
    });
  });

  describe('merge', () => {
    it('should merge two e-classes', () => {
      const id1 = egraph.add({ op: 'a', children: [] });
      const id2 = egraph.add({ op: 'b', children: [] });

      const merged = egraph.merge(id1, id2);

      expect(merged).toBeDefined();
      expect(egraph.find(id1)).toBe(egraph.find(id2));
    });

    it('should combine nodes from both classes', () => {
      const node1: ENode = { op: 'a', children: [] };
      const node2: ENode = { op: 'b', children: [] };

      const id1 = egraph.add(node1);
      const id2 = egraph.add(node2);
      const merged = egraph.merge(id1, id2);

      const eclass = egraph.getEClass(merged);
      expect(eclass?.nodes).toHaveLength(2);
      expect(eclass?.nodes).toContainEqual(node1);
      expect(eclass?.nodes).toContainEqual(node2);
    });

    it('should be idempotent', () => {
      const id1 = egraph.add({ op: 'a', children: [] });
      const id2 = egraph.add({ op: 'b', children: [] });

      const merged1 = egraph.merge(id1, id2);
      const merged2 = egraph.merge(id1, id2);

      expect(merged1).toBe(merged2);
    });

    it('should handle transitive merging', () => {
      const id1 = egraph.add({ op: 'a', children: [] });
      const id2 = egraph.add({ op: 'b', children: [] });
      const id3 = egraph.add({ op: 'c', children: [] });

      egraph.merge(id1, id2);
      egraph.merge(id2, id3);

      expect(egraph.find(id1)).toBe(egraph.find(id3));
    });
  });

  describe('getEClass', () => {
    it('should return the e-class for a valid ID', () => {
      const id = egraph.add({ op: 'test', children: [] });

      const eclass = egraph.getEClass(id);

      expect(eclass).toBeDefined();
      expect(eclass?.id).toBe(id);
    });

    it('should return undefined for invalid ID', () => {
      const eclass = egraph.getEClass(999);

      expect(eclass).toBeUndefined();
    });

    it('should return merged class for merged IDs', () => {
      const id1 = egraph.add({ op: 'a', children: [] });
      const id2 = egraph.add({ op: 'b', children: [] });
      egraph.merge(id1, id2);

      const class1 = egraph.getEClass(id1);
      const class2 = egraph.getEClass(id2);

      expect(class1).toBe(class2);
    });
  });

  describe('getAllClasses', () => {
    it('should return empty array for empty e-graph', () => {
      const classes = egraph.getAllClasses();

      expect(classes).toEqual([]);
    });

    it('should return all e-classes', () => {
      egraph.add({ op: 'a', children: [] });
      egraph.add({ op: 'b', children: [] });
      egraph.add({ op: 'c', children: [] });

      const classes = egraph.getAllClasses();

      expect(classes).toHaveLength(3);
    });

    it('should not return merged classes separately', () => {
      const id1 = egraph.add({ op: 'a', children: [] });
      const id2 = egraph.add({ op: 'b', children: [] });
      egraph.add({ op: 'c', children: [] });
      egraph.merge(id1, id2);

      const classes = egraph.getAllClasses();

      expect(classes).toHaveLength(2);
    });
  });

  describe('find', () => {
    it('should return same ID for unmerged class', () => {
      const id = egraph.add({ op: 'test', children: [] });

      expect(egraph.find(id)).toBe(id);
    });

    it('should return canonical ID after merge', () => {
      const id1 = egraph.add({ op: 'a', children: [] });
      const id2 = egraph.add({ op: 'b', children: [] });
      const merged = egraph.merge(id1, id2);

      expect(egraph.find(id1)).toBe(merged);
      expect(egraph.find(id2)).toBe(merged);
    });

    it('should handle path compression', () => {
      const id1 = egraph.add({ op: 'a', children: [] });
      const id2 = egraph.add({ op: 'b', children: [] });
      const id3 = egraph.add({ op: 'c', children: [] });
      const id4 = egraph.add({ op: 'd', children: [] });

      egraph.merge(id1, id2);
      egraph.merge(id2, id3);
      egraph.merge(id3, id4);

      const root = egraph.find(id4);
      expect(egraph.find(id1)).toBe(root);
      expect(egraph.find(id2)).toBe(root);
      expect(egraph.find(id3)).toBe(root);
    });
  });
});
