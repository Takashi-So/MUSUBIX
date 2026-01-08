/**
 * EGraphBuilder Tests
 *
 * REQ-LL-004: E-graph最適化
 * Test-First approach
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { createEGraphBuilder, type EGraphBuilder } from '../../src/egraph/EGraphBuilder.js';
import type { LearnedPattern, EqualityRule } from '../../src/types.js';

describe('EGraphBuilder', () => {
  let builder: EGraphBuilder;

  const createTestPattern = (overrides: Partial<LearnedPattern> = {}): LearnedPattern => ({
    id: `PAT-${Date.now()}-${Math.random().toString(36).slice(2, 7)}`,
    name: 'Test Pattern',
    description: 'A test pattern',
    level: 'concrete',
    ast: { type: 'Declaration' },
    confidence: 0.8,
    usageCount: 5,
    tags: ['test'],
    createdAt: new Date(),
    updatedAt: new Date(),
    ...overrides,
  });

  beforeEach(() => {
    builder = createEGraphBuilder();
  });

  describe('createEGraphBuilder', () => {
    it('should create an EGraphBuilder instance', () => {
      expect(builder).toBeDefined();
      expect(builder.build).toBeDefined();
      expect(builder.saturate).toBeDefined();
    });
  });

  describe('build', () => {
    it('should create an e-graph from empty patterns', () => {
      const graph = builder.build([]);

      expect(graph).toBeDefined();
      expect(graph.getAllClasses()).toHaveLength(0);
    });

    it('should create nodes for each pattern', () => {
      const patterns = [
        createTestPattern({ name: 'Pattern1' }),
        createTestPattern({ name: 'Pattern2' }),
        createTestPattern({ name: 'Pattern3' }),
      ];

      const graph = builder.build(patterns);

      expect(graph.getAllClasses()).toHaveLength(3);
    });

    it('should use pattern names as operators', () => {
      const patterns = [
        createTestPattern({ name: 'AddPattern' }),
      ];

      const graph = builder.build(patterns);
      const classes = graph.getAllClasses();

      expect(classes[0].nodes[0].op).toBe('AddPattern');
    });
  });

  describe('saturate', () => {
    it('should return graph unchanged with empty rules', () => {
      const patterns = [createTestPattern({ name: 'Test' })];
      const graph = builder.build(patterns);

      const saturated = builder.saturate(graph, []);

      expect(saturated).toBe(graph);
    });

    it('should accept equality rules', () => {
      const patterns = [
        createTestPattern({ name: 'A' }),
        createTestPattern({ name: 'B' }),
      ];
      const graph = builder.build(patterns);

      const rules: EqualityRule[] = [
        {
          name: 'commutative',
          lhs: { op: 'add', children: ['?a', '?b'] },
          rhs: { op: 'add', children: ['?b', '?a'] },
        },
      ];

      const saturated = builder.saturate(graph, rules);

      expect(saturated).toBeDefined();
    });

    it('should handle multiple rules', () => {
      const patterns = [createTestPattern({ name: 'X' })];
      const graph = builder.build(patterns);

      const rules: EqualityRule[] = [
        { name: 'rule1', lhs: { op: 'a' }, rhs: { op: 'b' } },
        { name: 'rule2', lhs: { op: 'b' }, rhs: { op: 'c' } },
        { name: 'rule3', lhs: { op: 'c' }, rhs: { op: 'd' } },
      ];

      const saturated = builder.saturate(graph, rules);

      expect(saturated).toBeDefined();
    });
  });
});
