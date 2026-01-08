/**
 * RewriteRuleSet Unit Tests
 *
 * @module @nahisaho/musubix-library-learner
 * @see TSK-LL-104
 * @see DES-LL-104
 * @see REQ-LL-104
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  RewriteRuleSet,
  createRewriteRuleSet,
  DefaultRewriteRuleSet,
  type RewriteRule,
  type RewriteResult,
  type RewriteRuleSetConfig,
} from '../../src/rewrite/RewriteRuleSet.js';
import type { ASTNode } from '../../src/types.js';

describe('RewriteRuleSet', () => {
  let ruleSet: RewriteRuleSet;

  beforeEach(() => {
    ruleSet = createRewriteRuleSet();
  });

  // ==========================================================================
  // Interface Tests
  // ==========================================================================

  describe('createRewriteRuleSet', () => {
    it('should create a RewriteRuleSet instance', () => {
      expect(ruleSet).toBeDefined();
      expect(ruleSet).toBeInstanceOf(DefaultRewriteRuleSet);
    });

    it('should accept custom configuration', () => {
      const customSet = createRewriteRuleSet({
        maxIterations: 50,
        enableBuiltinRules: false,
      });
      expect(customSet).toBeDefined();
    });

    it('should have at least 20 built-in rules', () => {
      expect(ruleSet.getRuleCount()).toBeGreaterThanOrEqual(20);
    });
  });

  // ==========================================================================
  // addRule Tests
  // ==========================================================================

  describe('addRule', () => {
    it('should add a custom rule', () => {
      const rule: RewriteRule = {
        id: 'custom-1',
        name: 'simplify-double-negation',
        pattern: { type: 'UnaryExpression', operator: '!', argument: { type: 'UnaryExpression', operator: '!' } },
        replacement: { type: 'Identifier', name: '$1' },
        description: 'Simplify !!x to x',
      };

      const initialCount = ruleSet.getRuleCount();
      ruleSet.addRule(rule);
      expect(ruleSet.getRuleCount()).toBe(initialCount + 1);
    });

    it('should prevent duplicate rule IDs', () => {
      const rule: RewriteRule = {
        id: 'duplicate',
        name: 'test',
        pattern: {},
        replacement: {},
      };
      ruleSet.addRule(rule);
      expect(() => ruleSet.addRule(rule)).toThrow(/duplicate/i);
    });

    it('should validate rule structure', () => {
      const invalidRule = {
        id: 'invalid',
        // missing required fields
      } as unknown as RewriteRule;

      expect(() => ruleSet.addRule(invalidRule)).toThrow();
    });
  });

  // ==========================================================================
  // rewrite Tests
  // ==========================================================================

  describe('rewrite', () => {
    it('should rewrite AST using rules', () => {
      // Test: x + 0 -> x
      const ast: ASTNode = {
        type: 'BinaryExpression',
        operator: '+',
        left: { type: 'Identifier', name: 'x' },
        right: { type: 'Literal', value: 0 },
      } as unknown as ASTNode;

      const result = ruleSet.rewrite(ast);

      expect(result.rewritten).toBeDefined();
      expect(result.rulesApplied.length).toBeGreaterThan(0);
    });

    it('should apply multiple rules', () => {
      // Test: (x * 1) + 0 -> x
      const ast: ASTNode = {
        type: 'BinaryExpression',
        operator: '+',
        left: {
          type: 'BinaryExpression',
          operator: '*',
          left: { type: 'Identifier', name: 'x' },
          right: { type: 'Literal', value: 1 },
        },
        right: { type: 'Literal', value: 0 },
      } as unknown as ASTNode;

      const result = ruleSet.rewrite(ast);

      expect(result.iterationCount).toBeGreaterThanOrEqual(1);
    });

    it('should track applied rules', () => {
      const ast: ASTNode = {
        type: 'BinaryExpression',
        operator: '+',
        left: { type: 'Identifier', name: 'x' },
        right: { type: 'Literal', value: 0 },
      } as unknown as ASTNode;

      const result = ruleSet.rewrite(ast);

      expect(Array.isArray(result.rulesApplied)).toBe(true);
    });

    it('should respect maxIterations limit', () => {
      const limitedSet = createRewriteRuleSet({ maxIterations: 3 });

      const ast: ASTNode = {
        type: 'BinaryExpression',
        operator: '+',
        left: { type: 'Identifier', name: 'x' },
        right: { type: 'Literal', value: 0 },
      } as unknown as ASTNode;

      const result = limitedSet.rewrite(ast);
      expect(result.iterationCount).toBeLessThanOrEqual(3);
    });
  });

  // ==========================================================================
  // Built-in Rules Tests
  // ==========================================================================

  describe('built-in rules', () => {
    it('should simplify x + 0 to x', () => {
      const ast: ASTNode = {
        type: 'BinaryExpression',
        operator: '+',
        left: { type: 'Identifier', name: 'x' },
        right: { type: 'Literal', value: 0 },
      } as unknown as ASTNode;

      const result = ruleSet.rewrite(ast);
      const rewritten = result.rewritten as unknown as { type: string; name?: string };

      expect(rewritten.type).toBe('Identifier');
      expect(rewritten.name).toBe('x');
    });

    it('should simplify x * 1 to x', () => {
      const ast: ASTNode = {
        type: 'BinaryExpression',
        operator: '*',
        left: { type: 'Identifier', name: 'x' },
        right: { type: 'Literal', value: 1 },
      } as unknown as ASTNode;

      const result = ruleSet.rewrite(ast);
      const rewritten = result.rewritten as unknown as { type: string; name?: string };

      expect(rewritten.type).toBe('Identifier');
      expect(rewritten.name).toBe('x');
    });

    it('should simplify x * 0 to 0', () => {
      const ast: ASTNode = {
        type: 'BinaryExpression',
        operator: '*',
        left: { type: 'Identifier', name: 'x' },
        right: { type: 'Literal', value: 0 },
      } as unknown as ASTNode;

      const result = ruleSet.rewrite(ast);
      const rewritten = result.rewritten as unknown as { type: string; value?: number };

      expect(rewritten.type).toBe('Literal');
      expect(rewritten.value).toBe(0);
    });

    it('should simplify 0 + x to x', () => {
      const ast: ASTNode = {
        type: 'BinaryExpression',
        operator: '+',
        left: { type: 'Literal', value: 0 },
        right: { type: 'Identifier', name: 'x' },
      } as unknown as ASTNode;

      const result = ruleSet.rewrite(ast);
      const rewritten = result.rewritten as unknown as { type: string; name?: string };

      expect(rewritten.type).toBe('Identifier');
      expect(rewritten.name).toBe('x');
    });

    it('should simplify 1 * x to x', () => {
      const ast: ASTNode = {
        type: 'BinaryExpression',
        operator: '*',
        left: { type: 'Literal', value: 1 },
        right: { type: 'Identifier', name: 'x' },
      } as unknown as ASTNode;

      const result = ruleSet.rewrite(ast);
      const rewritten = result.rewritten as unknown as { type: string; name?: string };

      expect(rewritten.type).toBe('Identifier');
      expect(rewritten.name).toBe('x');
    });

    it('should simplify x - 0 to x', () => {
      const ast: ASTNode = {
        type: 'BinaryExpression',
        operator: '-',
        left: { type: 'Identifier', name: 'x' },
        right: { type: 'Literal', value: 0 },
      } as unknown as ASTNode;

      const result = ruleSet.rewrite(ast);
      const rewritten = result.rewritten as unknown as { type: string; name?: string };

      expect(rewritten.type).toBe('Identifier');
      expect(rewritten.name).toBe('x');
    });

    it('should simplify x / 1 to x', () => {
      const ast: ASTNode = {
        type: 'BinaryExpression',
        operator: '/',
        left: { type: 'Identifier', name: 'x' },
        right: { type: 'Literal', value: 1 },
      } as unknown as ASTNode;

      const result = ruleSet.rewrite(ast);
      const rewritten = result.rewritten as unknown as { type: string; name?: string };

      expect(rewritten.type).toBe('Identifier');
      expect(rewritten.name).toBe('x');
    });
  });

  // ==========================================================================
  // getRule Tests
  // ==========================================================================

  describe('getRule', () => {
    it('should return rule by ID', () => {
      const rule = ruleSet.getRule('add-zero-right');
      expect(rule).toBeDefined();
      expect(rule?.name).toContain('0');
    });

    it('should return undefined for unknown ID', () => {
      const rule = ruleSet.getRule('unknown-rule');
      expect(rule).toBeUndefined();
    });
  });

  // ==========================================================================
  // listRules Tests
  // ==========================================================================

  describe('listRules', () => {
    it('should return all rules', () => {
      const rules = ruleSet.listRules();
      expect(Array.isArray(rules)).toBe(true);
      expect(rules.length).toBeGreaterThanOrEqual(20);
    });

    it('should filter by category', () => {
      const arithmeticRules = ruleSet.listRules('arithmetic');
      expect(arithmeticRules.length).toBeGreaterThan(0);
      expect(arithmeticRules.every((r) => r.category === 'arithmetic')).toBe(true);
    });
  });

  // ==========================================================================
  // removeRule Tests
  // ==========================================================================

  describe('removeRule', () => {
    it('should remove rule by ID', () => {
      const customSet = createRewriteRuleSet({ enableBuiltinRules: false });
      const rule: RewriteRule = {
        id: 'to-remove',
        name: 'test',
        pattern: {},
        replacement: {},
      };
      customSet.addRule(rule);

      const countBefore = customSet.getRuleCount();
      customSet.removeRule('to-remove');
      expect(customSet.getRuleCount()).toBe(countBefore - 1);
    });

    it('should not throw for unknown ID', () => {
      expect(() => ruleSet.removeRule('unknown')).not.toThrow();
    });
  });

  // ==========================================================================
  // Performance Tests
  // ==========================================================================

  describe('performance', () => {
    it('should rewrite complex AST within 50ms', () => {
      const ast = generateComplexAST(10);

      const startTime = Date.now();
      ruleSet.rewrite(ast);
      const elapsed = Date.now() - startTime;

      expect(elapsed).toBeLessThan(50);
    });
  });
});

// =============================================================================
// Test Helpers
// =============================================================================

function generateComplexAST(depth: number): ASTNode {
  if (depth <= 0) {
    return { type: 'Identifier', name: 'x' } as unknown as ASTNode;
  }

  return {
    type: 'BinaryExpression',
    operator: depth % 2 === 0 ? '+' : '*',
    left: generateComplexAST(depth - 1),
    right: { type: 'Literal', value: depth % 2 === 0 ? 0 : 1 },
  } as unknown as ASTNode;
}
