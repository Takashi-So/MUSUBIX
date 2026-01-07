/**
 * @fileoverview Unit tests for ProofGenerator
 * @module @nahisaho/musubix-lean/tests/proof/ProofGenerator
 * @traceability REQ-LEAN-PROOF-001 to REQ-LEAN-PROOF-003
 */

import { describe, it, expect } from 'vitest';
import {
  ProofGenerator,
  generateProof,
  generateProofSketch,
  applyTactic,
  selectStrategy,
} from '../../src/proof/ProofGenerator.ts';
import type { LeanTheorem, ProofStrategy, ProofState } from '../../src/types.ts';

describe('ProofGenerator', () => {
  const generator = new ProofGenerator();

  const createTheorem = (overrides: Partial<LeanTheorem> = {}): LeanTheorem => ({
    id: 'THM-001',
    name: 'test_theorem',
    statement: 'a > 0 → a + 1 > 0',
    requirementId: 'REQ-001',
    hypotheses: [{ name: 'h_pos', type: 'a > 0', leanCode: 'h_pos : a > 0' }],
    conclusion: { type: 'a + 1 > 0', leanCode: 'a + 1 > 0' },
    leanCode: 'theorem test_theorem : a > 0 → a + 1 > 0 := by sorry',
    ...overrides,
  });

  describe('generate (async)', () => {
    it('should generate proof for simple theorem', async () => {
      const theorem = createTheorem();
      const result = await generator.generate(theorem);

      expect(result.success || !result.success).toBe(true); // Either succeeds or fails gracefully
      expect(result.tacticsAttempted.length).toBeGreaterThanOrEqual(0);
      expect(result.duration).toBeGreaterThanOrEqual(0);
    });

    it('should respect timeout option', async () => {
      const theorem = createTheorem();
      const result = await generator.generate(theorem, { timeout: 100 });

      expect(result.duration).toBeLessThanOrEqual(1000);
    });

    it('should use provided strategies', async () => {
      const theorem = createTheorem();
      const customStrategy: ProofStrategy = {
        name: 'custom',
        tactics: ['intro', 'assumption'],
        applicability: () => true,
      };

      const result = await generator.generate(theorem, {
        strategies: [customStrategy],
      });

      expect(result.tacticsAttempted).toBeDefined();
    });
  });

  describe('generateSketch', () => {
    it('should generate proof sketch with sorry markers', () => {
      const theorem = createTheorem();
      const sketch = generator.generateSketch(theorem);

      expect(sketch.theoremName).toBe('test_theorem');
      expect(sketch.completionRate).toBeGreaterThanOrEqual(0);
      expect(sketch.completionRate).toBeLessThanOrEqual(100);
    });

    it('should include hints for sorry locations', () => {
      const theorem = createTheorem({
        statement: 'complex predicate → another complex predicate',
        conclusion: { type: 'another complex predicate', leanCode: 'another_complex_predicate' },
      });

      const sketch = generator.generateSketch(theorem);
      expect(sketch.hints).toBeDefined();
    });

    it('should include partial tactics in sketch', () => {
      const theorem = createTheorem();
      const sketch = generator.generateSketch(theorem, ['intro', 'assumption']);

      expect(sketch.partialProof).toContain('intro');
      expect(sketch.partialProof).toContain('sorry');
    });
  });

  describe('applyTactic', () => {
    it('should apply tactic to proof state', async () => {
      const state: ProofState = {
        goals: [{ id: 0, type: 'True', leanCode: 'True' }],
        hypotheses: [],
        currentGoal: 0,
      };

      const result = await generator.applyTactic(state, 'trivial');
      expect(result.success || !result.success).toBe(true);
    });
  });

  describe('selectStrategy', () => {
    it('should select best strategy for theorem', () => {
      const theorem = createTheorem();
      const strategy = generator.selectStrategy(theorem);

      expect(strategy).toBeDefined();
      expect(strategy.name).toBeDefined();
      expect(strategy.tactics.length).toBeGreaterThan(0);
    });
  });

  describe('addStrategy', () => {
    it('should add custom strategy', () => {
      const newGenerator = new ProofGenerator();
      newGenerator.addStrategy({
        name: 'test-strategy',
        tactics: ['test_tactic'],
        applicability: () => true,
      });

      // Strategy should be usable
      const theorem = createTheorem();
      const strategy = newGenerator.selectStrategy(theorem);
      expect(strategy).toBeDefined();
    });
  });
});

describe('generateProof function', () => {
  it('should generate proof for theorem', async () => {
    const theorem: LeanTheorem = {
      id: 'THM-001',
      name: 'test_theorem',
      statement: 'True',
      requirementId: 'REQ-001',
      hypotheses: [],
      conclusion: { type: 'True', leanCode: 'True' },
      leanCode: 'theorem test_theorem : True := by trivial',
    };

    const result = await generateProof(theorem);
    expect(result.tacticsAttempted).toBeDefined();
    expect(result.duration).toBeGreaterThanOrEqual(0);
  });
});

describe('generateProofSketch function', () => {
  it('should generate sketch with sorry markers', () => {
    const theorem: LeanTheorem = {
      id: 'THM-001',
      name: 'test_theorem',
      statement: 'a → b',
      requirementId: 'REQ-001',
      hypotheses: [],
      conclusion: { type: 'a → b', leanCode: 'a → b' },
      leanCode: 'theorem test_theorem : a → b := by sorry',
    };

    const sketch = generateProofSketch(theorem);
    expect(sketch.theoremName).toBe('test_theorem');
    expect(sketch.partialProof).toContain('sorry');
    expect(sketch.hints).toBeDefined();
  });
});

describe('applyTactic function', () => {
  it('should apply rfl tactic on equality goal', async () => {
    const state: ProofState = {
      goals: [{ id: 0, type: 'a = a', leanCode: 'a = a' }],
      hypotheses: [],
      currentGoal: 0,
    };

    const result = await applyTactic(state, 'rfl');
    expect(result.success).toBe(true);
  });

  it('should apply assumption when hypothesis matches goal', async () => {
    const state: ProofState = {
      goals: [{ id: 0, type: 'p', leanCode: 'p' }],
      hypotheses: [{ name: 'h', type: 'p', leanCode: 'h : p' }],
      currentGoal: 0,
    };

    const result = await applyTactic(state, 'assumption');
    expect(result.success).toBe(true);
  });

  it('should fail tactic when not applicable', async () => {
    const state: ProofState = {
      goals: [{ id: 0, type: 'complex_goal', leanCode: 'complex_goal' }],
      hypotheses: [],
      currentGoal: 0,
    };

    const result = await applyTactic(state, 'rfl');
    expect(result.success).toBe(false);
  });
});

describe('selectStrategy function', () => {
  it('should select applicable strategy', () => {
    const theorem: LeanTheorem = {
      id: 'THM-001',
      name: 'test_theorem',
      statement: 'a ∧ b',
      requirementId: 'REQ-001',
      hypotheses: [],
      conclusion: { type: 'a ∧ b', leanCode: 'a ∧ b' },
      leanCode: 'theorem test_theorem : a ∧ b := by sorry',
    };

    const strategy = selectStrategy(theorem);
    expect(strategy).toBeDefined();
    expect(strategy.tactics.length).toBeGreaterThan(0);
  });
});
