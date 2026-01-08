/**
 * RuleLibrary Tests
 * @module @nahisaho/musubix-synthesis/tests
 * @description Tests for rule library storage and retrieval
 * Traces to: REQ-SYN-004 (Rule Learning)
 */

import { describe, expect, it, beforeEach } from 'vitest';
import { RuleLibrary } from '../../src/rules/RuleLibrary.js';
import type { SynthesisRule, Specification } from '../../src/types.js';

describe('RuleLibrary', () => {
  let library: RuleLibrary;

  beforeEach(() => {
    library = new RuleLibrary();
  });

  describe('add', () => {
    it('should add rule to library', async () => {
      const rule: SynthesisRule = {
        id: 'RULE-001',
        pattern: { inputCount: 2, outputType: 'int', exampleCount: 2 },
        template: {
          expression: { kind: 'application', operator: 'add', args: [] },
          holes: [],
        },
        confidence: 0.8,
      };

      await library.add(rule);

      const retrieved = await library.get('RULE-001');
      expect(retrieved).toEqual(rule);
    });

    it('should update existing rule', async () => {
      const rule1: SynthesisRule = {
        id: 'RULE-001',
        pattern: { inputCount: 2, outputType: 'int', exampleCount: 2 },
        template: {
          expression: { kind: 'constant', name: 'zero' },
          holes: [],
        },
        confidence: 0.5,
      };

      const rule2: SynthesisRule = {
        id: 'RULE-001',
        pattern: { inputCount: 2, outputType: 'int', exampleCount: 3 },
        template: {
          expression: { kind: 'constant', name: 'one' },
          holes: [],
        },
        confidence: 0.9,
      };

      await library.add(rule1);
      await library.add(rule2);

      const retrieved = await library.get('RULE-001');
      expect(retrieved?.confidence).toBe(0.9);
    });
  });

  describe('get', () => {
    it('should return rule by ID', async () => {
      const rule: SynthesisRule = {
        id: 'RULE-TEST',
        pattern: { inputCount: 1, outputType: 'string', exampleCount: 1 },
        template: {
          expression: { kind: 'constant', name: 'empty' },
          holes: [],
        },
        confidence: 0.7,
      };

      await library.add(rule);

      const retrieved = await library.get('RULE-TEST');
      expect(retrieved?.id).toBe('RULE-TEST');
    });

    it('should return null for non-existent rule', async () => {
      const retrieved = await library.get('NON-EXISTENT');
      expect(retrieved).toBeNull();
    });
  });

  describe('match', () => {
    it('should match rules by pattern', async () => {
      const rule: SynthesisRule = {
        id: 'RULE-ADD',
        pattern: { inputCount: 2, outputType: 'int', exampleCount: 2 },
        template: {
          expression: { kind: 'application', operator: 'add', args: [] },
          holes: [],
        },
        confidence: 0.8,
      };

      await library.add(rule);

      const spec: Specification = {
        examples: [
          { input: { a: 1, b: 2 }, output: 3 },
          { input: { a: 2, b: 3 }, output: 5 },
        ],
      };

      const matches = await library.match(spec);

      expect(matches).toHaveLength(1);
      expect(matches[0].id).toBe('RULE-ADD');
    });

    it('should return empty array when no match', async () => {
      const rule: SynthesisRule = {
        id: 'RULE-THREE',
        pattern: { inputCount: 3, outputType: 'int', exampleCount: 1 },
        template: {
          expression: { kind: 'constant', name: 'zero' },
          holes: [],
        },
        confidence: 0.8,
      };

      await library.add(rule);

      const spec: Specification = {
        examples: [{ input: { x: 1 }, output: 2 }],
      };

      const matches = await library.match(spec);

      expect(matches).toHaveLength(0);
    });

    it('should return multiple matches', async () => {
      const rule1: SynthesisRule = {
        id: 'RULE-001',
        pattern: { inputCount: 2, outputType: 'int', exampleCount: 2 },
        template: {
          expression: { kind: 'application', operator: 'add', args: [] },
          holes: [],
        },
        confidence: 0.8,
      };

      const rule2: SynthesisRule = {
        id: 'RULE-002',
        pattern: { inputCount: 2, outputType: 'int', exampleCount: 2 },
        template: {
          expression: { kind: 'application', operator: 'mul', args: [] },
          holes: [],
        },
        confidence: 0.7,
      };

      await library.add(rule1);
      await library.add(rule2);

      const spec: Specification = {
        examples: [
          { input: { a: 1, b: 2 }, output: 3 },
          { input: { a: 2, b: 3 }, output: 5 },
        ],
      };

      const matches = await library.match(spec);

      expect(matches).toHaveLength(2);
    });

    it('should sort matches by confidence', async () => {
      const lowConf: SynthesisRule = {
        id: 'RULE-LOW',
        pattern: { inputCount: 1, outputType: 'int', exampleCount: 1 },
        template: {
          expression: { kind: 'constant', name: 'zero' },
          holes: [],
        },
        confidence: 0.3,
      };

      const highConf: SynthesisRule = {
        id: 'RULE-HIGH',
        pattern: { inputCount: 1, outputType: 'int', exampleCount: 1 },
        template: {
          expression: { kind: 'constant', name: 'one' },
          holes: [],
        },
        confidence: 0.9,
      };

      await library.add(lowConf);
      await library.add(highConf);

      const spec: Specification = {
        examples: [{ input: { x: 1 }, output: 2 }],
      };

      const matches = await library.match(spec);

      expect(matches[0].id).toBe('RULE-HIGH');
      expect(matches[1].id).toBe('RULE-LOW');
    });
  });

  describe('recordUsage', () => {
    it('should increase confidence on success', async () => {
      const rule: SynthesisRule = {
        id: 'RULE-001',
        pattern: { inputCount: 1, outputType: 'int', exampleCount: 1 },
        template: {
          expression: { kind: 'constant', name: 'zero' },
          holes: [],
        },
        confidence: 0.5,
      };

      await library.add(rule);
      await library.recordUsage('RULE-001', true);

      const updated = await library.get('RULE-001');
      expect(updated?.confidence).toBeGreaterThan(0.5);
    });

    it('should decrease confidence on failure', async () => {
      const rule: SynthesisRule = {
        id: 'RULE-001',
        pattern: { inputCount: 1, outputType: 'int', exampleCount: 1 },
        template: {
          expression: { kind: 'constant', name: 'zero' },
          holes: [],
        },
        confidence: 0.5,
      };

      await library.add(rule);
      await library.recordUsage('RULE-001', false);

      const updated = await library.get('RULE-001');
      expect(updated?.confidence).toBeLessThan(0.5);
    });

    it('should clamp confidence between 0 and 1', async () => {
      const rule: SynthesisRule = {
        id: 'RULE-001',
        pattern: { inputCount: 1, outputType: 'int', exampleCount: 1 },
        template: {
          expression: { kind: 'constant', name: 'zero' },
          holes: [],
        },
        confidence: 0.95,
      };

      await library.add(rule);

      // Multiple successes
      for (let i = 0; i < 10; i++) {
        await library.recordUsage('RULE-001', true);
      }

      const updated = await library.get('RULE-001');
      expect(updated?.confidence).toBeLessThanOrEqual(1.0);
    });
  });

  describe('prune', () => {
    it('should remove low confidence rules', async () => {
      const lowConf: SynthesisRule = {
        id: 'RULE-LOW',
        pattern: { inputCount: 1, outputType: 'int', exampleCount: 1 },
        template: {
          expression: { kind: 'constant', name: 'zero' },
          holes: [],
        },
        confidence: 0.1,
      };

      const highConf: SynthesisRule = {
        id: 'RULE-HIGH',
        pattern: { inputCount: 1, outputType: 'int', exampleCount: 1 },
        template: {
          expression: { kind: 'constant', name: 'one' },
          holes: [],
        },
        confidence: 0.9,
      };

      await library.add(lowConf);
      await library.add(highConf);

      await library.prune(0.3);

      const all = await library.getAll();
      expect(all).toHaveLength(1);
      expect(all[0].id).toBe('RULE-HIGH');
    });

    it('should not remove rules above threshold', async () => {
      const rule: SynthesisRule = {
        id: 'RULE-001',
        pattern: { inputCount: 1, outputType: 'int', exampleCount: 1 },
        template: {
          expression: { kind: 'constant', name: 'zero' },
          holes: [],
        },
        confidence: 0.6,
      };

      await library.add(rule);
      await library.prune(0.5);

      const retrieved = await library.get('RULE-001');
      expect(retrieved).not.toBeNull();
    });
  });

  describe('getAll', () => {
    it('should return all rules', async () => {
      await library.add({
        id: 'RULE-001',
        pattern: { inputCount: 1, outputType: 'int', exampleCount: 1 },
        template: {
          expression: { kind: 'constant', name: 'zero' },
          holes: [],
        },
        confidence: 0.5,
      });

      await library.add({
        id: 'RULE-002',
        pattern: { inputCount: 2, outputType: 'int', exampleCount: 2 },
        template: {
          expression: { kind: 'constant', name: 'one' },
          holes: [],
        },
        confidence: 0.7,
      });

      const all = await library.getAll();

      expect(all).toHaveLength(2);
    });

    it('should return empty array when no rules', async () => {
      const all = await library.getAll();

      expect(all).toHaveLength(0);
    });
  });
});
