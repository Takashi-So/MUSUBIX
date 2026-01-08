/**
 * RuleExtractor Tests
 * @module @nahisaho/musubix-synthesis/tests
 * @description Tests for rule extraction
 * Traces to: REQ-SYN-004 (Rule Learning)
 */

import { describe, expect, it, beforeEach } from 'vitest';
import { RuleExtractor, resetRuleIdCounter } from '../../src/rules/RuleExtractor.js';
import type { Specification, Program, SynthesisRule } from '../../src/types.js';

describe('RuleExtractor', () => {
  let extractor: RuleExtractor;

  beforeEach(() => {
    resetRuleIdCounter();
    extractor = new RuleExtractor();
  });

  describe('extract', () => {
    it('should extract rule from spec and program', () => {
      const spec: Specification = {
        examples: [
          { input: { x: 1 }, output: 2 },
          { input: { x: 2 }, output: 3 },
        ],
      };

      const program: Program = {
        expression: {
          kind: 'application',
          operator: 'add',
          args: [
            { kind: 'variable', name: 'x' },
            { kind: 'constant', name: 'one' },
          ],
        },
      };

      const rules = extractor.extract(spec, program);

      expect(rules).toHaveLength(1);
      expect(rules[0].id).toMatch(/^RULE-/);
      expect(rules[0].confidence).toBe(0.5);
    });

    it('should extract pattern from spec', () => {
      const spec: Specification = {
        examples: [
          { input: { a: 1, b: 2 }, output: 3 },
          { input: { a: 2, b: 3 }, output: 5 },
        ],
      };

      const program: Program = {
        expression: {
          kind: 'application',
          operator: 'add',
          args: [
            { kind: 'variable', name: 'a' },
            { kind: 'variable', name: 'b' },
          ],
        },
      };

      const rules = extractor.extract(spec, program);

      expect(rules).toHaveLength(1);
      expect(rules[0].pattern).toBeDefined();
      expect(rules[0].pattern.inputCount).toBe(2);
    });

    it('should extract template from program', () => {
      const spec: Specification = {
        examples: [{ input: {}, output: 0 }],
      };

      const program: Program = {
        expression: { kind: 'constant', name: 'zero' },
      };

      const rules = extractor.extract(spec, program);

      expect(rules).toHaveLength(1);
      expect(rules[0].template.expression.kind).toBe('constant');
    });

    it('should extract from nested application', () => {
      const spec: Specification = {
        examples: [{ input: { x: 1 }, output: -1 }],
      };

      const program: Program = {
        expression: {
          kind: 'application',
          operator: 'neg',
          args: [{ kind: 'variable', name: 'x' }],
        },
      };

      const rules = extractor.extract(spec, program);

      expect(rules).toHaveLength(1);
      expect(rules[0].template.expression.kind).toBe('application');
    });

    it('should generate unique rule IDs', () => {
      const spec: Specification = {
        examples: [{ input: {}, output: 0 }],
      };

      const program1: Program = {
        expression: { kind: 'constant', name: 'zero' },
      };

      const program2: Program = {
        expression: { kind: 'constant', name: 'one' },
      };

      const rules1 = extractor.extract(spec, program1);
      const rules2 = extractor.extract(spec, program2);

      expect(rules1[0].id).not.toBe(rules2[0].id);
    });
  });

  describe('generalize', () => {
    it('should generalize similar rules', () => {
      const rules: SynthesisRule[] = [
        {
          id: 'RULE-001',
          pattern: { inputCount: 2, outputType: 'int', exampleCount: 2 },
          template: {
            expression: {
              kind: 'application',
              operator: 'add',
              args: [
                { kind: 'variable', name: 'a' },
                { kind: 'variable', name: 'b' },
              ],
            },
            holes: [],
          },
          confidence: 0.7,
        },
        {
          id: 'RULE-002',
          pattern: { inputCount: 2, outputType: 'int', exampleCount: 3 },
          template: {
            expression: {
              kind: 'application',
              operator: 'add',
              args: [
                { kind: 'variable', name: 'x' },
                { kind: 'variable', name: 'y' },
              ],
            },
            holes: [],
          },
          confidence: 0.8,
        },
      ];

      const generalized = extractor.generalize(rules);

      expect(generalized.length).toBeLessThanOrEqual(rules.length);
    });

    it('should keep distinct rules separate', () => {
      const rules: SynthesisRule[] = [
        {
          id: 'RULE-001',
          pattern: { inputCount: 2, outputType: 'int', exampleCount: 2 },
          template: {
            expression: {
              kind: 'application',
              operator: 'add',
              args: [],
            },
            holes: [],
          },
          confidence: 0.7,
        },
        {
          id: 'RULE-002',
          pattern: { inputCount: 1, outputType: 'string', exampleCount: 1 },
          template: {
            expression: {
              kind: 'application',
              operator: 'concat',
              args: [],
            },
            holes: [],
          },
          confidence: 0.8,
        },
      ];

      const generalized = extractor.generalize(rules);

      // Different operators should remain separate
      expect(generalized.length).toBe(2);
    });

    it('should merge confidence when generalizing', () => {
      const rules: SynthesisRule[] = [
        {
          id: 'RULE-001',
          pattern: { inputCount: 2, outputType: 'int', exampleCount: 2 },
          template: {
            expression: { kind: 'application', operator: 'add', args: [] },
            holes: [],
          },
          confidence: 0.6,
        },
        {
          id: 'RULE-002',
          pattern: { inputCount: 2, outputType: 'int', exampleCount: 2 },
          template: {
            expression: { kind: 'application', operator: 'add', args: [] },
            holes: [],
          },
          confidence: 0.8,
        },
      ];

      const generalized = extractor.generalize(rules);

      // Merged rule should have averaged confidence
      expect(generalized.length).toBe(1);
      expect(generalized[0].confidence).toBe(0.7);
    });

    it('should return empty for empty input', () => {
      const generalized = extractor.generalize([]);

      expect(generalized).toHaveLength(0);
    });

    it('should handle single rule', () => {
      const rules: SynthesisRule[] = [
        {
          id: 'RULE-001',
          pattern: { inputCount: 1, outputType: 'int', exampleCount: 1 },
          template: {
            expression: { kind: 'constant', name: 'zero' },
            holes: [],
          },
          confidence: 0.9,
        },
      ];

      const generalized = extractor.generalize(rules);

      expect(generalized).toHaveLength(1);
      expect(generalized[0].confidence).toBe(0.9);
    });
  });
});
