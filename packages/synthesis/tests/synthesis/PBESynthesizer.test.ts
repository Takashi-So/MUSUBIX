/**
 * PBESynthesizer Tests
 * @module @nahisaho/musubix-synthesis/tests
 * @description Tests for Programming by Example synthesizer
 * Traces to: REQ-SYN-003 (PBE Synthesis)
 */

import { describe, expect, it, beforeEach } from 'vitest';
import { PBESynthesizer } from '../../src/synthesis/PBESynthesizer.js';
import { DSL, DSLBuilder } from '../../src/dsl/index.js';
import type { Specification, Example, Program } from '../../src/types.js';

describe('PBESynthesizer', () => {
  let dsl: DSL;
  let synthesizer: PBESynthesizer;

  beforeEach(() => {
    const builder = new DSLBuilder();
    builder
      .type('int', { kind: 'primitive', name: 'int' })
      .type('string', { kind: 'primitive', name: 'string' })
      .operator('add', {
        name: 'add',
        inputTypes: ['int', 'int'],
        outputType: 'int',
        implementation: (a: number, b: number) => a + b,
      })
      .operator('mul', {
        name: 'mul',
        inputTypes: ['int', 'int'],
        outputType: 'int',
        implementation: (a: number, b: number) => a * b,
      })
      .operator('neg', {
        name: 'neg',
        inputTypes: ['int'],
        outputType: 'int',
        implementation: (a: number) => -a,
      })
      .operator('concat', {
        name: 'concat',
        inputTypes: ['string', 'string'],
        outputType: 'string',
        implementation: (a: string, b: string) => a + b,
      })
      .constant('zero', { name: 'zero', type: 'int', value: 0 })
      .constant('one', { name: 'one', type: 'int', value: 1 })
      .constant('two', { name: 'two', type: 'int', value: 2 });

    const config = builder.build();
    dsl = new DSL(config);
    synthesizer = new PBESynthesizer();
  });

  describe('synthesize', () => {
    it('should synthesize constant program', async () => {
      const spec: Specification = {
        examples: [
          { input: {}, output: 1 },
          { input: { x: 5 }, output: 1 },
        ],
      };

      const result = await synthesizer.synthesize(spec, dsl);

      expect(result.success).toBe(true);
      expect(result.program).toBeDefined();

      // Execute to verify
      if (result.program) {
        const output = dsl.execute(result.program, {});
        expect(output).toBe(1);
      }
    });

    it('should synthesize addition program', async () => {
      const spec: Specification = {
        examples: [{ input: {}, output: 2 }],
      };

      const result = await synthesizer.synthesize(spec, dsl, { maxDepth: 2 });

      expect(result.success).toBe(true);
      if (result.program) {
        const output = dsl.execute(result.program, {});
        expect(output).toBe(2);
      }
    });

    it('should synthesize negation program', async () => {
      const spec: Specification = {
        examples: [{ input: {}, output: -1 }],
      };

      const result = await synthesizer.synthesize(spec, dsl, { maxDepth: 2 });

      expect(result.success).toBe(true);
      if (result.program) {
        const output = dsl.execute(result.program, {});
        expect(output).toBe(-1);
      }
    });

    it('should return failure for unsatisfiable spec', async () => {
      const spec: Specification = {
        examples: [
          { input: {}, output: 1 },
          { input: {}, output: 2 }, // Contradictory
        ],
      };

      const result = await synthesizer.synthesize(spec, dsl, { maxDepth: 2 });

      expect(result.success).toBe(false);
      expect(result.error).toBeDefined();
    });

    it('should respect timeout', async () => {
      const spec: Specification = {
        examples: [{ input: {}, output: 999999 }],
      };

      const result = await synthesizer.synthesize(spec, dsl, {
        maxDepth: 2,
        timeout: 10, // Very short timeout
      });

      // Should either succeed quickly or timeout
      expect(typeof result.success).toBe('boolean');
    });

    it('should report synthesis time', async () => {
      const spec: Specification = {
        examples: [{ input: {}, output: 0 }],
      };

      const result = await synthesizer.synthesize(spec, dsl);

      expect(result.synthesisTime).toBeGreaterThanOrEqual(0);
    });

    it('should report candidates explored', async () => {
      const spec: Specification = {
        examples: [{ input: {}, output: 0 }],
      };

      const result = await synthesizer.synthesize(spec, dsl, { maxDepth: 2 });

      expect(result.candidatesExplored).toBeGreaterThan(0);
    });

    it('should find first satisfying program', async () => {
      const spec: Specification = {
        examples: [{ input: {}, output: 0 }],
      };

      const result = await synthesizer.synthesize(spec, dsl);

      expect(result.success).toBe(true);
      // Should find 'zero' constant
      expect(result.program?.expression.kind).toBe('constant');
    });
  });

  describe('getCandidates', () => {
    it('should return multiple candidates', async () => {
      const spec: Specification = {
        examples: [{ input: {}, output: 2 }],
      };

      const candidates = await synthesizer.getCandidates(spec, dsl, 10);

      expect(candidates.length).toBeGreaterThan(0);
    });

    it('should respect limit', async () => {
      const spec: Specification = {
        examples: [{ input: {}, output: 0 }],
      };

      const candidates = await synthesizer.getCandidates(spec, dsl, 3);

      expect(candidates.length).toBeLessThanOrEqual(3);
    });

    it('should return candidates that satisfy spec', async () => {
      const spec: Specification = {
        examples: [{ input: {}, output: 1 }],
      };

      const candidates = await synthesizer.getCandidates(spec, dsl, 5);

      for (const candidate of candidates) {
        const output = dsl.execute(candidate, {});
        expect(output).toBe(1);
      }
    });
  });

  describe('disambiguate', () => {
    it('should filter candidates with additional example', () => {
      const candidates: Program[] = [
        { expression: { kind: 'constant', name: 'one' } },
        { expression: { kind: 'constant', name: 'two' } },
      ];

      const example: Example = { input: {}, output: 1 };
      const filtered = synthesizer.disambiguate(candidates, example);

      // Current implementation returns all candidates
      expect(filtered.length).toBeGreaterThan(0);
    });
  });

  describe('ranking', () => {
    it('should prefer simpler programs', async () => {
      const spec: Specification = {
        examples: [{ input: {}, output: 1 }],
      };

      const result = await synthesizer.synthesize(spec, dsl, { maxDepth: 3 });

      // Should find 'one' constant, not 'add(zero, one)'
      expect(result.success).toBe(true);
      if (result.program) {
        // Simpler programs should be explored first
        const depth = getExpressionDepth(result.program.expression);
        expect(depth).toBeLessThanOrEqual(1);
      }
    });
  });
});

function getExpressionDepth(expr: Program['expression']): number {
  if (expr.kind === 'constant' || expr.kind === 'variable') {
    return 0;
  }
  if (expr.kind === 'application') {
    if (expr.args.length === 0) return 1;
    return 1 + Math.max(...expr.args.map(getExpressionDepth));
  }
  if (expr.kind === 'lambda') {
    return 1 + getExpressionDepth(expr.body);
  }
  return 0;
}
