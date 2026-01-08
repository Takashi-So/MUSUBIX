/**
 * VersionSpace Tests
 * @module @nahisaho/musubix-synthesis/tests
 * @description Tests for version space algebra
 * Traces to: REQ-SYN-003 (PBE Synthesis)
 */

import { describe, expect, it, beforeEach } from 'vitest';
import { VersionSpace } from '../../src/synthesis/VersionSpace.js';
import { DSL, DSLBuilder } from '../../src/dsl/index.js';
import type { Program, Example } from '../../src/types.js';

describe('VersionSpace', () => {
  let dsl: DSL;

  beforeEach(() => {
    const builder = new DSLBuilder();
    builder
      .type('int', { kind: 'primitive', name: 'int' })
      .operator('add', {
        name: 'add',
        inputTypes: ['int', 'int'],
        outputType: 'int',
        implementation: (a: number, b: number) => a + b,
      })
      .operator('neg', {
        name: 'neg',
        inputTypes: ['int'],
        outputType: 'int',
        implementation: (a: number) => -a,
      })
      .constant('zero', { name: 'zero', type: 'int', value: 0 })
      .constant('one', { name: 'one', type: 'int', value: 1 });

    const config = builder.build();
    dsl = new DSL(config);
  });

  describe('add', () => {
    it('should add program to version space', () => {
      const vs = new VersionSpace();
      const program: Program = {
        expression: { kind: 'constant', name: 'zero' },
      };

      vs.add(program);

      expect(vs.size()).toBe(1);
    });

    it('should not add duplicate programs', () => {
      const vs = new VersionSpace();
      const program: Program = {
        expression: { kind: 'constant', name: 'zero' },
      };

      vs.add(program);
      vs.add(program);

      expect(vs.size()).toBe(1);
    });

    it('should add different programs', () => {
      const vs = new VersionSpace();

      vs.add({ expression: { kind: 'constant', name: 'zero' } });
      vs.add({ expression: { kind: 'constant', name: 'one' } });

      expect(vs.size()).toBe(2);
    });
  });

  describe('refine', () => {
    it('should remove programs that do not satisfy example', () => {
      const vs = new VersionSpace(dsl);

      vs.add({ expression: { kind: 'constant', name: 'zero' } });
      vs.add({ expression: { kind: 'constant', name: 'one' } });

      const example: Example = { input: {}, output: 0 };
      const refined = vs.refine(example, dsl);

      expect(refined.size()).toBe(1);
      const program = refined.getProgram();
      expect(program?.expression).toEqual({ kind: 'constant', name: 'zero' });
    });

    it('should keep programs that satisfy example', () => {
      const vs = new VersionSpace(dsl);

      vs.add({ expression: { kind: 'constant', name: 'one' } });

      const example: Example = { input: {}, output: 1 };
      const refined = vs.refine(example, dsl);

      expect(refined.size()).toBe(1);
    });

    it('should return empty version space if no programs satisfy', () => {
      const vs = new VersionSpace(dsl);

      vs.add({ expression: { kind: 'constant', name: 'zero' } });

      const example: Example = { input: {}, output: 999 };
      const refined = vs.refine(example, dsl);

      expect(refined.size()).toBe(0);
    });

    it('should handle multiple refinements', () => {
      const vs = new VersionSpace(dsl);

      vs.add({ expression: { kind: 'constant', name: 'zero' } });
      vs.add({ expression: { kind: 'constant', name: 'one' } });
      vs.add({
        expression: {
          kind: 'application',
          operator: 'neg',
          args: [{ kind: 'constant', name: 'one' }],
        },
      });

      const example1: Example = { input: {}, output: 1 };
      let refined = vs.refine(example1, dsl);

      // Only 'one' should remain
      expect(refined.size()).toBe(1);

      const example2: Example = { input: {}, output: 1 };
      refined = refined.refine(example2, dsl);

      expect(refined.size()).toBe(1);
    });
  });

  describe('isConverged', () => {
    it('should return true when single program', () => {
      const vs = new VersionSpace();

      vs.add({ expression: { kind: 'constant', name: 'zero' } });

      expect(vs.isConverged()).toBe(true);
    });

    it('should return false when multiple programs', () => {
      const vs = new VersionSpace();

      vs.add({ expression: { kind: 'constant', name: 'zero' } });
      vs.add({ expression: { kind: 'constant', name: 'one' } });

      expect(vs.isConverged()).toBe(false);
    });

    it('should return false when empty', () => {
      const vs = new VersionSpace();

      expect(vs.isConverged()).toBe(false);
    });
  });

  describe('getProgram', () => {
    it('should return program when converged', () => {
      const vs = new VersionSpace();
      const program: Program = {
        expression: { kind: 'constant', name: 'zero' },
      };

      vs.add(program);

      expect(vs.getProgram()).toEqual(program);
    });

    it('should return null when not converged', () => {
      const vs = new VersionSpace();

      vs.add({ expression: { kind: 'constant', name: 'zero' } });
      vs.add({ expression: { kind: 'constant', name: 'one' } });

      expect(vs.getProgram()).toBeNull();
    });

    it('should return null when empty', () => {
      const vs = new VersionSpace();

      expect(vs.getProgram()).toBeNull();
    });
  });

  describe('size', () => {
    it('should return 0 for empty version space', () => {
      const vs = new VersionSpace();

      expect(vs.size()).toBe(0);
    });

    it('should return correct count', () => {
      const vs = new VersionSpace();

      vs.add({ expression: { kind: 'constant', name: 'zero' } });
      vs.add({ expression: { kind: 'constant', name: 'one' } });

      expect(vs.size()).toBe(2);
    });
  });

  describe('getCandidates', () => {
    it('should return all candidates', () => {
      const vs = new VersionSpace();

      vs.add({ expression: { kind: 'constant', name: 'zero' } });
      vs.add({ expression: { kind: 'constant', name: 'one' } });

      const candidates = vs.getCandidates();

      expect(candidates).toHaveLength(2);
    });

    it('should respect limit', () => {
      const vs = new VersionSpace();

      vs.add({ expression: { kind: 'constant', name: 'zero' } });
      vs.add({ expression: { kind: 'constant', name: 'one' } });

      const candidates = vs.getCandidates(1);

      expect(candidates).toHaveLength(1);
    });

    it('should return copy of candidates', () => {
      const vs = new VersionSpace();
      const program: Program = {
        expression: { kind: 'constant', name: 'zero' },
      };

      vs.add(program);

      const candidates1 = vs.getCandidates();
      const candidates2 = vs.getCandidates();

      expect(candidates1).not.toBe(candidates2);
    });
  });
});
