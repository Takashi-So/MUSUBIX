/**
 * Enumerator Tests
 * @module @nahisaho/musubix-synthesis/tests
 * @description Tests for program enumerator
 * Traces to: REQ-SYN-003 (PBE Synthesis)
 */

import { describe, expect, it, beforeEach } from 'vitest';
import { Enumerator } from '../../src/synthesis/Enumerator.js';
import { DSL, DSLBuilder } from '../../src/dsl/index.js';
import type { DSLConfig, Program } from '../../src/types.js';

describe('Enumerator', () => {
  let dsl: DSL;
  let enumerator: Enumerator;

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
      .constant('zero', { name: 'zero', type: 'int', value: 0 })
      .constant('one', { name: 'one', type: 'int', value: 1 });

    const config = builder.build();
    dsl = new DSL(config);
    enumerator = new Enumerator(dsl);
  });

  describe('enumerate', () => {
    it('should enumerate programs at depth 1', () => {
      const programs = enumerator.enumerate({ maxDepth: 1 });

      expect(programs.length).toBeGreaterThan(0);
      // Should include constants
      const hasConstant = programs.some((p) => p.expression.kind === 'constant');
      expect(hasConstant).toBe(true);
    });

    it('should enumerate more programs at greater depth', () => {
      const depth1 = enumerator.enumerate({ maxDepth: 1 });
      const depth2 = enumerator.enumerate({ maxDepth: 2 });

      expect(depth2.length).toBeGreaterThan(depth1.length);
    });

    it('should respect maxPrograms limit', () => {
      const programs = enumerator.enumerate({ maxDepth: 3, maxPrograms: 10 });

      expect(programs.length).toBeLessThanOrEqual(10);
    });

    it('should include operator applications at depth 2', () => {
      const programs = enumerator.enumerate({ maxDepth: 2 });

      const hasApplication = programs.some(
        (p) => p.expression.kind === 'application'
      );
      expect(hasApplication).toBe(true);
    });

    it('should include nested applications at depth 3', () => {
      const programs = enumerator.enumerate({ maxDepth: 3, maxPrograms: 100 });

      // Find program with nested application
      const hasNested = programs.some((p) => {
        if (p.expression.kind !== 'application') return false;
        return p.expression.args.some((arg) => arg.kind === 'application');
      });

      expect(hasNested).toBe(true);
    });

    it('should enumerate distinct programs', () => {
      const programs = enumerator.enumerate({ maxDepth: 2 });

      const serialized = programs.map((p) => JSON.stringify(p.expression));
      const unique = new Set(serialized);

      expect(unique.size).toBe(programs.length);
    });

    it('should use targetType when specified', () => {
      const programs = enumerator.enumerate({
        maxDepth: 2,
        targetType: 'int',
      });

      // All programs should have int type
      expect(programs.length).toBeGreaterThan(0);
    });
  });

  describe('enumerateExpressions', () => {
    it('should enumerate base expressions at depth 0', () => {
      const exprs = enumerator.enumerateExpressions(0);

      // Should only have constants at depth 0
      expect(exprs.every((e) => e.kind === 'constant')).toBe(true);
    });

    it('should include applications at depth > 0', () => {
      const exprs = enumerator.enumerateExpressions(1);

      const hasApplication = exprs.some((e) => e.kind === 'application');
      expect(hasApplication).toBe(true);
    });
  });

  describe('getExpressionDepth', () => {
    it('should return 0 for constant', () => {
      const depth = enumerator.getExpressionDepth({ kind: 'constant', name: 'zero' });
      expect(depth).toBe(0);
    });

    it('should return 0 for variable', () => {
      const depth = enumerator.getExpressionDepth({ kind: 'variable', name: 'x' });
      expect(depth).toBe(0);
    });

    it('should return 1 for simple application', () => {
      const depth = enumerator.getExpressionDepth({
        kind: 'application',
        operator: 'neg',
        args: [{ kind: 'constant', name: 'one' }],
      });
      expect(depth).toBe(1);
    });

    it('should return correct depth for nested application', () => {
      const depth = enumerator.getExpressionDepth({
        kind: 'application',
        operator: 'add',
        args: [
          {
            kind: 'application',
            operator: 'neg',
            args: [{ kind: 'constant', name: 'one' }],
          },
          { kind: 'constant', name: 'zero' },
        ],
      });
      expect(depth).toBe(2);
    });
  });

  describe('countPrograms', () => {
    it('should count programs at depth 1', () => {
      const count = enumerator.countPrograms(1);
      const programs = enumerator.enumerate({ maxDepth: 1 });

      expect(count).toBe(programs.length);
    });

    it('should increase with depth', () => {
      const count1 = enumerator.countPrograms(1);
      const count2 = enumerator.countPrograms(2);

      expect(count2).toBeGreaterThan(count1);
    });
  });
});
