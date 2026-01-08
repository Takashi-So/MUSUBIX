/**
 * DSL Tests
 * @module @nahisaho/musubix-synthesis/tests
 * @description Tests for DSL execution and validation
 * Traces to: REQ-SYN-001 (DSL Definition)
 */

import { describe, expect, it, beforeEach } from 'vitest';
import { DSL, DSLBuilder } from '../../src/dsl/index.js';
import type { DSLConfig, Program, Expression } from '../../src/types.js';

describe('DSL', () => {
  let config: DSLConfig;
  let dsl: DSL;

  beforeEach(() => {
    const builder = new DSLBuilder();
    builder
      .type('int', { kind: 'primitive', name: 'int' })
      .type('string', { kind: 'primitive', name: 'string' })
      .type('bool', { kind: 'primitive', name: 'bool' })
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
      .operator('gt', {
        name: 'gt',
        inputTypes: ['int', 'int'],
        outputType: 'bool',
        implementation: (a: number, b: number) => a > b,
      })
      .operator('concat', {
        name: 'concat',
        inputTypes: ['string', 'string'],
        outputType: 'string',
        implementation: (a: string, b: string) => a + b,
      })
      .operator('strlen', {
        name: 'strlen',
        inputTypes: ['string'],
        outputType: 'int',
        implementation: (s: string) => s.length,
      })
      .constant('zero', { name: 'zero', type: 'int', value: 0 })
      .constant('one', { name: 'one', type: 'int', value: 1 })
      .constant('empty', { name: 'empty', type: 'string', value: '' });

    config = builder.build();
    dsl = new DSL(config);
  });

  describe('execute', () => {
    it('should execute constant expression', () => {
      const program: Program = {
        expression: { kind: 'constant', name: 'one' },
      };

      const result = dsl.execute(program, {});
      expect(result).toBe(1);
    });

    it('should execute variable expression', () => {
      const program: Program = {
        expression: { kind: 'variable', name: 'x' },
      };

      const result = dsl.execute(program, { x: 42 });
      expect(result).toBe(42);
    });

    it('should execute simple operator application', () => {
      const program: Program = {
        expression: {
          kind: 'application',
          operator: 'add',
          args: [
            { kind: 'constant', name: 'one' },
            { kind: 'constant', name: 'one' },
          ],
        },
      };

      const result = dsl.execute(program, {});
      expect(result).toBe(2);
    });

    it('should execute nested application', () => {
      const program: Program = {
        expression: {
          kind: 'application',
          operator: 'add',
          args: [
            {
              kind: 'application',
              operator: 'mul',
              args: [
                { kind: 'variable', name: 'x' },
                { kind: 'constant', name: 'one' },
              ],
            },
            { kind: 'constant', name: 'one' },
          ],
        },
      };

      const result = dsl.execute(program, { x: 5 });
      expect(result).toBe(6);
    });

    it('should execute string operations', () => {
      const program: Program = {
        expression: {
          kind: 'application',
          operator: 'strlen',
          args: [{ kind: 'variable', name: 's' }],
        },
      };

      const result = dsl.execute(program, { s: 'hello' });
      expect(result).toBe(5);
    });

    it('should throw for unknown operator', () => {
      const program: Program = {
        expression: {
          kind: 'application',
          operator: 'unknown',
          args: [],
        },
      };

      expect(() => dsl.execute(program, {})).toThrow('Unknown operator');
    });

    it('should throw for unknown variable', () => {
      const program: Program = {
        expression: { kind: 'variable', name: 'unknown' },
      };

      expect(() => dsl.execute(program, {})).toThrow('Unknown variable');
    });

    it('should throw for unknown constant', () => {
      const program: Program = {
        expression: { kind: 'constant', name: 'unknown' },
      };

      expect(() => dsl.execute(program, {})).toThrow('Unknown constant');
    });
  });

  describe('validate', () => {
    it('should validate correct program', () => {
      const program: Program = {
        expression: {
          kind: 'application',
          operator: 'add',
          args: [
            { kind: 'constant', name: 'one' },
            { kind: 'constant', name: 'zero' },
          ],
        },
      };

      expect(dsl.validate(program)).toBe(true);
    });

    it('should reject unknown operator', () => {
      const program: Program = {
        expression: {
          kind: 'application',
          operator: 'unknown',
          args: [],
        },
      };

      expect(dsl.validate(program)).toBe(false);
    });

    it('should validate nested expressions', () => {
      const program: Program = {
        expression: {
          kind: 'application',
          operator: 'gt',
          args: [
            {
              kind: 'application',
              operator: 'add',
              args: [
                { kind: 'constant', name: 'one' },
                { kind: 'constant', name: 'one' },
              ],
            },
            { kind: 'constant', name: 'zero' },
          ],
        },
      };

      expect(dsl.validate(program)).toBe(true);
    });
  });

  describe('enumerate', () => {
    it('should enumerate programs up to max depth 1', () => {
      const programs = dsl.enumerate(1);

      // Should include constants and simple variables
      expect(programs.length).toBeGreaterThan(0);
      expect(programs.some((p) => p.expression.kind === 'constant')).toBe(true);
    });

    it('should enumerate more programs at greater depth', () => {
      const depth1 = dsl.enumerate(1);
      const depth2 = dsl.enumerate(2);

      expect(depth2.length).toBeGreaterThan(depth1.length);
    });

    it('should respect max results limit', () => {
      const programs = dsl.enumerate(3, 5);

      expect(programs.length).toBeLessThanOrEqual(5);
    });

    it('should include operator applications at depth 2', () => {
      const programs = dsl.enumerate(2);

      const hasApplication = programs.some(
        (p) => p.expression.kind === 'application'
      );
      expect(hasApplication).toBe(true);
    });
  });

  describe('getOperator', () => {
    it('should return operator by name', () => {
      const op = dsl.getOperator('add');

      expect(op).toBeDefined();
      expect(op?.name).toBe('add');
      expect(op?.inputTypes).toEqual(['int', 'int']);
    });

    it('should return undefined for unknown operator', () => {
      const op = dsl.getOperator('unknown');

      expect(op).toBeUndefined();
    });
  });

  describe('getConstant', () => {
    it('should return constant by name', () => {
      const c = dsl.getConstant('zero');

      expect(c).toBeDefined();
      expect(c?.value).toBe(0);
    });

    it('should return undefined for unknown constant', () => {
      const c = dsl.getConstant('unknown');

      expect(c).toBeUndefined();
    });
  });

  describe('getOperators', () => {
    it('should return all operators', () => {
      const ops = dsl.getOperators();

      expect(ops.length).toBe(5);
      expect(ops.map((o) => o.name)).toContain('add');
      expect(ops.map((o) => o.name)).toContain('mul');
    });
  });

  describe('getConstants', () => {
    it('should return all constants', () => {
      const constants = dsl.getConstants();

      expect(constants.length).toBe(3);
      expect(constants.map((c) => c.name)).toContain('zero');
      expect(constants.map((c) => c.name)).toContain('one');
    });
  });
});
