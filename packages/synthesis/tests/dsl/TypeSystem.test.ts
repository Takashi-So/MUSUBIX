/**
 * TypeSystem Tests
 * @module @nahisaho/musubix-synthesis/tests
 * @description Tests for type checking and inference
 * Traces to: REQ-SYN-001 (DSL Definition)
 */

import { describe, expect, it, beforeEach } from 'vitest';
import { TypeSystem, DSLBuilder } from '../../src/dsl/index.js';
import type { DSLConfig, Program, Expression } from '../../src/types.js';

describe('TypeSystem', () => {
  let config: DSLConfig;
  let typeSystem: TypeSystem;

  beforeEach(() => {
    const builder = new DSLBuilder();
    builder
      .type('int', { kind: 'primitive', name: 'int' })
      .type('string', { kind: 'primitive', name: 'string' })
      .type('bool', { kind: 'primitive', name: 'bool' })
      .type('intList', { kind: 'list', element: 'int' })
      .operator('add', {
        name: 'add',
        inputTypes: ['int', 'int'],
        outputType: 'int',
        implementation: (a: number, b: number) => a + b,
      })
      .operator('eq', {
        name: 'eq',
        inputTypes: ['int', 'int'],
        outputType: 'bool',
        implementation: (a: number, b: number) => a === b,
      })
      .operator('strlen', {
        name: 'strlen',
        inputTypes: ['string'],
        outputType: 'int',
        implementation: (s: string) => s.length,
      })
      .constant('zero', { name: 'zero', type: 'int', value: 0 })
      .constant('empty', { name: 'empty', type: 'string', value: '' })
      .constant('true', { name: 'true', type: 'bool', value: true });

    config = builder.build();
    typeSystem = new TypeSystem(config);
  });

  describe('check', () => {
    it('should check constant type', () => {
      const program: Program = {
        expression: { kind: 'constant', name: 'zero' },
      };

      const result = typeSystem.check(program);
      expect(result).toBe(true);
    });

    it('should check operator application type', () => {
      const program: Program = {
        expression: {
          kind: 'application',
          operator: 'add',
          args: [
            { kind: 'constant', name: 'zero' },
            { kind: 'constant', name: 'zero' },
          ],
        },
      };

      const result = typeSystem.check(program);
      expect(result).toBe(true);
    });

    it('should reject type mismatch', () => {
      const program: Program = {
        expression: {
          kind: 'application',
          operator: 'add',
          args: [
            { kind: 'constant', name: 'zero' },
            { kind: 'constant', name: 'empty' }, // string, not int
          ],
        },
      };

      const result = typeSystem.check(program);
      expect(result).toBe(false);
    });

    it('should reject wrong arity', () => {
      const program: Program = {
        expression: {
          kind: 'application',
          operator: 'add',
          args: [{ kind: 'constant', name: 'zero' }],
        },
      };

      const result = typeSystem.check(program);
      expect(result).toBe(false);
    });

    it('should check nested expressions', () => {
      const program: Program = {
        expression: {
          kind: 'application',
          operator: 'eq',
          args: [
            {
              kind: 'application',
              operator: 'add',
              args: [
                { kind: 'constant', name: 'zero' },
                { kind: 'constant', name: 'zero' },
              ],
            },
            { kind: 'constant', name: 'zero' },
          ],
        },
      };

      const result = typeSystem.check(program);
      expect(result).toBe(true);
    });

    it('should reject unknown operator', () => {
      const program: Program = {
        expression: {
          kind: 'application',
          operator: 'unknown',
          args: [],
        },
      };

      const result = typeSystem.check(program);
      expect(result).toBe(false);
    });

    it('should check variable with env', () => {
      const program: Program = {
        expression: { kind: 'variable', name: 'x' },
      };

      const result = typeSystem.check(program, { x: 'int' });
      expect(result).toBe(true);
    });

    it('should reject variable without type in env', () => {
      const program: Program = {
        expression: { kind: 'variable', name: 'x' },
      };

      const result = typeSystem.check(program);
      expect(result).toBe(false);
    });
  });

  describe('infer', () => {
    it('should infer constant type', () => {
      const expr: Expression = { kind: 'constant', name: 'zero' };

      const type = typeSystem.infer(expr);
      expect(type).toBe('int');
    });

    it('should infer operator result type', () => {
      const expr: Expression = {
        kind: 'application',
        operator: 'eq',
        args: [
          { kind: 'constant', name: 'zero' },
          { kind: 'constant', name: 'zero' },
        ],
      };

      const type = typeSystem.infer(expr);
      expect(type).toBe('bool');
    });

    it('should infer nested expression type', () => {
      const expr: Expression = {
        kind: 'application',
        operator: 'strlen',
        args: [{ kind: 'constant', name: 'empty' }],
      };

      const type = typeSystem.infer(expr);
      expect(type).toBe('int');
    });

    it('should return null for unknown constant', () => {
      const expr: Expression = { kind: 'constant', name: 'unknown' };

      const type = typeSystem.infer(expr);
      expect(type).toBeNull();
    });

    it('should return null for unknown operator', () => {
      const expr: Expression = {
        kind: 'application',
        operator: 'unknown',
        args: [],
      };

      const type = typeSystem.infer(expr);
      expect(type).toBeNull();
    });

    it('should infer variable type from env', () => {
      const expr: Expression = { kind: 'variable', name: 'x' };

      const type = typeSystem.infer(expr, { x: 'string' });
      expect(type).toBe('string');
    });

    it('should return null for unknown variable', () => {
      const expr: Expression = { kind: 'variable', name: 'x' };

      const type = typeSystem.infer(expr);
      expect(type).toBeNull();
    });
  });

  describe('unify', () => {
    it('should unify same types', () => {
      const result = typeSystem.unify('int', 'int');
      expect(result).toBe('int');
    });

    it('should return null for different types', () => {
      const result = typeSystem.unify('int', 'string');
      expect(result).toBeNull();
    });
  });

  describe('isSubtype', () => {
    it('should return true for same type', () => {
      const result = typeSystem.isSubtype('int', 'int');
      expect(result).toBe(true);
    });

    it('should return false for different types', () => {
      const result = typeSystem.isSubtype('int', 'string');
      expect(result).toBe(false);
    });
  });
});
