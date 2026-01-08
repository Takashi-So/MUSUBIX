/**
 * DSLBuilder Tests
 * @module @nahisaho/musubix-synthesis/tests
 * @description Tests for DSL builder
 * Traces to: REQ-SYN-001 (DSL Definition)
 */

import { describe, expect, it, beforeEach } from 'vitest';
import { DSLBuilder } from '../../src/dsl/DSLBuilder.js';

describe('DSLBuilder', () => {
  let builder: DSLBuilder;

  beforeEach(() => {
    builder = new DSLBuilder();
  });

  describe('type definition', () => {
    it('should define primitive types', () => {
      builder.type('int', { kind: 'primitive', name: 'int' });
      const config = builder.build();

      expect(config.types).toHaveLength(1);
      expect(config.types[0].name).toBe('int');
      expect(config.types[0].kind).toBe('primitive');
    });

    it('should define function types', () => {
      builder.type('intFunc', {
        kind: 'function',
        params: ['int'],
        result: 'string',
      });
      const config = builder.build();

      expect(config.types).toHaveLength(1);
      expect(config.types[0].kind).toBe('function');
    });

    it('should define list types', () => {
      builder.type('intList', { kind: 'list', element: 'int' });
      const config = builder.build();

      expect(config.types).toHaveLength(1);
      expect(config.types[0].kind).toBe('list');
    });

    it('should support chaining', () => {
      builder
        .type('int', { kind: 'primitive', name: 'int' })
        .type('string', { kind: 'primitive', name: 'string' });

      const config = builder.build();
      expect(config.types).toHaveLength(2);
    });
  });

  describe('operator definition', () => {
    it('should define operator with input/output types', () => {
      builder.operator('add', {
        name: 'add',
        inputTypes: ['int', 'int'],
        outputType: 'int',
        implementation: (a: number, b: number) => a + b,
      });

      const config = builder.build();
      expect(config.operators).toHaveLength(1);
      expect(config.operators[0].name).toBe('add');
    });

    it('should validate operator has implementation', () => {
      builder.operator('noop', {
        name: 'noop',
        inputTypes: [],
        outputType: 'void',
        implementation: () => {},
      });

      const config = builder.build();
      expect(typeof config.operators[0].implementation).toBe('function');
    });

    it('should support operator description', () => {
      builder.operator('multiply', {
        name: 'multiply',
        inputTypes: ['int', 'int'],
        outputType: 'int',
        description: 'Multiplies two integers',
        implementation: (a: number, b: number) => a * b,
      });

      const config = builder.build();
      expect(config.operators[0].description).toBe('Multiplies two integers');
    });

    it('should support multiple operators', () => {
      builder
        .operator('add', {
          name: 'add',
          inputTypes: ['int', 'int'],
          outputType: 'int',
          implementation: (a: number, b: number) => a + b,
        })
        .operator('sub', {
          name: 'sub',
          inputTypes: ['int', 'int'],
          outputType: 'int',
          implementation: (a: number, b: number) => a - b,
        });

      const config = builder.build();
      expect(config.operators).toHaveLength(2);
    });
  });

  describe('constant definition', () => {
    it('should define constant with value', () => {
      builder.constant('zero', {
        name: 'zero',
        type: 'int',
        value: 0,
      });

      const config = builder.build();
      expect(config.constants).toHaveLength(1);
      expect(config.constants[0].value).toBe(0);
    });

    it('should support multiple constants', () => {
      builder
        .constant('zero', { name: 'zero', type: 'int', value: 0 })
        .constant('one', { name: 'one', type: 'int', value: 1 })
        .constant('empty', { name: 'empty', type: 'string', value: '' });

      const config = builder.build();
      expect(config.constants).toHaveLength(3);
    });
  });

  describe('build', () => {
    it('should return empty config when nothing defined', () => {
      const config = builder.build();

      expect(config.types).toHaveLength(0);
      expect(config.operators).toHaveLength(0);
      expect(config.constants).toHaveLength(0);
    });

    it('should build complete DSL config', () => {
      builder
        .type('int', { kind: 'primitive', name: 'int' })
        .type('string', { kind: 'primitive', name: 'string' })
        .operator('toString', {
          name: 'toString',
          inputTypes: ['int'],
          outputType: 'string',
          implementation: (n: number) => String(n),
        })
        .constant('zero', { name: 'zero', type: 'int', value: 0 });

      const config = builder.build();

      expect(config.types).toHaveLength(2);
      expect(config.operators).toHaveLength(1);
      expect(config.constants).toHaveLength(1);
    });

    it('should return new object each call', () => {
      builder.type('int', { kind: 'primitive', name: 'int' });

      const config1 = builder.build();
      const config2 = builder.build();

      expect(config1).not.toBe(config2);
      expect(config1).toEqual(config2);
    });
  });
});
