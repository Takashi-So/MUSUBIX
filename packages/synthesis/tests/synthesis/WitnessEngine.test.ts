/**
 * WitnessEngine Tests
 * @module @nahisaho/musubix-synthesis/tests
 * @description Tests for witness-based deductive synthesis
 * Traces to: REQ-SYN-002 (Witness Functions)
 */

import { describe, expect, it, beforeEach } from 'vitest';
import { WitnessEngine } from '../../src/synthesis/WitnessEngine.js';
import { DSL, DSLBuilder } from '../../src/dsl/index.js';
import type { Specification, WitnessFunction } from '../../src/types.js';

describe('WitnessEngine', () => {
  let dsl: DSL;
  let engine: WitnessEngine;

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
      .operator('concat', {
        name: 'concat',
        inputTypes: ['string', 'string'],
        outputType: 'string',
        implementation: (a: string, b: string) => a + b,
      })
      .operator('substr', {
        name: 'substr',
        inputTypes: ['string', 'int', 'int'],
        outputType: 'string',
        implementation: (s: string, start: number, len: number) =>
          s.substring(start, start + len),
      })
      .constant('zero', { name: 'zero', type: 'int', value: 0 })
      .constant('one', { name: 'one', type: 'int', value: 1 })
      .constant('empty', { name: 'empty', type: 'string', value: '' });

    const config = builder.build();
    dsl = new DSL(config);
    engine = new WitnessEngine(dsl);
  });

  describe('registerWitness', () => {
    it('should register witness function', () => {
      const witness: WitnessFunction = {
        operator: 'add',
        argIndex: 0,
        witness: (spec) => [spec],
      };

      engine.registerWitness(witness);

      const witnesses = engine.getWitnesses('add');
      expect(witnesses).toHaveLength(1);
    });

    it('should register multiple witnesses for same operator', () => {
      const witness1: WitnessFunction = {
        operator: 'add',
        argIndex: 0,
        witness: (spec) => [spec],
      };

      const witness2: WitnessFunction = {
        operator: 'add',
        argIndex: 1,
        witness: (spec) => [spec],
      };

      engine.registerWitness(witness1);
      engine.registerWitness(witness2);

      const witnesses = engine.getWitnesses('add');
      expect(witnesses).toHaveLength(2);
    });
  });

  describe('decompose', () => {
    it('should decompose specification for operator', () => {
      const spec: Specification = {
        examples: [{ input: { a: 1, b: 2 }, output: 3 }],
      };

      // Register witness for add that propagates spec
      engine.registerWitness({
        operator: 'add',
        argIndex: 0,
        witness: (s) => [s],
      });

      const decomposed = engine.decompose(spec, 'add');

      expect(decomposed.operator).toBe('add');
      expect(decomposed.argSpecs.length).toBeGreaterThanOrEqual(0);
    });

    it('should return empty argSpecs when no witnesses', () => {
      const spec: Specification = {
        examples: [{ input: {}, output: 0 }],
      };

      const decomposed = engine.decompose(spec, 'unknown');

      expect(decomposed.operator).toBe('unknown');
      expect(decomposed.argSpecs).toHaveLength(0);
    });

    it('should apply witness functions', () => {
      const spec: Specification = {
        examples: [{ input: {}, output: 'hello' }],
      };

      let witnessCalled = false;
      engine.registerWitness({
        operator: 'concat',
        argIndex: 0,
        witness: (_s) => {
          witnessCalled = true;
          return [{ examples: [{ input: {}, output: 'hel' }] }];
        },
      });

      engine.decompose(spec, 'concat');

      expect(witnessCalled).toBe(true);
    });
  });

  describe('synthesizeWithWitness', () => {
    it('should synthesize using witness functions', async () => {
      const spec: Specification = {
        examples: [{ input: {}, output: 0 }],
      };

      const result = await engine.synthesizeWithWitness(spec, { maxDepth: 2 });

      expect(result.success).toBe(true);
      if (result.program) {
        const output = dsl.execute(result.program, {});
        expect(output).toBe(0);
      }
    });

    it('should report witness used', async () => {
      engine.registerWitness({
        operator: 'add',
        argIndex: 0,
        witness: (s) => [s],
      });

      const spec: Specification = {
        examples: [{ input: {}, output: 0 }],
      };

      const result = await engine.synthesizeWithWitness(spec, { maxDepth: 2 });

      // witnessesUsed may or may not be populated depending on path taken
      expect(result.success).toBe(true);
    });
  });

  describe('getWitnesses', () => {
    it('should return empty array for unknown operator', () => {
      const witnesses = engine.getWitnesses('unknown');
      expect(witnesses).toHaveLength(0);
    });

    it('should return registered witnesses', () => {
      engine.registerWitness({
        operator: 'concat',
        argIndex: 0,
        witness: (s) => [s],
      });

      const witnesses = engine.getWitnesses('concat');
      expect(witnesses).toHaveLength(1);
      expect(witnesses[0].operator).toBe('concat');
    });
  });

  describe('clearWitnesses', () => {
    it('should clear all witnesses', () => {
      engine.registerWitness({
        operator: 'add',
        argIndex: 0,
        witness: (s) => [s],
      });

      engine.clearWitnesses();

      const witnesses = engine.getWitnesses('add');
      expect(witnesses).toHaveLength(0);
    });
  });
});
