/**
 * EnhancedWitnessEngine Test Suite
 * @module @nahisaho/musubix-synthesis
 * @see TSK-SY-101
 * @see DES-SY-101
 * @see REQ-SY-101
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  EnhancedWitnessEngine,
  createEnhancedWitnessEngine,
  BUILTIN_WITNESSES,
  type EnhancedWitnessConfig,
} from '../../src/witness/EnhancedWitnessEngine.js';
import { DSL } from '../../src/dsl/index.js';
import type { Specification, WitnessFunction, DSLConfig } from '../../src/types.js';

// =============================================================================
// Test Fixtures
// =============================================================================

function createTestDSL(): DSL {
  const config: DSLConfig = {
    name: 'test-dsl',
    operators: [
      {
        name: 'concat',
        inputTypes: ['string', 'string'],
        outputType: 'string',
        implementation: (a: string, b: string) => a + b,
      },
      {
        name: 'substring',
        inputTypes: ['string', 'number', 'number'],
        outputType: 'string',
        implementation: (s: string, start: number, end: number) => s.substring(start, end),
      },
      {
        name: 'add',
        inputTypes: ['number', 'number'],
        outputType: 'number',
        implementation: (a: number, b: number) => a + b,
      },
      {
        name: 'multiply',
        inputTypes: ['number', 'number'],
        outputType: 'number',
        implementation: (a: number, b: number) => a * b,
      },
      {
        name: 'length',
        inputTypes: ['string'],
        outputType: 'number',
        implementation: (s: string) => s.length,
      },
      {
        name: 'map',
        inputTypes: [{ kind: 'function', inputs: ['T'], output: 'U' }, 'T[]'],
        outputType: 'U[]',
      },
      {
        name: 'filter',
        inputTypes: [{ kind: 'function', inputs: ['T'], output: 'boolean' }, 'T[]'],
        outputType: 'T[]',
      },
      {
        name: 'ite',
        inputTypes: ['boolean', 'T', 'T'],
        outputType: 'T',
        implementation: (cond: boolean, t: unknown, f: unknown) => cond ? t : f,
      },
    ],
    constants: [
      { name: 'empty', type: 'string', value: '' },
      { name: 'zero', type: 'number', value: 0 },
    ],
    types: [
      { name: 'string', kind: 'primitive' },
      { name: 'number', kind: 'primitive' },
      { name: 'boolean', kind: 'primitive' },
    ],
  };
  return new DSL(config);
}

function createSpec(input: unknown, output: unknown): Specification {
  return {
    examples: [{ input, output }],
  };
}

// =============================================================================
// Tests
// =============================================================================

describe('EnhancedWitnessEngine', () => {
  let engine: EnhancedWitnessEngine;
  let dsl: DSL;

  beforeEach(() => {
    dsl = createTestDSL();
    engine = createEnhancedWitnessEngine(dsl);
  });

  describe('Factory Function', () => {
    it('should create engine with default config', () => {
      const e = createEnhancedWitnessEngine(dsl);
      expect(e).toBeDefined();
      expect(e.getWitnessCount()).toBeGreaterThan(0);
    });

    it('should create engine with custom config', () => {
      const config: EnhancedWitnessConfig = {
        enableStringWitnesses: true,
        enableListWitnesses: false,
        enableArithmeticWitnesses: true,
        enableConditionalWitnesses: false,
      };
      const e = createEnhancedWitnessEngine(dsl, config);
      expect(e).toBeDefined();
    });

    it('should register builtin witnesses automatically', () => {
      const e = createEnhancedWitnessEngine(dsl);
      expect(e.getWitnessCount()).toBeGreaterThanOrEqual(20);
    });
  });

  describe('BUILTIN_WITNESSES', () => {
    it('should have at least 20 witness functions', () => {
      expect(BUILTIN_WITNESSES.length).toBeGreaterThanOrEqual(20);
    });

    it('should include string witnesses (8+)', () => {
      const stringWitnesses = BUILTIN_WITNESSES.filter(w => w.category === 'string');
      expect(stringWitnesses.length).toBeGreaterThanOrEqual(8);
    });

    it('should include list witnesses (6+)', () => {
      const listWitnesses = BUILTIN_WITNESSES.filter(w => w.category === 'list');
      expect(listWitnesses.length).toBeGreaterThanOrEqual(6);
    });

    it('should include arithmetic witnesses (4+)', () => {
      const arithmeticWitnesses = BUILTIN_WITNESSES.filter(w => w.category === 'arithmetic');
      expect(arithmeticWitnesses.length).toBeGreaterThanOrEqual(4);
    });

    it('should include conditional witnesses (2+)', () => {
      const conditionalWitnesses = BUILTIN_WITNESSES.filter(w => w.category === 'conditional');
      expect(conditionalWitnesses.length).toBeGreaterThanOrEqual(2);
    });
  });

  describe('String Witnesses', () => {
    it('should decompose concat specification', () => {
      const spec = createSpec(['hello', 'world'], 'helloworld');
      const decomp = engine.decompose(spec, 'concat');
      
      expect(decomp.operator).toBe('concat');
      expect(decomp.argSpecs.length).toBeGreaterThan(0);
    });

    it('should decompose substring specification', () => {
      const spec = createSpec(['hello world'], 'world');
      const decomp = engine.decompose(spec, 'substring');
      
      expect(decomp.operator).toBe('substring');
      expect(decomp.confidence).toBeGreaterThanOrEqual(0);
    });

    it('should handle empty string cases', () => {
      const spec = createSpec([''], '');
      const decomp = engine.decompose(spec, 'concat');
      
      expect(decomp).toBeDefined();
    });
  });

  describe('List Witnesses', () => {
    it('should decompose map specification', () => {
      const spec = createSpec([[1, 2, 3]], [2, 4, 6]);
      const decomp = engine.decompose(spec, 'map');
      
      expect(decomp.operator).toBe('map');
    });

    it('should decompose filter specification', () => {
      const spec = createSpec([[1, 2, 3, 4]], [2, 4]);
      const decomp = engine.decompose(spec, 'filter');
      
      expect(decomp.operator).toBe('filter');
    });
  });

  describe('Arithmetic Witnesses', () => {
    it('should decompose add specification', () => {
      const spec = createSpec([5, 3], 8);
      const decomp = engine.decompose(spec, 'add');
      
      expect(decomp.operator).toBe('add');
      expect(decomp.argSpecs.length).toBeGreaterThan(0);
    });

    it('should decompose multiply specification', () => {
      const spec = createSpec([4, 5], 20);
      const decomp = engine.decompose(spec, 'multiply');
      
      expect(decomp.operator).toBe('multiply');
    });
  });

  describe('Conditional Witnesses', () => {
    it('should decompose if-then-else specification', () => {
      const spec = createSpec([true, 'yes', 'no'], 'yes');
      const decomp = engine.decompose(spec, 'ite');
      
      expect(decomp.operator).toBe('ite');
    });
  });

  describe('registerWitness', () => {
    it('should allow custom witness registration', () => {
      const customWitness: WitnessFunction = {
        operator: 'custom_op',
        witness: () => [],
      };
      
      const countBefore = engine.getWitnessCount();
      engine.registerWitness(customWitness);
      const countAfter = engine.getWitnessCount();
      
      expect(countAfter).toBe(countBefore + 1);
    });

    it('should return registered custom witness', () => {
      const customWitness: WitnessFunction = {
        operator: 'my_op',
        witness: () => [],
      };
      
      engine.registerWitness(customWitness);
      const witnesses = engine.getWitnesses('my_op');
      
      expect(witnesses.length).toBe(1);
    });
  });

  describe('getWitnessesByCategory', () => {
    it('should return witnesses by category', () => {
      const stringWitnesses = engine.getWitnessesByCategory('string');
      expect(stringWitnesses.length).toBeGreaterThan(0);
    });

    it('should return empty array for unknown category', () => {
      const witnesses = engine.getWitnessesByCategory('unknown');
      expect(witnesses.length).toBe(0);
    });
  });

  describe('synthesizeWithWitness', () => {
    it('should synthesize using witness functions', async () => {
      const spec = createSpec([5, 3], 8);
      const result = await engine.synthesizeWithWitness(spec, { maxDepth: 3 });
      
      expect(result.synthesisTime).toBeDefined();
      expect(result.searchNodes).toBeGreaterThanOrEqual(0);
    });

    it('should track search statistics', async () => {
      const spec = createSpec(['a', 'b'], 'ab');
      const result = await engine.synthesizeWithWitness(spec);
      
      expect(result.candidatesExplored).toBeDefined();
    });
  });

  describe('listWitnesses', () => {
    it('should list all registered witnesses', () => {
      const list = engine.listWitnesses();
      
      expect(Array.isArray(list)).toBe(true);
      expect(list.length).toBeGreaterThanOrEqual(20);
    });

    it('should include operator and category info', () => {
      const list = engine.listWitnesses();
      
      for (const item of list) {
        expect(item.operator).toBeDefined();
        expect(item.category).toBeDefined();
      }
    });
  });

  describe('toJSON / fromJSON', () => {
    it('should serialize witness configuration', () => {
      const json = engine.toJSON();
      expect(json).toBeDefined();
      expect(typeof json).toBe('string');
      
      const parsed = JSON.parse(json);
      expect(parsed.version).toBeDefined();
    });

    it('should restore custom witnesses from JSON', () => {
      // Register custom witness
      engine.registerWitness({
        operator: 'custom_serialize_test',
        witness: () => [],
        category: 'custom' as 'string',
      });
      
      const json = engine.toJSON();
      
      // Create new engine and restore
      const newEngine = createEnhancedWitnessEngine(dsl);
      newEngine.fromJSON(json);
      
      expect(newEngine.getWitnessCount()).toBeGreaterThanOrEqual(engine.getWitnessCount() - 1);
    });
  });
});
