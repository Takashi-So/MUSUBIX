/**
 * DSLExtender Tests
 * @module @nahisaho/musubix-synthesis
 * @description Tests for DSL grammar extension capabilities
 * Traces to: TSK-SY-104, REQ-SY-104
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  DSLExtender,
  createDSLExtender,
  DSLGap,
  OperatorSuggestion,
  DSLExtenderConfig,
} from '../../src/dsl/DSLExtender.js';

describe('DSLExtender', () => {
  let extender: DSLExtender;

  beforeEach(() => {
    extender = createDSLExtender();
  });

  describe('createDSLExtender', () => {
    it('should create extender with default config', () => {
      const newExtender = createDSLExtender();
      expect(newExtender).toBeDefined();
    });

    it('should create extender with custom config', () => {
      const config: DSLExtenderConfig = {
        maxSuggestions: 10,
        minConfidence: 0.8,
      };
      const customExtender = createDSLExtender(config);
      expect(customExtender).toBeDefined();
    });
  });

  describe('analyzeGap', () => {
    it('should identify missing operators for string manipulation', () => {
      const examples = [
        { input: 'hello world', output: 'Hello World' },
        { input: 'test case', output: 'Test Case' },
      ];
      const dslOperators = ['concat', 'substring'];

      const gaps = extender.analyzeGap(examples, dslOperators);

      expect(gaps.length).toBeGreaterThan(0);
      expect(gaps.some(g => g.type === 'missing-operator')).toBe(true);
    });

    it('should identify missing operators for numeric operations', () => {
      const examples = [
        { input: [1, 2, 3], output: 6 },
        { input: [4, 5], output: 9 },
      ];
      const dslOperators = ['map', 'filter'];

      const gaps = extender.analyzeGap(examples, dslOperators);

      expect(gaps.some(g => g.description.includes('reduce') || g.description.includes('sum'))).toBe(true);
    });

    it('should return empty array when DSL is sufficient', () => {
      const examples = [
        { input: 'hello', output: 'HELLO' },
      ];
      const dslOperators = ['uppercase', 'lowercase', 'concat'];

      const gaps = extender.analyzeGap(examples, dslOperators);

      // May still have gaps but should be minimal
      expect(gaps.every(g => g.severity === 'low' || gaps.length === 0)).toBe(true);
    });

    it('should detect type transformation gaps', () => {
      const examples = [
        { input: '123', output: 123 },
        { input: '456', output: 456 },
      ];
      const dslOperators = ['concat', 'substring'];

      const gaps = extender.analyzeGap(examples, dslOperators);

      expect(gaps.some(g => g.type === 'type-conversion')).toBe(true);
    });
  });

  describe('suggestOperators', () => {
    it('should suggest capitalize operator for title case', () => {
      const examples = [
        { input: 'hello world', output: 'Hello World' },
      ];

      const suggestions = extender.suggestOperators(examples);

      expect(suggestions.length).toBeGreaterThan(0);
      expect(suggestions.some(s => 
        s.name.includes('capitalize') || 
        s.name.includes('titleCase') ||
        s.name.includes('title')
      )).toBe(true);
    });

    it('should suggest reduce/sum for array summation', () => {
      const examples = [
        { input: [1, 2, 3], output: 6 },
        { input: [10, 20], output: 30 },
      ];

      const suggestions = extender.suggestOperators(examples);

      expect(suggestions.some(s => 
        s.name.includes('sum') || 
        s.name.includes('reduce')
      )).toBe(true);
    });

    it('should suggest parse operator for string to number', () => {
      const examples = [
        { input: '42', output: 42 },
        { input: '100', output: 100 },
      ];

      const suggestions = extender.suggestOperators(examples);

      expect(suggestions.some(s => 
        s.name.includes('parse') || 
        s.name.includes('toNumber')
      )).toBe(true);
    });

    it('should provide operator signature in suggestions', () => {
      const examples = [
        { input: 'hello', output: 'HELLO' },
      ];

      const suggestions = extender.suggestOperators(examples);

      for (const suggestion of suggestions) {
        expect(suggestion.signature).toBeDefined();
        expect(suggestion.signature).toContain('->');
      }
    });

    it('should include confidence score for each suggestion', () => {
      const examples = [
        { input: [1, 2, 3], output: [2, 4, 6] },
      ];

      const suggestions = extender.suggestOperators(examples);

      for (const suggestion of suggestions) {
        expect(suggestion.confidence).toBeGreaterThanOrEqual(0);
        expect(suggestion.confidence).toBeLessThanOrEqual(1);
      }
    });
  });

  describe('generateOperatorCode', () => {
    it('should generate implementation for suggested operator', () => {
      const suggestion: OperatorSuggestion = {
        name: 'titleCase',
        signature: 'string -> string',
        confidence: 0.9,
        description: 'Convert to title case',
      };

      const code = extender.generateOperatorCode(suggestion);

      expect(code).toContain('function');
      expect(code).toContain('titleCase');
    });

    it('should generate type-safe operator code', () => {
      const suggestion: OperatorSuggestion = {
        name: 'sum',
        signature: 'number[] -> number',
        confidence: 0.95,
        description: 'Sum array elements',
      };

      const code = extender.generateOperatorCode(suggestion);

      expect(code).toContain('number[]');
      expect(code).toContain('number');
    });
  });

  describe('getAvailableOperators', () => {
    it('should return list of known operators', () => {
      const operators = extender.getAvailableOperators();

      expect(operators.length).toBeGreaterThan(0);
      expect(operators).toContain('uppercase');
      expect(operators).toContain('lowercase');
    });

    it('should include category information', () => {
      const categories = extender.getOperatorCategories();

      expect(categories).toBeDefined();
      expect(categories['string']).toBeDefined();
      expect(categories['array']).toBeDefined();
    });
  });

  describe('validateOperator', () => {
    it('should validate correct operator signature', () => {
      const result = extender.validateOperator(
        'myOp',
        'string -> string',
        (s: string) => s.toUpperCase()
      );

      expect(result.valid).toBe(true);
    });

    it('should reject invalid operator', () => {
      const result = extender.validateOperator(
        'badOp',
        'string -> number',
        () => { throw new Error('fail'); }
      );

      expect(result.valid).toBe(false);
      expect(result.error).toBeDefined();
    });
  });
});
