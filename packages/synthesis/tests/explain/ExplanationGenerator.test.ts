/**
 * ExplanationGenerator Tests
 * 
 * @see TSK-SY-106 - ExplanationGenerator実装
 * @see REQ-SY-106 - 説明生成要件
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  ExplanationGenerator,
  createExplanationGenerator,
  type SynthesizedProgram,
  type Explanation,
} from '../../src/explain/ExplanationGenerator.js';

describe('ExplanationGenerator', () => {
  let generator: ExplanationGenerator;

  beforeEach(() => {
    generator = createExplanationGenerator();
  });

  describe('Interface Definition', () => {
    it('should have generate method', () => {
      expect(typeof generator.generate).toBe('function');
    });

    it('should have getConfidence method', () => {
      expect(typeof generator.getConfidence).toBe('function');
    });

    it('should have explain method', () => {
      expect(typeof generator.explain).toBe('function');
    });

    it('should have summarize method', () => {
      expect(typeof generator.summarize).toBe('function');
    });
  });

  describe('Explanation Generation', () => {
    it('should generate explanation for string transformation', () => {
      const program: SynthesizedProgram = {
        id: 'prog-001',
        code: 'input.toUpperCase()',
        domain: 'string',
        examples: [
          { input: 'hello', output: 'HELLO' },
          { input: 'world', output: 'WORLD' },
        ],
        confidence: 0.95,
      };

      const explanation = generator.generate(program);

      expect(explanation.description).toBeTruthy();
      expect(explanation.description.length).toBeGreaterThan(10);
      expect(explanation.confidence).toBeGreaterThan(0);
    });

    it('should generate explanation for array transformation', () => {
      const program: SynthesizedProgram = {
        id: 'prog-002',
        code: 'input.reduce((a, b) => a + b, 0)',
        domain: 'array',
        examples: [
          { input: [1, 2, 3], output: 6 },
          { input: [10, 20], output: 30 },
        ],
        confidence: 0.90,
      };

      const explanation = generator.generate(program);

      expect(explanation.description).toBeTruthy();
      expect(explanation.domain).toBe('array');
    });

    it('should include step-by-step breakdown', () => {
      const program: SynthesizedProgram = {
        id: 'prog-003',
        code: 'input.split(" ").map(w => w[0]).join("")',
        domain: 'string',
        examples: [
          { input: 'hello world', output: 'hw' },
        ],
        confidence: 0.85,
      };

      const explanation = generator.generate(program);

      expect(explanation.steps).toBeDefined();
      expect(explanation.steps.length).toBeGreaterThan(0);
    });

    it('should include example walkthrough', () => {
      const program: SynthesizedProgram = {
        id: 'prog-004',
        code: 'input * 2',
        domain: 'number',
        examples: [
          { input: 5, output: 10 },
          { input: 3, output: 6 },
        ],
        confidence: 0.99,
      };

      const explanation = generator.generate(program);

      expect(explanation.exampleWalkthrough).toBeDefined();
      expect(explanation.exampleWalkthrough.length).toBeGreaterThan(0);
    });
  });

  describe('Confidence Calculation', () => {
    it('should return high confidence for simple transformations', () => {
      const program: SynthesizedProgram = {
        id: 'prog-005',
        code: 'input + 1',
        domain: 'number',
        examples: [
          { input: 1, output: 2 },
          { input: 5, output: 6 },
        ],
        confidence: 0.95,
      };

      const confidence = generator.getConfidence(program);

      expect(confidence).toBeGreaterThanOrEqual(0.8);
    });

    it('should return lower confidence for complex transformations', () => {
      const program: SynthesizedProgram = {
        id: 'prog-006',
        code: 'input.split("").filter(c => c.match(/[a-z]/i)).reverse().join("")',
        domain: 'string',
        examples: [
          { input: 'hello123', output: 'olleh' },
        ],
        confidence: 0.6,
      };

      const confidence = generator.getConfidence(program);

      expect(confidence).toBeLessThanOrEqual(0.8);
    });

    it('should factor in example count', () => {
      const programFewExamples: SynthesizedProgram = {
        id: 'prog-007',
        code: 'input.toUpperCase()',
        domain: 'string',
        examples: [{ input: 'a', output: 'A' }],
        confidence: 0.7,
      };

      const programManyExamples: SynthesizedProgram = {
        id: 'prog-008',
        code: 'input.toUpperCase()',
        domain: 'string',
        examples: [
          { input: 'a', output: 'A' },
          { input: 'b', output: 'B' },
          { input: 'c', output: 'C' },
          { input: 'd', output: 'D' },
          { input: 'e', output: 'E' },
        ],
        confidence: 0.9,
      };

      const confFew = generator.getConfidence(programFewExamples);
      const confMany = generator.getConfidence(programManyExamples);

      expect(confMany).toBeGreaterThanOrEqual(confFew);
    });
  });

  describe('Explain Method', () => {
    it('should provide detailed explanation', () => {
      const program: SynthesizedProgram = {
        id: 'prog-009',
        code: 'input.length',
        domain: 'string',
        examples: [
          { input: 'hello', output: 5 },
          { input: 'hi', output: 2 },
        ],
        confidence: 0.95,
      };

      const detailed = generator.explain(program);

      expect(detailed.description).toBeTruthy();
      expect(detailed.rationale).toBeTruthy();
      expect(detailed.limitations).toBeDefined();
    });

    it('should identify input-output relationship', () => {
      const program: SynthesizedProgram = {
        id: 'prog-010',
        code: 'input.repeat(2)',
        domain: 'string',
        examples: [
          { input: 'ab', output: 'abab' },
          { input: 'x', output: 'xx' },
        ],
        confidence: 0.88,
      };

      const detailed = generator.explain(program);

      expect(detailed.relationship).toBeDefined();
      expect(detailed.relationship.length).toBeGreaterThan(0);
    });
  });

  describe('Summarize Method', () => {
    it('should provide one-line summary', () => {
      const program: SynthesizedProgram = {
        id: 'prog-011',
        code: 'input.trim()',
        domain: 'string',
        examples: [
          { input: '  hello  ', output: 'hello' },
        ],
        confidence: 0.92,
      };

      const summary = generator.summarize(program);

      expect(typeof summary).toBe('string');
      expect(summary.length).toBeLessThan(100);
      expect(summary.length).toBeGreaterThan(5);
    });

    it('should be human-readable', () => {
      const program: SynthesizedProgram = {
        id: 'prog-012',
        code: 'input.charAt(0)',
        domain: 'string',
        examples: [
          { input: 'hello', output: 'h' },
        ],
        confidence: 0.95,
      };

      const summary = generator.summarize(program);

      // Should not contain code-like syntax
      expect(summary).not.toContain('()');
      expect(summary).not.toContain('=>');
    });
  });

  describe('Edge Cases', () => {
    it('should handle empty examples array', () => {
      const program: SynthesizedProgram = {
        id: 'prog-013',
        code: 'input',
        domain: 'unknown',
        examples: [],
        confidence: 0.1,
      };

      const explanation = generator.generate(program);

      expect(explanation.description).toBeTruthy();
      expect(explanation.confidence).toBeLessThan(0.5);
    });

    it('should handle complex nested code', () => {
      const program: SynthesizedProgram = {
        id: 'prog-014',
        code: 'input.map(x => x.split(",")).flat().filter(Boolean).map(Number)',
        domain: 'array',
        examples: [
          { input: ['1,2', '3,4'], output: [1, 2, 3, 4] },
        ],
        confidence: 0.7,
      };

      expect(() => generator.generate(program)).not.toThrow();
    });
  });
});
