/**
 * ExampleAnalyzer Tests
 * @module @nahisaho/musubix-synthesis
 * @description Tests for input/output example quality analysis
 * Traces to: TSK-SY-105, REQ-SY-105
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  ExampleAnalyzer,
  createExampleAnalyzer,
  ExampleQuality,
  Ambiguity,
  ExampleSuggestion,
  ExampleAnalyzerConfig,
} from '../../src/analysis/ExampleAnalyzer.js';

describe('ExampleAnalyzer', () => {
  let analyzer: ExampleAnalyzer;

  beforeEach(() => {
    analyzer = createExampleAnalyzer();
  });

  describe('createExampleAnalyzer', () => {
    it('should create analyzer with default config', () => {
      const newAnalyzer = createExampleAnalyzer();
      expect(newAnalyzer).toBeDefined();
    });

    it('should create analyzer with custom config', () => {
      const config: ExampleAnalyzerConfig = {
        minExamples: 5,
        ambiguityThreshold: 0.3,
      };
      const customAnalyzer = createExampleAnalyzer(config);
      expect(customAnalyzer).toBeDefined();
    });
  });

  describe('analyzeQuality', () => {
    it('should rate high quality for diverse examples', () => {
      const examples = [
        { input: 'hello', output: 'HELLO' },
        { input: 'world', output: 'WORLD' },
        { input: 'Test Case', output: 'TEST CASE' },
        { input: '', output: '' },
        { input: 'abc123', output: 'ABC123' },
      ];

      const quality = analyzer.analyzeQuality(examples);

      expect(quality.score).toBeGreaterThan(0.7);
      expect(quality.diversity).toBeGreaterThan(0.5);
    });

    it('should rate low quality for insufficient examples', () => {
      const examples = [
        { input: 'hello', output: 'HELLO' },
      ];

      const quality = analyzer.analyzeQuality(examples);

      expect(quality.score).toBeLessThan(0.5);
      expect(quality.issues).toContain('Insufficient examples');
    });

    it('should rate low quality for redundant examples', () => {
      const examples = [
        { input: 'hello', output: 'HELLO' },
        { input: 'hello', output: 'HELLO' },
        { input: 'hello', output: 'HELLO' },
      ];

      const quality = analyzer.analyzeQuality(examples);

      expect(quality.score).toBeLessThan(0.5);
      expect(quality.issues.some(i => i.includes('redundant') || i.includes('duplicate'))).toBe(true);
    });

    it('should detect missing edge cases', () => {
      const examples = [
        { input: 'hello', output: 'HELLO' },
        { input: 'world', output: 'WORLD' },
      ];

      const quality = analyzer.analyzeQuality(examples);

      expect(quality.missingEdgeCases.length).toBeGreaterThan(0);
    });

    it('should calculate consistency score', () => {
      const examples = [
        { input: 'a', output: 'A' },
        { input: 'b', output: 'B' },
        { input: 'c', output: 'C' },
      ];

      const quality = analyzer.analyzeQuality(examples);

      expect(quality.consistency).toBeGreaterThan(0.8);
    });
  });

  describe('suggestAdditionalExamples', () => {
    it('should suggest empty string example if missing', () => {
      const examples = [
        { input: 'hello', output: 'HELLO' },
        { input: 'world', output: 'WORLD' },
      ];

      const suggestions = analyzer.suggestAdditionalExamples(examples);

      expect(suggestions.some(s => s.input === '' || s.reason.includes('empty'))).toBe(true);
    });

    it('should suggest numeric examples for string input', () => {
      const examples = [
        { input: 'hello', output: 'HELLO' },
      ];

      const suggestions = analyzer.suggestAdditionalExamples(examples);

      expect(suggestions.some(s => 
        /\d/.test(String(s.input)) || s.reason.includes('numeric')
      )).toBe(true);
    });

    it('should suggest boundary cases for arrays', () => {
      const examples = [
        { input: [1, 2, 3], output: 6 },
        { input: [4, 5], output: 9 },
      ];

      const suggestions = analyzer.suggestAdditionalExamples(examples);

      expect(suggestions.some(s => 
        Array.isArray(s.input) && (s.input as unknown[]).length === 0
      )).toBe(true);
    });

    it('should suggest negative number cases', () => {
      const examples = [
        { input: [1, 2, 3], output: 6 },
      ];

      const suggestions = analyzer.suggestAdditionalExamples(examples);

      expect(suggestions.some(s => 
        s.reason.includes('negative')
      )).toBe(true);
    });

    it('should limit suggestions to maxSuggestions', () => {
      const examples = [
        { input: 'a', output: 'A' },
      ];

      const suggestions = analyzer.suggestAdditionalExamples(examples, 3);

      expect(suggestions.length).toBeLessThanOrEqual(3);
    });
  });

  describe('detectAmbiguity', () => {
    it('should detect ambiguity when multiple transformations are possible', () => {
      const examples = [
        { input: 'hello', output: 'Hello' },
      ];

      const ambiguities = analyzer.detectAmbiguity(examples);

      expect(ambiguities.length).toBeGreaterThan(0);
      expect(ambiguities[0].possibleInterpretations.length).toBeGreaterThan(1);
    });

    it('should not detect ambiguity for clear transformations', () => {
      const examples = [
        { input: 'hello', output: 'HELLO' },
        { input: 'world', output: 'WORLD' },
        { input: 'test', output: 'TEST' },
        { input: '', output: '' },
      ];

      const ambiguities = analyzer.detectAmbiguity(examples);

      expect(ambiguities.length).toBe(0);
    });

    it('should suggest disambiguating examples', () => {
      const examples = [
        { input: 'hello', output: 'Hello' },
      ];

      const ambiguities = analyzer.detectAmbiguity(examples);

      if (ambiguities.length > 0) {
        expect(ambiguities[0].suggestedDisambiguation).toBeDefined();
        expect(ambiguities[0].suggestedDisambiguation.length).toBeGreaterThan(0);
      }
    });

    it('should detect type ambiguity', () => {
      const examples = [
        { input: '42', output: 42 },
      ];

      const ambiguities = analyzer.detectAmbiguity(examples);

      expect(ambiguities.some(a => 
        a.type === 'type-ambiguity' || a.possibleInterpretations.some(i => i.includes('parse'))
      )).toBe(true);
    });
  });

  describe('getExampleCoverage', () => {
    it('should return coverage metrics', () => {
      const examples = [
        { input: 'hello', output: 'HELLO' },
        { input: '', output: '' },
        { input: '123', output: '123' },
      ];

      const coverage = analyzer.getExampleCoverage(examples);

      expect(coverage.inputTypes).toBeDefined();
      expect(coverage.edgeCases).toBeDefined();
      expect(coverage.totalCoverage).toBeGreaterThan(0);
    });

    it('should track covered input types', () => {
      const examples = [
        { input: 'string', output: 'STRING' },
        { input: 123, output: '123' },
        { input: [1, 2], output: '[1, 2]' },
      ];

      const coverage = analyzer.getExampleCoverage(examples);

      expect(coverage.inputTypes).toContain('string');
      expect(coverage.inputTypes).toContain('number');
      expect(coverage.inputTypes).toContain('array');
    });
  });
});
