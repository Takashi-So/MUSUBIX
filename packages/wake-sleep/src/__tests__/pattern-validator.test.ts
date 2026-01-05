/**
 * @fileoverview Tests for PatternValidator
 * @traceability REQ-WAKE-001-F003
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { PatternValidator } from '../validation/pattern-validator.js';
import type { PatternCandidate } from '../types.js';

describe('PatternValidator', () => {
  let validator: PatternValidator;

  beforeEach(() => {
    validator = new PatternValidator();
  });

  describe('validatePattern', () => {
    it('should validate pattern with sufficient confidence', () => {
      const pattern: PatternCandidate = {
        name: 'test-pattern',
        structure: { type: 'test', value: 'example' },
        occurrences: 3,
        confidence: 0.8,
        source: 'code',
      };

      const result = validator.validatePattern(pattern, []);

      expect(result.valid).toBe(true);
      expect(result.violations).toHaveLength(0);
      expect(result.confidence).toBe(0.8);
    });

    it('should warn on low confidence', () => {
      const pattern: PatternCandidate = {
        name: 'low-confidence-pattern',
        structure: { type: 'test' },
        occurrences: 1,
        confidence: 0.3,
        source: 'code',
      };

      const result = validator.validatePattern(pattern, []);

      expect(result.valid).toBe(true); // Warning doesn't invalidate
      expect(result.violations).toHaveLength(1);
      expect(result.violations[0].type).toBe('low-confidence');
      expect(result.violations[0].severity).toBe('warning');
    });

    it('should detect duplicate patterns', () => {
      const existingPattern: PatternCandidate = {
        id: 'existing-1',
        name: 'factory-pattern',
        structure: { type: 'factory', method: 'create' },
        occurrences: 5,
        confidence: 0.9,
        source: 'code',
      };

      const duplicatePattern: PatternCandidate = {
        name: 'factory-pattern-dup',
        structure: { type: 'factory', method: 'create' }, // Same structure
        occurrences: 2,
        confidence: 0.7,
        source: 'code',
      };

      const result = validator.validatePattern(duplicatePattern, [existingPattern]);

      expect(result.valid).toBe(false);
      expect(result.violations.some(v => v.type === 'duplicate')).toBe(true);
      expect(result.suggestions.length).toBeGreaterThan(0);
    });

    it('should warn on name collision', () => {
      const existingPatterns: PatternCandidate[] = [
        { id: 'p1', name: 'singleton', structure: { v: 1 }, occurrences: 3, confidence: 0.9, source: 'code' },
        { id: 'p2', name: 'singleton', structure: { v: 2 }, occurrences: 3, confidence: 0.9, source: 'code' },
        { id: 'p3', name: 'singleton', structure: { v: 3 }, occurrences: 3, confidence: 0.9, source: 'code' },
      ];

      const newPattern: PatternCandidate = {
        name: 'singleton',
        structure: { v: 4 },
        occurrences: 2,
        confidence: 0.8,
        source: 'code',
      };

      const result = validator.validatePattern(newPattern, existingPatterns);

      expect(result.violations.some(v => v.type === 'name-collision')).toBe(true);
    });

    it('should detect circular dependencies', () => {
      const existingPattern: PatternCandidate = {
        id: 'pattern-A',
        name: 'pattern-A',
        structure: { refs: [{ $ref: 'pattern-B' }] },
        occurrences: 3,
        confidence: 0.8,
        source: 'code',
      };

      const newPattern: PatternCandidate = {
        id: 'pattern-B',
        name: 'pattern-B',
        structure: { refs: [{ $ref: 'pattern-A' }] }, // Circular!
        occurrences: 2,
        confidence: 0.7,
        source: 'code',
      };

      const result = validator.validatePattern(newPattern, [existingPattern]);

      expect(result.valid).toBe(false);
      expect(result.violations.some(v => v.type === 'circular')).toBe(true);
    });
  });

  describe('validateBatch', () => {
    it('should validate multiple patterns', () => {
      const patterns: PatternCandidate[] = [
        { name: 'pattern-1', structure: { a: 1 }, occurrences: 3, confidence: 0.8, source: 'code' },
        { name: 'pattern-2', structure: { b: 2 }, occurrences: 2, confidence: 0.7, source: 'code' },
        { name: 'pattern-3', structure: { c: 3 }, occurrences: 4, confidence: 0.9, source: 'design' },
      ];

      const results = validator.validateBatch(patterns, []);

      expect(results).toHaveLength(3);
      expect(results.every(r => r.valid)).toBe(true);
    });

    it('should accumulate valid patterns for subsequent checks', () => {
      const patterns: PatternCandidate[] = [
        { name: 'first', structure: { x: 1 }, occurrences: 3, confidence: 0.8, source: 'code' },
        { name: 'second', structure: { x: 1 }, occurrences: 2, confidence: 0.7, source: 'code' }, // Duplicate of first
      ];

      const results = validator.validateBatch(patterns, []);

      expect(results[0].valid).toBe(true);
      expect(results[1].valid).toBe(false);
      expect(results[1].violations.some(v => v.type === 'duplicate')).toBe(true);
    });
  });

  describe('configuration', () => {
    it('should use custom configuration', () => {
      const customValidator = new PatternValidator({
        minConfidence: 0.9,
        checkDuplicates: false,
      });

      const pattern: PatternCandidate = {
        name: 'test',
        structure: {},
        occurrences: 1,
        confidence: 0.85,
        source: 'code',
      };

      const result = customValidator.validatePattern(pattern, []);

      expect(result.violations.some(v => v.type === 'low-confidence')).toBe(true);
    });

    it('should update configuration', () => {
      validator.updateConfig({ minConfidence: 0.9 });

      const pattern: PatternCandidate = {
        name: 'test',
        structure: {},
        occurrences: 1,
        confidence: 0.85,
        source: 'code',
      };

      const result = validator.validatePattern(pattern, []);

      expect(result.violations.some(v => v.type === 'low-confidence')).toBe(true);
    });

    it('should return current configuration', () => {
      const config = validator.getConfig();

      expect(config.checkDuplicates).toBe(true);
      expect(config.checkCircular).toBe(true);
      expect(config.minConfidence).toBe(0.5);
    });
  });

  describe('confidence adjustment', () => {
    it('should reduce confidence for violations', () => {
      const pattern: PatternCandidate = {
        name: 'low-conf',
        structure: {},
        occurrences: 1,
        confidence: 0.4, // Below threshold
        source: 'code',
      };

      const result = validator.validatePattern(pattern, []);

      expect(result.confidence).toBeLessThan(pattern.confidence);
    });

    it('should not reduce confidence below zero', () => {
      const validator = new PatternValidator({ minConfidence: 0.99 });
      
      const pattern: PatternCandidate = {
        name: 'very-low-conf',
        structure: {},
        occurrences: 1,
        confidence: 0.1,
        source: 'code',
      };

      const result = validator.validatePattern(pattern, []);

      expect(result.confidence).toBeGreaterThanOrEqual(0);
    });
  });

  describe('cache management', () => {
    it('should clear cache', () => {
      // Just ensure no error
      expect(() => validator.clearCache()).not.toThrow();
    });
  });
});
