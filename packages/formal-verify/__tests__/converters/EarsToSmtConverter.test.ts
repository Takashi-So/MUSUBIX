/**
 * EarsToSmtConverter Unit Tests
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { EarsToSmtConverter } from '../../src/converters/EarsToSmtConverter';

describe('EarsToSmtConverter', () => {
  let converter: EarsToSmtConverter;

  beforeEach(() => {
    converter = new EarsToSmtConverter();
  });

  describe('constructor', () => {
    it('should create instance with default options', () => {
      const defaultConverter = new EarsToSmtConverter();
      expect(defaultConverter).toBeInstanceOf(EarsToSmtConverter);
    });

    it('should create instance with custom options', () => {
      const customConverter = new EarsToSmtConverter({
        strict: true,
        inferTypes: false,
        debug: true,
      });
      expect(customConverter).toBeInstanceOf(EarsToSmtConverter);
    });
  });

  describe('parseEarsPattern', () => {
    describe('Ubiquitous pattern', () => {
      it('should parse basic ubiquitous pattern', () => {
        const pattern = converter.parseEarsPattern(
          'THE system SHALL validate all user inputs'
        );
        expect(pattern).not.toBeNull();
        expect(pattern?.type).toBe('ubiquitous');
        expect(pattern?.system).toBe('system');
        expect(pattern?.requirement).toBe('validate all user inputs');
      });

      it('should handle complex system names', () => {
        const pattern = converter.parseEarsPattern(
          'THE payment processing module SHALL encrypt all data'
        );
        expect(pattern?.type).toBe('ubiquitous');
        expect(pattern?.system).toBe('payment processing module');
      });
    });

    describe('Event-driven pattern', () => {
      it('should parse event-driven pattern', () => {
        const pattern = converter.parseEarsPattern(
          'WHEN user clicks submit, THE system SHALL save the data'
        );
        expect(pattern).not.toBeNull();
        expect(pattern?.type).toBe('event-driven');
        expect(pattern?.event).toBe('user clicks submit');
        expect(pattern?.system).toBe('system');
        expect(pattern?.requirement).toBe('save the data');
      });

      it('should handle event without comma', () => {
        const pattern = converter.parseEarsPattern(
          'WHEN timeout occurs THE system SHALL retry the request'
        );
        expect(pattern?.type).toBe('event-driven');
        expect(pattern?.event).toBe('timeout occurs');
      });
    });

    describe('State-driven pattern', () => {
      it('should parse state-driven pattern', () => {
        const pattern = converter.parseEarsPattern(
          'WHILE user is logged in, THE system SHALL display the dashboard'
        );
        expect(pattern).not.toBeNull();
        expect(pattern?.type).toBe('state-driven');
        expect(pattern?.state).toBe('user is logged in');
        expect(pattern?.system).toBe('system');
        expect(pattern?.requirement).toBe('display the dashboard');
      });
    });

    describe('Unwanted pattern', () => {
      it('should parse unwanted pattern', () => {
        const pattern = converter.parseEarsPattern(
          'THE system SHALL NOT expose sensitive data in logs'
        );
        expect(pattern).not.toBeNull();
        expect(pattern?.type).toBe('unwanted');
        expect(pattern?.system).toBe('system');
        expect(pattern?.requirement).toBe('expose sensitive data in logs');
        expect(pattern?.negated).toBe(true);
      });
    });

    describe('Optional pattern', () => {
      it('should parse optional pattern', () => {
        const pattern = converter.parseEarsPattern(
          'IF payment amount exceeds 10000, THEN THE system SHALL require additional verification'
        );
        expect(pattern).not.toBeNull();
        expect(pattern?.type).toBe('optional');
        expect(pattern?.condition).toBe('payment amount exceeds 10000');
        expect(pattern?.system).toBe('system');
        expect(pattern?.requirement).toBe('require additional verification');
      });
    });

    describe('Invalid patterns', () => {
      it('should return null for invalid pattern', () => {
        const pattern = converter.parseEarsPattern(
          'This is not an EARS pattern'
        );
        expect(pattern).toBeNull();
      });

      it('should return null for empty string', () => {
        const pattern = converter.parseEarsPattern('');
        expect(pattern).toBeNull();
      });
    });
  });

  describe('convert', () => {
    it('should convert ubiquitous pattern to SMT', () => {
      const result = converter.convert(
        'THE system SHALL validate all user inputs'
      );
      expect(result.success).toBe(true);
      expect(result.formula).toBeDefined();
      expect(result.formula?.smtLib2).toContain('(set-logic ALL)');
      expect(result.formula?.smtLib2).toContain('declare-const');
      expect(result.formula?.smtLib2).toContain('(check-sat)');
    });

    it('should convert event-driven pattern to SMT', () => {
      const result = converter.convert(
        'WHEN user clicks submit, THE system SHALL save the data'
      );
      expect(result.success).toBe(true);
      expect(result.formula?.metadata.earsPattern.type).toBe('event-driven');
    });

    it('should convert state-driven pattern to SMT', () => {
      const result = converter.convert(
        'WHILE user is logged in, THE system SHALL display the dashboard'
      );
      expect(result.success).toBe(true);
      expect(result.formula?.metadata.earsPattern.type).toBe('state-driven');
    });

    it('should convert unwanted pattern to SMT', () => {
      const result = converter.convert(
        'THE system SHALL NOT expose sensitive data'
      );
      expect(result.success).toBe(true);
      expect(result.formula?.metadata.earsPattern.type).toBe('unwanted');
      expect(result.formula?.smtLib2).toContain('not');
    });

    it('should convert optional pattern to SMT', () => {
      const result = converter.convert(
        'IF payment exceeds limit, THEN THE system SHALL require approval'
      );
      expect(result.success).toBe(true);
      expect(result.formula?.metadata.earsPattern.type).toBe('optional');
    });

    it('should return error for invalid pattern', () => {
      const result = converter.convert('Not an EARS pattern');
      expect(result.success).toBe(false);
      expect(result.error).toBeDefined();
    });

    it('should include transformation rules in metadata', () => {
      const result = converter.convert(
        'THE system SHALL process requests'
      );
      expect(result.success).toBe(true);
      expect(result.formula?.metadata.transformationRules.length).toBeGreaterThan(0);
    });

    it('should record duration', () => {
      const result = converter.convert(
        'THE system SHALL validate inputs'
      );
      expect(result.duration).toBeGreaterThanOrEqual(0);
    });
  });

  describe('convertMultiple', () => {
    it('should convert multiple requirements', () => {
      const requirements = [
        'THE system SHALL validate inputs',
        'WHEN error occurs, THE system SHALL log the error',
        'THE system SHALL NOT crash',
      ];
      const results = converter.convertMultiple(requirements);
      expect(results.length).toBe(3);
      expect(results.filter(r => r.success).length).toBe(3);
    });
  });

  describe('getSupportedPatterns', () => {
    it('should return all supported pattern types', () => {
      const patterns = converter.getSupportedPatterns();
      expect(patterns).toContain('ubiquitous');
      expect(patterns).toContain('event-driven');
      expect(patterns).toContain('state-driven');
      expect(patterns).toContain('unwanted');
      expect(patterns).toContain('optional');
      expect(patterns.length).toBe(5);
    });
  });

  describe('getPatternExamples', () => {
    it('should return examples for all patterns', () => {
      const examples = converter.getPatternExamples();
      expect(Object.keys(examples).length).toBe(5);
      expect(examples['ubiquitous']).toContain('SHALL');
      expect(examples['event-driven']).toContain('WHEN');
      expect(examples['state-driven']).toContain('WHILE');
      expect(examples['unwanted']).toContain('SHALL NOT');
      expect(examples['optional']).toContain('IF');
    });
  });
});
