/**
 * Best Practices Test Suite
 *
 * Tests for the self-learning best practices module
 * Updated with patterns from Project-13 and Project-14
 */
import { describe, it, expect } from 'vitest';
import {
  LEARNED_BEST_PRACTICES,
  getBestPracticesByCategory,
  getBestPracticesByAction,
  getPreferredPatterns,
  getHighConfidencePatterns,
  formatBestPractice,
  generateBestPracticesReport,
  type BestPractice,
} from '../learning/best-practices.js';

describe('Best Practices Module', () => {
  describe('LEARNED_BEST_PRACTICES', () => {
    it('should have at least 10 patterns', () => {
      expect(LEARNED_BEST_PRACTICES.length).toBeGreaterThanOrEqual(10);
    });

    it('should include new patterns from Project-13/14', () => {
      const patternIds = LEARNED_BEST_PRACTICES.map((bp) => bp.id);
      
      // New code patterns
      expect(patternIds).toContain('BP-CODE-004'); // Function-based Value Objects
      expect(patternIds).toContain('BP-CODE-005'); // Result Type
      
      // New design patterns
      expect(patternIds).toContain('BP-DESIGN-006'); // Entity Counter Reset
      expect(patternIds).toContain('BP-DESIGN-007'); // Expiry Time Logic
      
      // New test patterns
      expect(patternIds).toContain('BP-TEST-004'); // Result Type Test Pattern
      expect(patternIds).toContain('BP-TEST-005'); // Status Transition Testing
    });

    it('should have valid structure for all patterns', () => {
      for (const bp of LEARNED_BEST_PRACTICES) {
        expect(bp.id).toMatch(/^BP-(CODE|DESIGN|TEST|REQ)-\d{3}$/);
        expect(bp.name).toBeTruthy();
        expect(['code', 'design', 'test', 'requirement']).toContain(bp.category);
        expect(['prefer', 'avoid', 'suggest']).toContain(bp.action);
        expect(bp.description).toBeTruthy();
        expect(bp.confidence).toBeGreaterThanOrEqual(0);
        expect(bp.confidence).toBeLessThanOrEqual(1);
        expect(bp.source).toBeTruthy();
      }
    });
  });

  describe('getBestPracticesByCategory', () => {
    it('should return code patterns', () => {
      const codePatterns = getBestPracticesByCategory('code');
      expect(codePatterns.length).toBeGreaterThanOrEqual(5);
      expect(codePatterns.every((bp) => bp.category === 'code')).toBe(true);
    });

    it('should return design patterns', () => {
      const designPatterns = getBestPracticesByCategory('design');
      expect(designPatterns.length).toBeGreaterThanOrEqual(7);
      expect(designPatterns.every((bp) => bp.category === 'design')).toBe(true);
    });

    it('should return test patterns', () => {
      const testPatterns = getBestPracticesByCategory('test');
      expect(testPatterns.length).toBeGreaterThanOrEqual(5);
      expect(testPatterns.every((bp) => bp.category === 'test')).toBe(true);
    });
  });

  describe('getBestPracticesByAction', () => {
    it('should return prefer patterns', () => {
      const preferPatterns = getBestPracticesByAction('prefer');
      expect(preferPatterns.length).toBeGreaterThan(0);
      expect(preferPatterns.every((bp) => bp.action === 'prefer')).toBe(true);
    });

    it('should return avoid patterns', () => {
      const avoidPatterns = getBestPracticesByAction('avoid');
      // May be empty if all are prefer/suggest
      expect(avoidPatterns.every((bp) => bp.action === 'avoid')).toBe(true);
    });
  });

  describe('getPreferredPatterns', () => {
    it('should return patterns with action=prefer', () => {
      const preferred = getPreferredPatterns();
      expect(preferred.length).toBeGreaterThan(0);
      expect(preferred.every((bp) => bp.action === 'prefer')).toBe(true);
    });
  });

  describe('getHighConfidencePatterns', () => {
    it('should return patterns with confidence >= 0.9', () => {
      const highConf = getHighConfidencePatterns();
      expect(highConf.length).toBeGreaterThan(0);
      expect(highConf.every((bp) => bp.confidence >= 0.9)).toBe(true);
    });

    it('should include BP-CODE-004 (Function-based Value Objects)', () => {
      const highConf = getHighConfidencePatterns();
      const bp004 = highConf.find((bp) => bp.id === 'BP-CODE-004');
      expect(bp004).toBeDefined();
      expect(bp004?.confidence).toBe(0.95);
    });
  });

  describe('formatBestPractice', () => {
    it('should format a prefer pattern correctly', () => {
      const bp: BestPractice = {
        id: 'BP-TEST-999',
        name: 'Test Pattern',
        category: 'test',
        action: 'prefer',
        description: 'Test description',
        confidence: 0.95,
        source: 'Test source',
      };

      const formatted = formatBestPractice(bp);
      expect(formatted).toContain('✅');
      expect(formatted).toContain('Test Pattern');
      expect(formatted).toContain('95%');
      expect(formatted).toContain('Test description');
    });

    it('should include example if provided', () => {
      const bp: BestPractice = {
        id: 'BP-CODE-999',
        name: 'Example Pattern',
        category: 'code',
        action: 'prefer',
        description: 'Has example',
        example: 'const x = 1;',
        confidence: 0.9,
        source: 'Test',
      };

      const formatted = formatBestPractice(bp);
      expect(formatted).toContain('```typescript');
      expect(formatted).toContain('const x = 1;');
    });
  });

  describe('generateBestPracticesReport', () => {
    it('should generate markdown report', () => {
      const report = generateBestPracticesReport();
      
      expect(report).toContain('# MUSUBIX Learned Best Practices');
      expect(report).toContain('## Code Patterns');
      expect(report).toContain('## Design Patterns');
      expect(report).toContain('## Test Patterns');
      expect(report).toContain('Total Patterns');
      expect(report).toContain('High Confidence');
    });
  });

  describe('New Patterns from P13/P14', () => {
    it('BP-CODE-004 should describe function-based Value Objects', () => {
      const bp = LEARNED_BEST_PRACTICES.find((bp) => bp.id === 'BP-CODE-004');
      expect(bp).toBeDefined();
      expect(bp?.name).toBe('Function-based Value Objects');
      expect(bp?.description).toContain('interface');
      expect(bp?.description).toContain('factory function');
      expect(bp?.source).toContain('Project-13');
      expect(bp?.source).toContain('Project-14');
    });

    it('BP-CODE-005 should describe Result type pattern', () => {
      const bp = LEARNED_BEST_PRACTICES.find((bp) => bp.id === 'BP-CODE-005');
      expect(bp).toBeDefined();
      expect(bp?.name).toBe('Result Type for Fallible Operations');
      expect(bp?.description).toContain('Result<T, E>');
      expect(bp?.example).toContain('isOk()');
      expect(bp?.example).toContain('isErr()');
    });

    it('BP-DESIGN-006 should describe counter reset pattern', () => {
      const bp = LEARNED_BEST_PRACTICES.find((bp) => bp.id === 'BP-DESIGN-006');
      expect(bp).toBeDefined();
      expect(bp?.name).toBe('Entity Counter Reset for Testing');
      expect(bp?.example).toContain('resetEventCounter');
      expect(bp?.example).toContain('beforeEach');
    });

    it('BP-DESIGN-007 should describe expiry time logic', () => {
      const bp = LEARNED_BEST_PRACTICES.find((bp) => bp.id === 'BP-DESIGN-007');
      expect(bp).toBeDefined();
      expect(bp?.name).toBe('Expiry Time Business Logic');
      expect(bp?.example).toContain('expiresAt');
      expect(bp?.example).toContain('isReservationExpired');
    });

    it('BP-TEST-004 should describe Result type testing', () => {
      const bp = LEARNED_BEST_PRACTICES.find((bp) => bp.id === 'BP-TEST-004');
      expect(bp).toBeDefined();
      expect(bp?.name).toBe('Result Type Test Pattern');
      expect(bp?.example).toContain('expect(result.isOk())');
      expect(bp?.example).toContain('expect(result.isErr())');
    });

    it('BP-TEST-005 should describe status transition testing', () => {
      const bp = LEARNED_BEST_PRACTICES.find((bp) => bp.id === 'BP-TEST-005');
      expect(bp).toBeDefined();
      expect(bp?.name).toBe('Status Transition Testing');
      expect(bp?.example).toContain('validTransitions');
    });
  });
});
