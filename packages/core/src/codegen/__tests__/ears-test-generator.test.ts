/**
 * EARS Test Generator Tests
 *
 * Tests for the EARS requirement to test case generator.
 *
 * @see REQ-TST-001 - EARS Test Generation
 */

import { describe, it, expect } from 'vitest';
import {
  EarsTestGenerator,
  createEarsTestGenerator,
  type EarsRequirement,
} from '../unit-test-generator.js';

describe('EarsTestGenerator', () => {
  describe('createEarsTestGenerator', () => {
    it('should create an instance with default config', () => {
      const generator = createEarsTestGenerator();
      expect(generator).toBeInstanceOf(EarsTestGenerator);
    });

    it('should create an instance with custom config', () => {
      const generator = createEarsTestGenerator({ framework: 'vitest' });
      expect(generator).toBeInstanceOf(EarsTestGenerator);
    });
  });

  describe('generateFromRequirements', () => {
    const generator = createEarsTestGenerator({ framework: 'vitest' });

    it('should generate tests for UBIQUITOUS requirements', () => {
      const requirements: EarsRequirement[] = [
        {
          id: 'REQ-001',
          type: 'ubiquitous',
          text: 'THE system SHALL validate user input',
          system: 'system',
          response: 'validate user input',
        },
      ];

      const tests = generator.generateFromRequirements(requirements);
      expect(tests.length).toBeGreaterThan(0);
      expect(tests[0].requirementId).toBe('REQ-001');
      expect(tests[0].testType).toBe('positive');
    });

    it('should generate tests for EVENT-DRIVEN requirements', () => {
      const requirements: EarsRequirement[] = [
        {
          id: 'REQ-002',
          type: 'event-driven',
          text: 'WHEN user submits form, THE system SHALL save data',
          event: 'user submits form',
          response: 'save data',
        },
      ];

      const tests = generator.generateFromRequirements(requirements);
      expect(tests.length).toBeGreaterThanOrEqual(2);
      expect(tests.some((t) => t.testType === 'positive')).toBe(true);
      expect(tests.some((t) => t.testType === 'negative')).toBe(true);
    });

    it('should generate tests for STATE-DRIVEN requirements', () => {
      const requirements: EarsRequirement[] = [
        {
          id: 'REQ-003',
          type: 'state-driven',
          text: 'WHILE in editing mode, THE system SHALL auto-save',
          state: 'editing mode',
          response: 'auto-save',
        },
      ];

      const tests = generator.generateFromRequirements(requirements);
      expect(tests.length).toBeGreaterThanOrEqual(2);
      // Should include status transition test (BP-TEST-005)
      expect(tests.some((t) => t.testName.includes('status transition'))).toBe(true);
    });

    it('should generate tests for UNWANTED requirements', () => {
      const requirements: EarsRequirement[] = [
        {
          id: 'REQ-004',
          type: 'unwanted',
          text: 'THE system SHALL NOT expose sensitive data',
        },
      ];

      const tests = generator.generateFromRequirements(requirements);
      expect(tests.length).toBeGreaterThan(0);
      expect(tests[0].testType).toBe('negative');
      // Should include Result.err test (BP-TEST-004)
      expect(tests.some((t) => t.assertion.includes('isErr'))).toBe(true);
    });

    it('should generate tests for OPTIONAL requirements', () => {
      const requirements: EarsRequirement[] = [
        {
          id: 'REQ-005',
          type: 'optional',
          text: 'IF user is premium, THEN THE system SHALL unlock features',
          condition: 'user is premium',
          response: 'unlock features',
        },
      ];

      const tests = generator.generateFromRequirements(requirements);
      expect(tests.length).toBeGreaterThanOrEqual(2);
      expect(tests.some((t) => t.testType === 'positive')).toBe(true);
      expect(tests.some((t) => t.testType === 'negative')).toBe(true);
    });
  });

  describe('generateTestFileContent', () => {
    const generator = createEarsTestGenerator({ framework: 'vitest' });

    it('should generate valid test file content', () => {
      const requirements: EarsRequirement[] = [
        {
          id: 'REQ-001',
          type: 'ubiquitous',
          text: 'THE system SHALL validate input',
        },
        {
          id: 'REQ-002',
          type: 'event-driven',
          text: 'WHEN button clicked, THE system SHALL submit',
          event: 'button clicked',
        },
      ];

      const tests = generator.generateFromRequirements(requirements);
      const content = generator.generateTestFileContent(tests, 'myModule');

      expect(content).toContain("import { describe, it, expect, beforeEach } from 'vitest'");
      expect(content).toContain("describe('myModule'");
      expect(content).toContain("describe('REQ-001'");
      expect(content).toContain("describe('REQ-002'");
      expect(content).toContain('beforeEach');
      // Should include BP-TEST-001 comment
      expect(content).toContain('BP-TEST-001');
    });

    it('should include Result type test patterns (BP-TEST-004)', () => {
      const requirements: EarsRequirement[] = [
        {
          id: 'REQ-001',
          type: 'ubiquitous',
          text: 'THE system SHALL create entity',
        },
      ];

      const tests = generator.generateFromRequirements(requirements);
      expect(tests.some((t) => t.assertion.includes('isOk()'))).toBe(true);
    });
  });
});
