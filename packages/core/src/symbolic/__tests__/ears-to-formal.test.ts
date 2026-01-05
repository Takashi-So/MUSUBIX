/**
 * EARS to Formal Spec Converter Tests
 *
 * Tests for EARS requirement parsing and SMT-LIB generation.
 *
 * @see TSK-SYMB-009
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  EarsToFormalSpecConverter,
  parseEarsRequirement,
  generateSmtLib,
  type EarsAstNode,
} from '../ears-to-formal.js';

describe('EarsToFormalSpecConverter', () => {
  let converter: EarsToFormalSpecConverter;

  beforeEach(() => {
    converter = new EarsToFormalSpecConverter();
  });

  describe('parseEarsRequirement', () => {
    it('should parse ubiquitous pattern (THE system SHALL requirement)', () => {
      const result = parseEarsRequirement(
        'REQ-001',
        'THE system SHALL validate all user inputs',
      );

      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.ast.pattern).toBe('ubiquitous');
        expect(result.ast.system).toBe('system');
        expect(result.ast.requirement).toBe('validate all user inputs');
        expect(result.ast.requirementId).toBe('REQ-001');
      }
    });

    it('should parse event-driven pattern (WHEN event, THE system SHALL response)', () => {
      const result = parseEarsRequirement(
        'REQ-002',
        'WHEN user clicks submit, THE system SHALL save the form data',
      );

      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.ast.pattern).toBe('event-driven');
        expect(result.ast.event).toBe('user clicks submit');
        expect(result.ast.system).toBe('system');
        expect(result.ast.requirement).toBe('save the form data');
      }
    });

    it('should parse state-driven pattern (WHILE state, THE system SHALL response)', () => {
      const result = parseEarsRequirement(
        'REQ-003',
        'WHILE system is in maintenance mode, THE API SHALL return 503 status',
      );

      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.ast.pattern).toBe('state-driven');
        expect(result.ast.state).toBe('system is in maintenance mode');
        expect(result.ast.system).toBe('API');
        expect(result.ast.requirement).toBe('return 503 status');
      }
    });

    it('should parse unwanted pattern (THE system SHALL NOT behavior)', () => {
      const result = parseEarsRequirement(
        'REQ-004',
        'THE system SHALL NOT store passwords in plain text',
      );

      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.ast.pattern).toBe('unwanted');
        expect(result.ast.system).toBe('system');
        expect(result.ast.unwantedBehavior).toBe('store passwords in plain text');
      }
    });

    it('should parse optional pattern (IF condition, THEN THE system SHALL response)', () => {
      const result = parseEarsRequirement(
        'REQ-005',
        'IF user is premium, THEN THE system SHALL provide advanced features',
      );

      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.ast.pattern).toBe('optional');
        expect(result.ast.condition).toBe('user is premium');
        expect(result.ast.system).toBe('system');
        expect(result.ast.requirement).toBe('provide advanced features');
      }
    });

    it('should return error for non-EARS format', () => {
      const result = parseEarsRequirement('REQ-006', 'The system should work properly');

      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.error).toContain('EARS pattern');
      }
    });

    it('should be case-insensitive for keywords', () => {
      const result = parseEarsRequirement(
        'REQ-007',
        'the System shall Process all requests',
      );

      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.ast.pattern).toBe('ubiquitous');
      }
    });
  });

  describe('generateSmtLib', () => {
    it('should generate SMT-LIB for ubiquitous pattern', () => {
      const ast: EarsAstNode = {
        requirementId: 'REQ-001',
        pattern: 'ubiquitous',
        system: 'system',
        requirement: 'validate inputs',
        originalText: 'THE system SHALL validate inputs',
        parsedAt: new Date().toISOString(),
      };

      const result = generateSmtLib(ast);

      expect(result.smtLib).toContain('REQ-001');
      expect(result.smtLib).toContain('declare-const');
      expect(result.requirementId).toBe('REQ-001');
      expect(result.variables.length).toBeGreaterThan(0);
      expect(result.assertions.length).toBeGreaterThan(0);
    });

    it('should generate SMT-LIB for event-driven pattern with implication', () => {
      const ast: EarsAstNode = {
        requirementId: 'REQ-002',
        pattern: 'event-driven',
        system: 'system',
        requirement: 'respond quickly',
        event: 'user clicks',
        originalText: 'WHEN user clicks, THE system SHALL respond quickly',
        parsedAt: new Date().toISOString(),
      };

      const result = generateSmtLib(ast);

      expect(result.smtLib).toContain('user_clicks');
      // Event-driven pattern should have implication logic
      expect(result.assertions.length).toBeGreaterThan(0);
    });

    it('should generate SMT-LIB for unwanted pattern with negation', () => {
      const ast: EarsAstNode = {
        requirementId: 'REQ-003',
        pattern: 'unwanted',
        system: 'system',
        requirement: 'NOT store plaintext',
        unwantedBehavior: 'store plaintext',
        originalText: 'THE system SHALL NOT store plaintext',
        parsedAt: new Date().toISOString(),
      };

      const result = generateSmtLib(ast);

      expect(result.smtLib).toContain('not');
    });

    it('should include explanation with reasoning', () => {
      const ast: EarsAstNode = {
        requirementId: 'REQ-004',
        pattern: 'ubiquitous',
        system: 'API',
        requirement: 'return JSON',
        originalText: 'THE API SHALL return JSON',
        parsedAt: new Date().toISOString(),
      };

      const result = generateSmtLib(ast);

      expect(result.explanation.summary).toContain('SMT-LIB');
      expect(result.explanation.reasoning.length).toBeGreaterThan(0);
      expect(result.explanation.relatedRequirements).toContain('REQ-004');
    });
  });

  describe('EarsToFormalSpecConverter class', () => {
    it('should parse requirements using parse method', () => {
      const result = converter.parse('REQ-001', 'THE system SHALL work');

      expect(result.success).toBe(true);
    });

    it('should convert single requirement to SMT-LIB', () => {
      const result = converter.convert({
        id: 'REQ-001',
        text: 'THE system SHALL validate inputs',
        type: 'ubiquitous',
      });

      expect(result.smtLib).toBeTruthy();
      expect(result.requirementId).toBe('REQ-001');
    });

    it('should handle parse errors gracefully in convert', () => {
      const result = converter.convert({
        id: 'REQ-INVALID',
        text: 'This is not EARS format',
        type: 'ubiquitous',
      });

      expect(result.smtLib).toContain('Error');
      expect(result.explanation.summary).toContain('Failed');
    });

    it('should convert multiple requirements', () => {
      const requirements = [
        { id: 'REQ-001', text: 'THE system SHALL validate inputs', type: 'ubiquitous' as const },
        { id: 'REQ-002', text: 'WHEN error occurs, THE system SHALL log it', type: 'event-driven' as const },
      ];

      const result = converter.convertAll(requirements);

      expect(result.astNodes.length).toBe(2);
      expect(result.smtOutputs.length).toBe(2);
      expect(result.combinedSmtLib).toContain('REQ-001');
      expect(result.combinedSmtLib).toContain('REQ-002');
    });

    it('should generate combined SMT-LIB with all requirements', () => {
      const requirements = [
        { id: 'REQ-001', text: 'THE API SHALL return JSON', type: 'ubiquitous' as const },
        { id: 'REQ-002', text: 'THE API SHALL NOT leak secrets', type: 'unwanted' as const },
      ];

      const result = converter.convertAll(requirements);

      expect(result.combinedSmtLib).toContain('Combined');
      expect(result.combinedSmtLib).toContain('check-sat');
      expect(result.explanation.relatedRequirements).toContain('REQ-001');
      expect(result.explanation.relatedRequirements).toContain('REQ-002');
    });
  });
});
