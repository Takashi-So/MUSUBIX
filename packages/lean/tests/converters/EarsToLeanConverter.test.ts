/**
 * @fileoverview Unit tests for EarsToLeanConverter
 * @module @nahisaho/musubix-lean/tests/converters/EarsToLeanConverter
 * @traceability REQ-LEAN-CONV-001 to REQ-LEAN-CONV-005
 */

import { describe, it, expect } from 'vitest';
import {
  parseEarsRequirement,
  EarsToLeanConverter,
} from '../../src/converters/EarsToLeanConverter.ts';
import type { EarsRequirement, EarsParsedComponents } from '../../src/types.ts';

describe('EarsToLeanConverter', () => {
  describe('parseEarsRequirement', () => {
    describe('Ubiquitous pattern', () => {
      it('should parse basic ubiquitous requirement', () => {
        const result = parseEarsRequirement('THE system SHALL validate input');
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.pattern).toBe('ubiquitous');
          expect(result.value.subject).toBe('system');
          expect(result.value.action).toBe('validate input');
          expect(result.value.negated).toBe(false);
        }
      });

      it('should handle complex subject', () => {
        const result = parseEarsRequirement('THE authentication service SHALL verify credentials');
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.subject).toBe('authentication service');
        }
      });
    });

    describe('Event-driven pattern', () => {
      it('should parse event-driven requirement with comma', () => {
        const result = parseEarsRequirement('WHEN user submits form, THE system SHALL validate data');
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.pattern).toBe('event-driven');
          expect(result.value.trigger).toBe('user submits form');
          expect(result.value.subject).toBe('system');
          expect(result.value.action).toBe('validate data');
        }
      });

      it('should parse event-driven requirement without comma', () => {
        const result = parseEarsRequirement('WHEN button is clicked THE ui SHALL update display');
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.pattern).toBe('event-driven');
        }
      });
    });

    describe('State-driven pattern', () => {
      it('should parse state-driven requirement', () => {
        const result = parseEarsRequirement('WHILE system is in maintenance mode, THE api SHALL return 503');
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.pattern).toBe('state-driven');
          expect(result.value.state).toBe('system is in maintenance mode');
          expect(result.value.action).toBe('return 503');
        }
      });
    });

    describe('Unwanted pattern', () => {
      it('should parse unwanted requirement', () => {
        const result = parseEarsRequirement('THE system SHALL NOT expose sensitive data');
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.pattern).toBe('unwanted');
          expect(result.value.negated).toBe(true);
          expect(result.value.action).toBe('expose sensitive data');
        }
      });
    });

    describe('Optional pattern', () => {
      it('should parse optional requirement', () => {
        const result = parseEarsRequirement('IF user is admin, THEN THE system SHALL show admin panel');
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.pattern).toBe('optional');
          expect(result.value.condition).toBe('user is admin');
          expect(result.value.action).toBe('show admin panel');
        }
      });
    });

    describe('Error cases', () => {
      it('should return error for invalid text', () => {
        const result = parseEarsRequirement('This is not EARS format');
        expect(result.isErr()).toBe(true);
      });

      it('should return error for empty string', () => {
        const result = parseEarsRequirement('');
        expect(result.isErr()).toBe(true);
      });
    });
  });

  describe('EarsToLeanConverter class', () => {
    const converter = new EarsToLeanConverter();

    describe('convert', () => {
      it('should convert ubiquitous requirement to theorem', () => {
        const parsed: EarsParsedComponents = {
          pattern: 'ubiquitous',
          subject: 'system',
          action: 'validate all input',
          negated: false,
        };
        const req: EarsRequirement = {
          id: 'REQ-001',
          pattern: 'ubiquitous',
          text: 'THE system SHALL validate all input',
          parsed,
        };
        const result = converter.convert(req);
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.id).toBe('REQ-001');
          expect(result.value.requirementId).toBe('REQ-001');
          expect(result.value.leanCode).toContain('theorem');
        }
      });

      it('should convert event-driven requirement to theorem', () => {
        const parsed: EarsParsedComponents = {
          pattern: 'event-driven',
          trigger: 'user logs in',
          subject: 'system',
          action: 'create session',
          negated: false,
        };
        const req: EarsRequirement = {
          id: 'REQ-002',
          pattern: 'event-driven',
          text: 'WHEN user logs in, THE system SHALL create session',
          parsed,
        };
        const result = converter.convert(req);
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.hypotheses.length).toBeGreaterThan(0);
        }
      });

      it('should convert unwanted requirement to theorem with negation', () => {
        const parsed: EarsParsedComponents = {
          pattern: 'unwanted',
          subject: 'system',
          action: 'allow unauthorized access',
          negated: true,
        };
        const req: EarsRequirement = {
          id: 'REQ-003',
          pattern: 'unwanted',
          text: 'THE system SHALL NOT allow unauthorized access',
          parsed,
        };
        const result = converter.convert(req);
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.leanCode).toContain('¬');
        }
      });

      it('should return error when parsed components are missing', () => {
        const req: EarsRequirement = {
          id: 'REQ-004',
          pattern: 'ubiquitous',
          text: 'THE system SHALL validate',
          // parsed is missing
        };
        const result = converter.convert(req);
        expect(result.isErr()).toBe(true);
      });
    });

    describe('parseEars', () => {
      it('should parse EARS text into components', () => {
        const result = converter.parseEars('THE system SHALL process requests');
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.pattern).toBe('ubiquitous');
        }
      });

      it('should return error for invalid text', () => {
        const result = converter.parseEars('This is not valid');
        expect(result.isErr()).toBe(true);
      });
    });

    describe('buildTheorem', () => {
      it('should build theorem from parsed components', () => {
        const components: EarsParsedComponents = {
          pattern: 'ubiquitous',
          subject: 'system',
          action: 'validate input',
          negated: false,
        };
        const theorem = converter.buildTheorem(components, 'REQ-001', 'THE system SHALL validate input');
        expect(theorem.name).toContain('req_req_001');
        expect(theorem.requirementId).toBe('REQ-001');
        expect(theorem.leanCode).toContain('theorem');
      });
    });

    describe('convertBatch', () => {
      it('should convert multiple requirements', () => {
        const reqs: EarsRequirement[] = [
          {
            id: 'REQ-001',
            pattern: 'ubiquitous',
            text: 'THE system SHALL validate input',
            parsed: { pattern: 'ubiquitous', subject: 'system', action: 'validate input', negated: false },
          },
          {
            id: 'REQ-002',
            pattern: 'ubiquitous',
            text: 'THE system SHALL log events',
            parsed: { pattern: 'ubiquitous', subject: 'system', action: 'log events', negated: false },
          },
        ];
        const { successes, failures } = converter.convertBatch(reqs);
        expect(successes).toHaveLength(2);
        expect(failures).toHaveLength(0);
      });

      it('should handle partial failures', () => {
        const reqs: EarsRequirement[] = [
          {
            id: 'REQ-001',
            pattern: 'ubiquitous',
            text: 'THE system SHALL validate input',
            parsed: { pattern: 'ubiquitous', subject: 'system', action: 'validate input', negated: false },
          },
          {
            id: 'REQ-002',
            pattern: 'ubiquitous',
            text: 'Invalid requirement',
            // parsed is missing - will fail
          },
        ];
        const { successes, failures } = converter.convertBatch(reqs);
        expect(successes).toHaveLength(1);
        expect(failures).toHaveLength(1);
        expect(failures[0].id).toBe('REQ-002');
      });
    });
  });
});
