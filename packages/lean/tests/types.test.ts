/**
 * @fileoverview Unit tests for type definitions
 * @module @nahisaho/musubix-lean/tests/types
 * @traceability REQ-LEAN-001
 */

import { describe, it, expect } from 'vitest';
import {
  DEFAULT_LEAN_CONFIG,
  type EarsPattern,
  type EarsRequirement,
  type LeanTheorem,
  type LeanProof,
  type LeanConfig,
  type TypeScriptFunction,
  type VerificationResult,
  type TraceabilityLink,
  type HybridVerificationResult,
  type LeanVersion,
} from '../src/types.ts';

describe('Types', () => {
  describe('EarsPattern', () => {
    it('should accept valid EARS patterns', () => {
      const patterns: EarsPattern[] = [
        'ubiquitous',
        'event-driven',
        'state-driven',
        'unwanted',
        'optional',
      ];
      expect(patterns).toHaveLength(5);
    });
  });

  describe('EarsRequirement', () => {
    it('should create valid EARS requirement', () => {
      const req: EarsRequirement = {
        id: 'REQ-001',
        pattern: 'ubiquitous',
        text: 'THE system SHALL validate input',
      };
      expect(req.id).toBe('REQ-001');
      expect(req.pattern).toBe('ubiquitous');
      expect(req.text).toContain('SHALL');
    });

    it('should support parsed components', () => {
      const req: EarsRequirement = {
        id: 'REQ-002',
        pattern: 'event-driven',
        text: 'WHEN user submits form, THE system SHALL validate data',
        parsed: {
          pattern: 'event-driven',
          trigger: 'user submits form',
          subject: 'system',
          action: 'validate data',
          negated: false,
        },
      };
      expect(req.parsed?.trigger).toBe('user submits form');
      expect(req.parsed?.negated).toBe(false);
    });
  });

  describe('LeanTheorem', () => {
    it('should create valid Lean theorem', () => {
      const theorem: LeanTheorem = {
        id: 'THM-001',
        name: 'input_validation_theorem',
        statement: 'input > 0 → output > 0',
        requirementId: 'REQ-001',
        hypotheses: [{ name: 'h_positive', type: 'input > 0' }],
        leanCode: 'theorem input_validation_theorem : input > 0 → output > 0 := by sorry',
      };
      expect(theorem.name).toBe('input_validation_theorem');
      expect(theorem.hypotheses).toHaveLength(1);
    });
  });

  describe('LeanProof', () => {
    it('should create valid Lean proof', () => {
      const proof: LeanProof = {
        id: 'PROOF-001',
        theoremId: 'THM-001',
        tactics: ['intro h', 'exact h'],
        leanCode: 'by intro h; exact h',
        isComplete: true,
        generatedAt: new Date().toISOString(),
      };
      expect(proof.isComplete).toBe(true);
      expect(proof.tactics).toHaveLength(2);
    });
  });

  describe('TypeScriptFunction', () => {
    it('should create valid TypeScript function spec', () => {
      const func: TypeScriptFunction = {
        name: 'validateInput',
        parameters: [{ name: 'input', type: 'number', optional: false }],
        returnType: 'boolean',
        preconditions: [{ expression: 'input > 0', description: 'Input must be positive' }],
        postconditions: [{ expression: 'result === true || result === false', description: 'Returns boolean' }],
        invariants: [],
      };
      expect(func.name).toBe('validateInput');
      expect(func.preconditions).toHaveLength(1);
    });
  });

  describe('VerificationResult', () => {
    it('should create proved verification result', () => {
      const result: VerificationResult = {
        theoremId: 'THM-001',
        status: 'proved',
        errors: [],
        warnings: [],
        duration: 100,
      };
      expect(result.status).toBe('proved');
      expect(result.errors).toHaveLength(0);
    });

    it('should create error verification result', () => {
      const result: VerificationResult = {
        theoremId: 'THM-002',
        status: 'error',
        errors: ['Proof failed', 'Unknown tactic'],
        warnings: [],
        duration: 500,
      };
      expect(result.status).toBe('error');
      expect(result.errors).toHaveLength(2);
    });
  });

  describe('TraceabilityLink', () => {
    it('should create valid traceability link', () => {
      const link: TraceabilityLink = {
        id: 'LINK-001',
        source: 'REQ-001',
        target: 'THM-001',
        type: 'requirement_to_theorem',
        confidence: 0.95,
      };
      expect(link.source).toBe('REQ-001');
      expect(link.confidence).toBeGreaterThan(0.9);
    });
  });

  describe('HybridVerificationResult', () => {
    it('should create verified hybrid result', () => {
      const result: HybridVerificationResult = {
        functionId: 'validateInput',
        combinedStatus: 'verified',
        runtimeResult: {
          passed: true,
          testCount: 10,
          failedTests: [],
          coverage: 100,
          duration: 50,
        },
        formalResult: {
          proved: true,
          errors: [],
          duration: 200,
        },
        coverage: {
          runtimeCoverage: 100,
          formalCoverage: 100,
          combinedCoverage: 100,
        },
      };
      expect(result.combinedStatus).toBe('verified');
      expect(result.coverage.combinedCoverage).toBe(100);
    });
  });

  describe('LeanVersion', () => {
    it('should create valid Lean version', () => {
      const version: LeanVersion = {
        major: 4,
        minor: 3,
        patch: 0,
        full: '4.3.0',
      };
      expect(version.major).toBe(4);
      expect(version.full).toBe('4.3.0');
    });
  });

  describe('LeanConfig', () => {
    it('should have correct default values', () => {
      expect(DEFAULT_LEAN_CONFIG.minVersion).toBe('4.0.0');
      expect(DEFAULT_LEAN_CONFIG.timeout).toBe(30000);
      expect(DEFAULT_LEAN_CONFIG.mathlibEnabled).toBe(false);
      expect(DEFAULT_LEAN_CONFIG.lakeEnabled).toBe(true);
      expect(DEFAULT_LEAN_CONFIG.strategy).toBe('hybrid');
    });

    it('should allow custom configuration', () => {
      const config: LeanConfig = {
        ...DEFAULT_LEAN_CONFIG,
        leanPath: '/custom/path/to/lean',
        mathlibEnabled: true,
        timeout: 60000,
      };
      expect(config.leanPath).toBe('/custom/path/to/lean');
      expect(config.mathlibEnabled).toBe(true);
      expect(config.timeout).toBe(60000);
    });
  });
});
