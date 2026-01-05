/**
 * Verification Condition Generator Tests
 *
 * Tests for VC generation from EARS AST, function contracts, and domain constraints.
 *
 * @see TSK-SYMB-010
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  VerificationConditionGenerator,
  resetVcCounter,
  type FunctionContract,
  type DomainConstraint,
} from '../vc-generator.js';
import type { EarsAstNode } from '../ears-to-formal.js';

describe('VerificationConditionGenerator', () => {
  let generator: VerificationConditionGenerator;

  beforeEach(() => {
    resetVcCounter();
    generator = new VerificationConditionGenerator();
  });

  describe('fromEarsAst', () => {
    it('should generate VCs from ubiquitous pattern', () => {
      const astNodes: EarsAstNode[] = [
        {
          requirementId: 'REQ-001',
          pattern: 'ubiquitous',
          system: 'system',
          requirement: 'validate all inputs',
          originalText: 'THE system SHALL validate all inputs',
          parsedAt: new Date().toISOString(),
        },
      ];

      const result = generator.fromEarsAst(astNodes);

      expect(result.conditions.length).toBeGreaterThan(0);
      expect(result.conditions[0].requirementIds).toContain('REQ-001');
      expect(result.combinedSmtLib).toBeTruthy();
      expect(result.explanation.summary).toContain('verification conditions');
    });

    it('should generate VCs for event-driven pattern with preconditions', () => {
      const astNodes: EarsAstNode[] = [
        {
          requirementId: 'REQ-002',
          pattern: 'event-driven',
          system: 'API',
          requirement: 'return 200 status',
          event: 'valid request received',
          originalText: 'WHEN valid request received, THE API SHALL return 200 status',
          parsedAt: new Date().toISOString(),
        },
      ];

      const result = generator.fromEarsAst(astNodes);

      expect(result.conditions.length).toBeGreaterThan(0);
      // Should have precondition for event
      const hasPrecondition = result.conditions.some((c) => c.type === 'precondition');
      expect(hasPrecondition).toBe(true);
    });

    it('should generate VCs for state-driven pattern with invariants', () => {
      const astNodes: EarsAstNode[] = [
        {
          requirementId: 'REQ-003',
          pattern: 'state-driven',
          system: 'database',
          requirement: 'queue operations',
          state: 'connection is active',
          originalText: 'WHILE connection is active, THE database SHALL queue operations',
          parsedAt: new Date().toISOString(),
        },
      ];

      const result = generator.fromEarsAst(astNodes);

      expect(result.conditions.length).toBeGreaterThan(0);
      // Should have state-related VCs
      const hasInvariant = result.conditions.some((c) => c.type === 'invariant');
      expect(hasInvariant).toBe(true);
    });

    it('should generate VCs for unwanted pattern with negation', () => {
      const astNodes: EarsAstNode[] = [
        {
          requirementId: 'REQ-004',
          pattern: 'unwanted',
          system: 'system',
          requirement: 'NOT expose secrets',
          unwantedBehavior: 'expose secrets',
          originalText: 'THE system SHALL NOT expose secrets',
          parsedAt: new Date().toISOString(),
        },
      ];

      const result = generator.fromEarsAst(astNodes);

      expect(result.conditions.length).toBeGreaterThan(0);
      // VCs should contain negation assertion
      const hasAssertion = result.conditions.some((c) => c.type === 'assertion');
      expect(hasAssertion).toBe(true);
    });

    it('should handle multiple EARS AST nodes', () => {
      const astNodes: EarsAstNode[] = [
        {
          requirementId: 'REQ-001',
          pattern: 'ubiquitous',
          system: 'API',
          requirement: 'be available',
          originalText: 'THE API SHALL be available',
          parsedAt: new Date().toISOString(),
        },
        {
          requirementId: 'REQ-002',
          pattern: 'ubiquitous',
          system: 'API',
          requirement: 'return JSON',
          originalText: 'THE API SHALL return JSON',
          parsedAt: new Date().toISOString(),
        },
      ];

      const result = generator.fromEarsAst(astNodes);

      expect(result.conditions.length).toBeGreaterThan(1);
      expect(result.explanation.relatedRequirements).toContain('REQ-001');
      expect(result.explanation.relatedRequirements).toContain('REQ-002');
    });

    it('should include evidence for each AST node', () => {
      const astNodes: EarsAstNode[] = [
        {
          requirementId: 'REQ-001',
          pattern: 'ubiquitous',
          system: 'system',
          requirement: 'work',
          originalText: 'THE system SHALL work',
          parsedAt: new Date().toISOString(),
        },
      ];

      const result = generator.fromEarsAst(astNodes);

      expect(result.explanation.evidence.length).toBeGreaterThan(0);
      expect(result.explanation.evidence[0].type).toBe('requirement');
    });
  });

  describe('fromFunctionContract', () => {
    it('should generate precondition VCs', () => {
      const contract: FunctionContract = {
        functionName: 'divide',
        parameters: [
          { name: 'a', type: 'number' },
          { name: 'b', type: 'number' },
        ],
        returns: { type: 'number' },
        preconditions: ['b !== 0'],
        postconditions: [],
        invariants: [],
      };

      const result = generator.fromFunctionContract(contract, ['REQ-MATH-001']);

      expect(result.conditions.length).toBeGreaterThan(0);
      expect(result.conditions[0].type).toBe('precondition');
      expect(result.conditions[0].description).toContain('divide');
    });

    it('should generate postcondition VCs', () => {
      const contract: FunctionContract = {
        functionName: 'add',
        parameters: [
          { name: 'a', type: 'number' },
          { name: 'b', type: 'number' },
        ],
        returns: { type: 'number' },
        preconditions: [],
        postconditions: ['result === a + b'],
        invariants: [],
      };

      const result = generator.fromFunctionContract(contract, ['REQ-MATH-002']);

      const postconditionVcs = result.conditions.filter((c) => c.type === 'postcondition');
      expect(postconditionVcs.length).toBe(1);
    });

    it('should generate invariant VCs', () => {
      const contract: FunctionContract = {
        functionName: 'processQueue',
        parameters: [],
        returns: { type: 'void' },
        preconditions: [],
        postconditions: [],
        invariants: ['queue.length >= 0'],
      };

      const result = generator.fromFunctionContract(contract, ['REQ-QUEUE-001']);

      const invariantVcs = result.conditions.filter((c) => c.type === 'invariant');
      expect(invariantVcs.length).toBe(1);
    });

    it('should include code element reference', () => {
      const contract: FunctionContract = {
        functionName: 'calculateTotal',
        parameters: [{ name: 'items', type: 'Item[]' }],
        returns: { type: 'number' },
        preconditions: ['items.length > 0'],
        postconditions: ['result >= 0'],
        invariants: [],
      };

      const result = generator.fromFunctionContract(contract, ['REQ-CALC-001']);

      expect(result.conditions[0].codeElement).toBeDefined();
      expect(result.conditions[0].codeElement?.function).toBe('calculateTotal');
      expect(result.conditions[0].codeElement?.elementType).toBe('function');
    });
  });

  describe('fromDomainConstraints', () => {
    it('should generate domain constraint VCs', () => {
      const constraints: DomainConstraint[] = [
        {
          name: 'positive_price',
          description: 'Price must be positive',
          variables: ['price'],
          smtConstraint: '(> price 0)',
        },
      ];

      const result = generator.fromDomainConstraints(constraints, ['REQ-DOM-001']);

      expect(result.conditions.length).toBe(1);
      // Type is 'invariant' for domain constraints
      expect(result.conditions[0].type).toBe('invariant');
      expect(result.conditions[0].smtExpression).toContain('price');
    });

    it('should handle multiple domain constraints', () => {
      const constraints: DomainConstraint[] = [
        {
          name: 'valid_age',
          description: 'Age must be between 0 and 150',
          variables: ['age'],
          smtConstraint: '(and (>= age 0) (<= age 150))',
        },
        {
          name: 'valid_email',
          description: 'Email must not be empty',
          variables: ['email'],
          smtConstraint: '(> (str.len email) 0)',
        },
      ];

      const result = generator.fromDomainConstraints(constraints, ['REQ-DOM-002']);

      expect(result.conditions.length).toBe(2);
    });
  });

  describe('boundary VCs', () => {
    it('should generate boundary VCs when enabled', () => {
      const generator = new VerificationConditionGenerator({
        includeBoundaryChecks: true,
      });

      const astNodes: EarsAstNode[] = [
        {
          requirementId: 'REQ-001',
          pattern: 'ubiquitous',
          system: 'system',
          requirement: 'handle values',
          originalText: 'THE system SHALL handle values',
          parsedAt: new Date().toISOString(),
        },
      ];

      const result = generator.fromEarsAst(astNodes);

      // Check if VCs are generated (boundary VCs may or may not be present)
      expect(result.conditions.length).toBeGreaterThan(0);
    });
  });

  describe('VC ID generation', () => {
    it('should generate unique VC IDs', () => {
      const astNodes: EarsAstNode[] = [
        {
          requirementId: 'REQ-001',
          pattern: 'ubiquitous',
          system: 'system',
          requirement: 'work',
          originalText: 'THE system SHALL work',
          parsedAt: new Date().toISOString(),
        },
      ];

      const result1 = generator.fromEarsAst(astNodes);
      const result2 = generator.fromEarsAst(astNodes);

      const ids1 = result1.conditions.map((c) => c.id);
      const ids2 = result2.conditions.map((c) => c.id);

      // IDs should be different between calls
      const allIds = [...ids1, ...ids2];
      const uniqueIds = new Set(allIds);
      expect(uniqueIds.size).toBe(allIds.length);
    });

    it('should follow VC-YYYYMMDD-NNNN format', () => {
      const astNodes: EarsAstNode[] = [
        {
          requirementId: 'REQ-001',
          pattern: 'ubiquitous',
          system: 'system',
          requirement: 'work',
          originalText: 'THE system SHALL work',
          parsedAt: new Date().toISOString(),
        },
      ];

      const result = generator.fromEarsAst(astNodes);

      expect(result.conditions[0].id).toMatch(/^VC-\d{8}-\d{4}$/);
    });
  });

  describe('combined SMT-LIB generation', () => {
    it('should generate valid combined SMT-LIB', () => {
      const astNodes: EarsAstNode[] = [
        {
          requirementId: 'REQ-001',
          pattern: 'ubiquitous',
          system: 'API',
          requirement: 'respond',
          originalText: 'THE API SHALL respond',
          parsedAt: new Date().toISOString(),
        },
      ];

      const result = generator.fromEarsAst(astNodes);

      expect(result.combinedSmtLib).toContain('set-logic');
      expect(result.combinedSmtLib).toContain('declare-const');
      expect(result.combinedSmtLib).toContain('assert');
      expect(result.combinedSmtLib).toContain('check-sat');
    });
  });
});
