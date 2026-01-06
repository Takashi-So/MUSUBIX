/**
 * PreconditionVerifier Unit Tests
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { PreconditionVerifier } from '../../src/verifiers/PreconditionVerifier';
import type { Z3Client, Z3Result } from '../../src/z3/types';
import type { PreconditionInput } from '../../src/verifiers/types';

// Mock Z3Client
function createMockZ3Client(overrides: Partial<Z3Client> = {}): Z3Client {
  return {
    initialize: vi.fn().mockResolvedValue(undefined),
    isAvailable: vi.fn().mockReturnValue(true),
    dispose: vi.fn().mockResolvedValue(undefined),
    checkSat: vi.fn().mockResolvedValue('sat' as Z3Result),
    getModel: vi.fn().mockResolvedValue(new Map()),
    getProof: vi.fn().mockResolvedValue(undefined),
    ...overrides,
  };
}

describe('PreconditionVerifier', () => {
  let verifier: PreconditionVerifier;
  let mockZ3: Z3Client;

  beforeEach(() => {
    mockZ3 = createMockZ3Client();
    verifier = new PreconditionVerifier(mockZ3);
  });

  describe('constructor', () => {
    it('should create instance with Z3 client', () => {
      expect(verifier).toBeInstanceOf(PreconditionVerifier);
    });
  });

  describe('verify', () => {
    it('should verify satisfiable precondition', async () => {
      mockZ3.checkSat = vi.fn().mockResolvedValue('sat');

      const input: PreconditionInput = {
        condition: { expression: 'x > 0', format: 'javascript' },
        variables: [{ name: 'x', type: 'Int' }],
      };

      const result = await verifier.verify(input);

      expect(result.status).toBe('valid');
    });

    it('should detect unsatisfiable precondition', async () => {
      mockZ3.checkSat = vi.fn().mockResolvedValue('unsat');

      const input: PreconditionInput = {
        condition: { expression: 'x > 0 && x < 0', format: 'javascript' },
        variables: [{ name: 'x', type: 'Int' }],
      };

      const result = await verifier.verify(input);

      expect(result.status).toBe('invalid');
    });

    it('should handle unknown result', async () => {
      mockZ3.checkSat = vi.fn().mockResolvedValue('unknown');

      const input: PreconditionInput = {
        condition: { expression: 'complex_expression', format: 'javascript' },
        variables: [],
      };

      const result = await verifier.verify(input);

      expect(result.status).toBe('unknown');
    });

    it('should handle Z3 errors gracefully', async () => {
      mockZ3.checkSat = vi.fn().mockRejectedValue(new Error('Z3 error'));

      const input: PreconditionInput = {
        condition: { expression: 'invalid', format: 'javascript' },
        variables: [],
      };

      const result = await verifier.verify(input);

      expect(result.status).toBe('error');
      expect(result.errorMessage).toBeDefined();
    });
  });

  describe('checkSatisfiability', () => {
    it('should check if precondition is satisfiable', async () => {
      mockZ3.checkSat = vi.fn().mockResolvedValue('sat');

      const input: PreconditionInput = {
        condition: { expression: 'x >= 0', format: 'javascript' },
        variables: [{ name: 'x', type: 'Int' }],
      };

      const isSat = await verifier.checkSatisfiability(input);

      expect(isSat).toBe(true);
    });

    it('should return false for unsatisfiable expression', async () => {
      mockZ3.checkSat = vi.fn().mockResolvedValue('unsat');

      const input: PreconditionInput = {
        condition: { expression: 'false', format: 'javascript' },
        variables: [],
      };

      const isSat = await verifier.checkSatisfiability(input);

      expect(isSat).toBe(false);
    });
  });

  describe('checkValidity', () => {
    it('should check if precondition is valid (always true)', async () => {
      // For validity: check if negation is unsatisfiable
      mockZ3.checkSat = vi.fn().mockResolvedValue('unsat');

      const input: PreconditionInput = {
        condition: { expression: 'x == x', format: 'javascript' },
        variables: [{ name: 'x', type: 'Int' }],
      };

      const isValid = await verifier.checkValidity(input);

      expect(isValid).toBe(true);
    });

    it('should return false for invalid expression', async () => {
      mockZ3.checkSat = vi.fn().mockResolvedValue('sat');

      const input: PreconditionInput = {
        condition: { expression: 'x > 0', format: 'javascript' },
        variables: [{ name: 'x', type: 'Int' }],
      };

      const isValid = await verifier.checkValidity(input);

      expect(isValid).toBe(false);
    });
  });
});
