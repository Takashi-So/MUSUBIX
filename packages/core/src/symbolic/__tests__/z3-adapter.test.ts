/**
 * Z3 Adapter Tests
 *
 * Tests for Z3 theorem prover integration.
 * Note: Some tests may be skipped if Z3 is not installed.
 *
 * @see TSK-SYMB-011
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  Z3Adapter,
  PreconditionVerifier,
  PostconditionVerifier,
  InvariantVerifier,
  DEFAULT_Z3_CONFIG,
} from '../z3-adapter.js';
import type { VerificationCondition } from '../vc-generator.js';

describe('Z3Adapter', () => {
  let adapter: Z3Adapter;

  beforeEach(() => {
    adapter = new Z3Adapter();
  });

  describe('isAvailable', () => {
    it('should return boolean indicating Z3 availability', async () => {
      const available = await adapter.isAvailable();
      expect(typeof available).toBe('boolean');
    });

    it('should cache availability result', async () => {
      const result1 = await adapter.isAvailable();
      const result2 = await adapter.isAvailable();
      expect(result1).toBe(result2);
    });
  });

  describe('executeZ3', () => {
    it('should return Z3Result structure', async () => {
      const available = await adapter.isAvailable();
      if (!available) {
        console.log('Skipping Z3 execution test - Z3 not installed');
        return;
      }

      const result = await adapter.executeZ3('(check-sat)\n');

      expect(result).toHaveProperty('verdict');
      expect(result).toHaveProperty('executionTimeMs');
      expect(result).toHaveProperty('timedOut');
      expect(['sat', 'unsat', 'unknown', 'timeout', 'error']).toContain(result.verdict);
    });

    it('should handle simple sat check', async () => {
      const available = await adapter.isAvailable();
      if (!available) {
        console.log('Skipping Z3 sat test - Z3 not installed');
        return;
      }

      const smtLib = `
        (declare-const x Int)
        (assert (> x 0))
        (check-sat)
      `;

      const result = await adapter.executeZ3(smtLib);
      expect(result.verdict).toBe('sat');
    });

    it('should handle unsat check', async () => {
      const available = await adapter.isAvailable();
      if (!available) {
        console.log('Skipping Z3 unsat test - Z3 not installed');
        return;
      }

      const smtLib = `
        (declare-const x Int)
        (assert (> x 0))
        (assert (< x 0))
        (check-sat)
      `;

      const result = await adapter.executeZ3(smtLib);
      expect(result.verdict).toBe('unsat');
    });

    it('should respect timeout', async () => {
      const available = await adapter.isAvailable();
      if (!available) {
        console.log('Skipping Z3 timeout test - Z3 not installed');
        return;
      }

      // Very short timeout
      const shortAdapter = new Z3Adapter({ timeoutMs: 1 });
      const result = await shortAdapter.executeZ3('(check-sat)\n');

      // May or may not timeout depending on system
      expect(['sat', 'unsat', 'unknown', 'timeout', 'error']).toContain(result.verdict);
    });
  });

  describe('verifyCondition', () => {
    it('should handle unavailable Z3 gracefully', async () => {
      const unavailableAdapter = new Z3Adapter({
        z3Path: '/nonexistent/z3',
        fallbackBehavior: 'warn',
      });

      const vc: VerificationCondition = {
        id: 'VC-001',
        type: 'precondition',
        description: 'Test precondition',
        smtExpression: '(> x 0)',
        requirementIds: ['REQ-001'],
        status: 'pending',
        generatedAt: new Date().toISOString(),
      };

      const result = await unavailableAdapter.verifyCondition(vc, '(check-sat)');

      expect(result.vcId).toBe('VC-001');
      expect(['skipped', 'error', 'unknown']).toContain(result.status);
    });
  });

  describe('verifyAll', () => {
    it('should verify multiple conditions', async () => {
      const available = await adapter.isAvailable();
      if (!available) {
        console.log('Skipping Z3 verifyAll test - Z3 not installed');
        return;
      }

      const conditions: VerificationCondition[] = [
        {
          id: 'VC-001',
          type: 'precondition',
          description: 'x is positive',
          smtExpression: '(> x 0)',
          requirementIds: ['REQ-001'],
          status: 'pending',
          generatedAt: new Date().toISOString(),
        },
      ];

      const smtLib = `
        (declare-const x Int)
        (assert (> x 0))
        (check-sat)
      `;

      const result = await adapter.verifyAll(conditions, smtLib);

      expect(result).toHaveProperty('overallVerdict');
      expect(result).toHaveProperty('vcResults');
      expect(result).toHaveProperty('smtLibUsed');
      expect(result).toHaveProperty('totalExecutionTimeMs');
      expect(result).toHaveProperty('explanation');
    });

    it('should provide explanation with reasoning', async () => {
      const available = await adapter.isAvailable();
      if (!available) {
        console.log('Skipping Z3 explanation test - Z3 not installed');
        return;
      }

      const conditions: VerificationCondition[] = [
        {
          id: 'VC-001',
          type: 'assertion',
          description: 'Test assertion',
          smtExpression: '(= x 5)',
          requirementIds: ['REQ-001'],
          status: 'pending',
          generatedAt: new Date().toISOString(),
        },
      ];

      const smtLib = `
        (declare-const x Int)
        (assert (= x 5))
        (check-sat)
      `;

      const result = await adapter.verifyAll(conditions, smtLib);

      expect(result.explanation.summary).toBeTruthy();
      expect(result.explanation.reasoning.length).toBeGreaterThan(0);
    });
  });

  describe('graceful degradation', () => {
    it('should skip verification when Z3 unavailable with skip behavior', async () => {
      const skipAdapter = new Z3Adapter({
        z3Path: '/nonexistent/z3',
        fallbackBehavior: 'skip',
      });

      const conditions: VerificationCondition[] = [
        {
          id: 'VC-001',
          type: 'precondition',
          description: 'Test',
          smtExpression: '(> x 0)',
          requirementIds: ['REQ-001'],
          status: 'pending',
          generatedAt: new Date().toISOString(),
        },
      ];

      const result = await skipAdapter.verifyAll(conditions, '(check-sat)');

      expect(result.overallVerdict).toBe('partial');
      expect(result.partialResultMetadata).toBeDefined();
    });
  });

  describe('default configuration', () => {
    it('should have sensible defaults', () => {
      expect(DEFAULT_Z3_CONFIG.timeoutMs).toBe(5000);
      expect(DEFAULT_Z3_CONFIG.totalTimeoutMs).toBe(30000);
      expect(DEFAULT_Z3_CONFIG.fallbackBehavior).toBe('warn');
    });
  });
});

describe('PreconditionVerifier', () => {
  let verifier: PreconditionVerifier;
  let adapter: Z3Adapter;

  beforeEach(() => {
    adapter = new Z3Adapter();
    verifier = new PreconditionVerifier(adapter);
  });

  it('should verify preconditions', async () => {
    const available = await adapter.isAvailable();
    if (!available) {
      console.log('Skipping PreconditionVerifier test - Z3 not installed');
      return;
    }

    const preconditions = ['(> input 0)'];
    const context = {
      variables: [{ name: 'input', type: 'number' }],
    };

    const result = await verifier.verify(preconditions, context);

    expect(result.overallVerdict).toBeDefined();
    expect(result.vcResults).toBeDefined();
  });
});

describe('PostconditionVerifier', () => {
  let verifier: PostconditionVerifier;
  let adapter: Z3Adapter;

  beforeEach(() => {
    adapter = new Z3Adapter();
    verifier = new PostconditionVerifier(adapter);
  });

  it('should verify postconditions', async () => {
    const available = await adapter.isAvailable();
    if (!available) {
      console.log('Skipping PostconditionVerifier test - Z3 not installed');
      return;
    }

    const preconditions = ['(> a 0)', '(> b 0)'];
    const postconditions = ['(= result (+ a b))'];
    const context = {
      variables: [
        { name: 'a', type: 'number' },
        { name: 'b', type: 'number' },
        { name: 'result', type: 'number' },
      ],
    };

    const result = await verifier.verify(preconditions, postconditions, context);

    expect(result.overallVerdict).toBeDefined();
    expect(result.vcResults).toBeDefined();
  });
});

describe('InvariantVerifier', () => {
  let verifier: InvariantVerifier;
  let adapter: Z3Adapter;

  beforeEach(() => {
    adapter = new Z3Adapter();
    verifier = new InvariantVerifier(adapter);
  });

  it('should verify invariants', async () => {
    const available = await adapter.isAvailable();
    if (!available) {
      console.log('Skipping InvariantVerifier test - Z3 not installed');
      return;
    }

    const invariants = ['(>= balance 0)'];
    const context = {
      variables: [{ name: 'balance', type: 'number' }],
    };

    const result = await verifier.verify(invariants, context);

    expect(result.overallVerdict).toBeDefined();
    expect(result.vcResults).toBeDefined();
  });
});
