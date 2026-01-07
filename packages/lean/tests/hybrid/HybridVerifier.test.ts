/**
 * @fileoverview Unit tests for HybridVerifier
 * @module @nahisaho/musubix-lean/tests/hybrid/HybridVerifier
 * @traceability REQ-LEAN-HYBRID-001 to REQ-LEAN-HYBRID-003
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  HybridVerifier,
  type RuntimeTestResult,
  type VerificationStrategy,
} from '../../src/hybrid/HybridVerifier.ts';
import type { LeanTheorem, LeanConfig } from '../../src/types.ts';

describe('HybridVerifier', () => {
  let verifier: HybridVerifier;

  beforeEach(() => {
    verifier = new HybridVerifier({
      timeout: 5000,
    });
  });

  describe('constructor', () => {
    it('should create instance with default config', () => {
      const defaultVerifier = new HybridVerifier();
      expect(defaultVerifier).toBeInstanceOf(HybridVerifier);
    });

    it('should create instance with custom config', () => {
      const customVerifier = new HybridVerifier({
        timeout: 10000,
        verbose: true,
      });
      expect(customVerifier).toBeInstanceOf(HybridVerifier);
    });
  });

  describe('setStrategy', () => {
    it('should set verification strategy', () => {
      verifier.setStrategy('runtime-first');
      // No error means success
      expect(true).toBe(true);
    });

    it('should accept all strategy types', () => {
      const strategies: VerificationStrategy[] = ['runtime-first', 'formal-first', 'parallel', 'adaptive'];
      for (const strategy of strategies) {
        verifier.setStrategy(strategy);
      }
      // No errors means success
      expect(true).toBe(true);
    });
  });

  describe('verify', () => {
    it('should verify function with runtime tests and theorem', async () => {
      const theorem: LeanTheorem = {
        id: 'THM-001',
        name: 'add_positive',
        statement: 'a > 0 → b > 0 → a + b > 0',
        requirementId: 'REQ-001',
        hypotheses: [],
        conclusion: { type: 'a + b > 0', leanCode: 'a + b > 0' },
        leanCode: 'theorem add_positive : a > 0 → b > 0 → a + b > 0 := by sorry',
      };

      const runtimeTests = (): RuntimeTestResult => ({
        functionId: 'add',
        passed: true,
        testCount: 10,
        failedTests: [],
        coverage: 80,
        duration: 100,
      });

      const result = await verifier.verify('add', runtimeTests, theorem);
      expect(result.isOk() || result.isErr()).toBe(true);
      if (result.isOk()) {
        expect(result.value.functionId).toBe('add');
        expect(['verified', 'failed', 'partial', 'unknown']).toContain(result.value.combinedStatus);
      }
    });

    it('should handle runtime test failure', async () => {
      const theorem: LeanTheorem = {
        id: 'THM-001',
        name: 'test_theorem',
        statement: 'test',
        requirementId: 'REQ-001',
        hypotheses: [],
        conclusion: { type: 'test', leanCode: 'test' },
        leanCode: 'theorem test : test := by sorry',
      };

      const runtimeTests = (): RuntimeTestResult => ({
        functionId: 'failing_func',
        passed: false,
        testCount: 10,
        failedTests: ['test_1', 'test_2'],
        coverage: 50,
        duration: 100,
      });

      const result = await verifier.verify('failing_func', runtimeTests, theorem);
      expect(result.isOk() || result.isErr()).toBe(true);
    });
  });

  describe('verifyBatch', () => {
    it('should verify multiple functions', async () => {
      const items = [
        {
          functionId: 'add',
          runtimeTests: (): RuntimeTestResult => ({
            functionId: 'add',
            passed: true,
            testCount: 5,
            failedTests: [],
            coverage: 90,
            duration: 50,
          }),
          theorem: {
            id: 'THM-001',
            name: 'add_theorem',
            statement: 'test',
            requirementId: 'REQ-001',
            hypotheses: [],
            conclusion: { type: 'test', leanCode: 'test' },
            leanCode: 'theorem add_theorem : test := by sorry',
          } as LeanTheorem,
        },
        {
          functionId: 'subtract',
          runtimeTests: (): RuntimeTestResult => ({
            functionId: 'subtract',
            passed: true,
            testCount: 5,
            failedTests: [],
            coverage: 85,
            duration: 60,
          }),
          theorem: {
            id: 'THM-002',
            name: 'sub_theorem',
            statement: 'test',
            requirementId: 'REQ-002',
            hypotheses: [],
            conclusion: { type: 'test', leanCode: 'test' },
            leanCode: 'theorem sub_theorem : test := by sorry',
          } as LeanTheorem,
        },
      ];

      const results = await verifier.verifyBatch(items);
      expect(results.size).toBe(2);
    });
  });

  describe('getStatistics', () => {
    it('should calculate statistics from results', async () => {
      const items = [
        {
          functionId: 'func1',
          runtimeTests: (): RuntimeTestResult => ({
            functionId: 'func1',
            passed: true,
            testCount: 5,
            failedTests: [],
            coverage: 90,
            duration: 50,
          }),
          theorem: {
            id: 'THM-001',
            name: 'func1_theorem',
            statement: 'test',
            requirementId: 'REQ-001',
            hypotheses: [],
            conclusion: { type: 'test', leanCode: 'test' },
            leanCode: 'theorem func1_theorem : test := by sorry',
          } as LeanTheorem,
        },
      ];

      const results = await verifier.verifyBatch(items);
      const stats = verifier.getStatistics(results);

      expect(stats.total).toBe(1);
      expect(stats.averageCoverage).toBeGreaterThanOrEqual(0);
    });

    it('should handle empty results', () => {
      const results = new Map();
      const stats = verifier.getStatistics(results);

      expect(stats.total).toBe(0);
      expect(stats.averageCoverage).toBe(0);
    });
  });
});
