/**
 * ExtendedQualityGate Unit Tests
 *
 * @see TSK-FR-053 - ExtendedQualityGate型定義
 * @see TSK-FR-054 - toStandardGate関数
 * @see TSK-FR-055 - ExtendedQualityGateRunner
 * @see TSK-FR-056 - 基盤テスト
 * @trace DES-MUSUBIX-FR-001 Section 3.3
 */

import { describe, it, expect, vi } from 'vitest';
import {
  type GateTiming,
  type GateExecutionContext,
  type GateServices,
  createExtendedGate,
  toStandardGate,
  isEntryGate,
  isExitGate,
} from '../ExtendedQualityGate.js';
import type { QualityCheckResult } from '../QualityGate.js';

describe('ExtendedQualityGate', () => {
  // Test fixtures
  const createMockContext = (overrides: Partial<GateExecutionContext> = {}): GateExecutionContext => ({
    workflowId: 'WF-20260123-001',
    phase: 'design',
    artifacts: [],
    services: {},
    ...overrides,
  });

  const createSuccessResult = (): QualityCheckResult => ({
    passed: true,
    message: 'Check passed',
    severity: 'info',
  });

  const createFailureResult = (): QualityCheckResult => ({
    passed: false,
    message: 'Check failed',
    severity: 'error',
  });

  describe('GateTiming', () => {
    it('should accept "entry" as valid timing', () => {
      const timing: GateTiming = 'entry';
      expect(timing).toBe('entry');
    });

    it('should accept "exit" as valid timing', () => {
      const timing: GateTiming = 'exit';
      expect(timing).toBe('exit');
    });
  });

  describe('GateExecutionContext', () => {
    it('should have required properties', () => {
      const context = createMockContext();

      expect(context.workflowId).toBe('WF-20260123-001');
      expect(context.phase).toBe('design');
      expect(context.artifacts).toEqual([]);
      expect(context.services).toEqual({});
    });

    it('should support optional changedFiles', () => {
      const context = createMockContext({
        changedFiles: ['src/index.ts', 'src/utils.ts'],
      });

      expect(context.changedFiles).toEqual(['src/index.ts', 'src/utils.ts']);
    });

    it('should support optional tasks', () => {
      const context = createMockContext({
        tasks: [{ id: 'TSK-001', title: 'Test task' }] as any,
      });

      expect(context.tasks).toHaveLength(1);
    });
  });

  describe('createExtendedGate', () => {
    it('should create an entry gate', () => {
      const gate = createExtendedGate({
        id: 'gate-test-001',
        name: 'Test Entry Gate',
        phase: 'requirements',
        description: 'Test gate for requirements phase entry',
        timing: 'entry',
        check: async () => createSuccessResult(),
      });

      expect(gate.id).toBe('gate-test-001');
      expect(gate.name).toBe('Test Entry Gate');
      expect(gate.phase).toBe('requirements');
      expect(gate.description).toBe('Test gate for requirements phase entry');
      expect(gate.timing).toBe('entry');
      expect(gate.mandatory).toBe(true); // default
    });

    it('should create an exit gate', () => {
      const gate = createExtendedGate({
        id: 'gate-test-002',
        name: 'Test Exit Gate',
        phase: 'design',
        description: 'Test gate for design phase exit',
        timing: 'exit',
        mandatory: false,
        check: async () => createSuccessResult(),
      });

      expect(gate.timing).toBe('exit');
      expect(gate.mandatory).toBe(false);
    });

    it('should execute check function with context', async () => {
      const checkFn = vi.fn().mockResolvedValue(createSuccessResult());
      const gate = createExtendedGate({
        id: 'gate-test-003',
        name: 'Test Gate',
        phase: 'implementation',
        description: 'Test',
        timing: 'exit',
        check: checkFn,
      });

      const context = createMockContext({ phase: 'implementation' });
      const result = await gate.check(context);

      expect(checkFn).toHaveBeenCalledWith(context);
      expect(result.passed).toBe(true);
    });

    it('should be immutable (frozen)', () => {
      const gate = createExtendedGate({
        id: 'gate-test-004',
        name: 'Immutable Gate',
        phase: 'design',
        description: 'Test',
        timing: 'entry',
        check: async () => createSuccessResult(),
      });

      expect(Object.isFrozen(gate)).toBe(true);
    });
  });

  describe('toStandardGate', () => {
    it('should convert extended gate to standard QualityGate', () => {
      const extendedGate = createExtendedGate({
        id: 'gate-extended-001',
        name: 'Extended Gate',
        phase: 'design',
        description: 'Extended gate description',
        timing: 'exit',
        check: async () => createSuccessResult(),
      });

      const context = createMockContext();
      const contextProvider = () => context;
      const standardGate = toStandardGate(extendedGate, contextProvider);

      expect(standardGate.id).toBe('gate-extended-001');
      expect(standardGate.name).toBe('Extended Gate');
      expect(standardGate.phase).toBe('design');
      expect(standardGate.description).toBe('Extended gate description');
      expect(standardGate.mandatory).toBe(true);
      // Standard gate check takes no arguments
      expect(typeof standardGate.check).toBe('function');
    });

    it('should call extended check with context from provider', async () => {
      const checkFn = vi.fn().mockResolvedValue(createSuccessResult());
      const extendedGate = createExtendedGate({
        id: 'gate-extended-002',
        name: 'Extended Gate',
        phase: 'design',
        description: 'Test',
        timing: 'exit',
        check: checkFn,
      });

      const context = createMockContext({ workflowId: 'WF-CUSTOM-001' });
      const contextProvider = () => context;
      const standardGate = toStandardGate(extendedGate, contextProvider);

      // Execute standard gate (no arguments)
      await standardGate.check();

      // Verify extended check was called with context
      expect(checkFn).toHaveBeenCalledWith(context);
    });

    it('should preserve pass/fail results', async () => {
      const extendedGate = createExtendedGate({
        id: 'gate-extended-003',
        name: 'Failing Gate',
        phase: 'design',
        description: 'Test',
        timing: 'exit',
        check: async () => createFailureResult(),
      });

      const standardGate = toStandardGate(extendedGate, createMockContext);
      const result = await standardGate.check();

      expect(result.passed).toBe(false);
      expect(result.severity).toBe('error');
    });

    it('should be immutable (frozen)', () => {
      const extendedGate = createExtendedGate({
        id: 'gate-extended-004',
        name: 'Test',
        phase: 'design',
        description: 'Test',
        timing: 'entry',
        check: async () => createSuccessResult(),
      });

      const standardGate = toStandardGate(extendedGate, createMockContext);

      expect(Object.isFrozen(standardGate)).toBe(true);
    });
  });

  describe('isEntryGate', () => {
    it('should return true for entry timing', () => {
      const gate = createExtendedGate({
        id: 'gate-entry',
        name: 'Entry Gate',
        phase: 'requirements',
        description: 'Test',
        timing: 'entry',
        check: async () => createSuccessResult(),
      });

      expect(isEntryGate(gate)).toBe(true);
    });

    it('should return false for exit timing', () => {
      const gate = createExtendedGate({
        id: 'gate-exit',
        name: 'Exit Gate',
        phase: 'design',
        description: 'Test',
        timing: 'exit',
        check: async () => createSuccessResult(),
      });

      expect(isEntryGate(gate)).toBe(false);
    });
  });

  describe('isExitGate', () => {
    it('should return true for exit timing', () => {
      const gate = createExtendedGate({
        id: 'gate-exit',
        name: 'Exit Gate',
        phase: 'design',
        description: 'Test',
        timing: 'exit',
        check: async () => createSuccessResult(),
      });

      expect(isExitGate(gate)).toBe(true);
    });

    it('should return false for entry timing', () => {
      const gate = createExtendedGate({
        id: 'gate-entry',
        name: 'Entry Gate',
        phase: 'requirements',
        description: 'Test',
        timing: 'entry',
        check: async () => createSuccessResult(),
      });

      expect(isExitGate(gate)).toBe(false);
    });
  });

  describe('GateServices', () => {
    it('should support optional service dependencies', () => {
      const services: GateServices = {
        triageEngine: { checkPriorityBlocking: vi.fn() } as any,
      };

      const context = createMockContext({ services });

      expect(context.services.triageEngine).toBeDefined();
      expect(context.services.nonNegotiablesEngine).toBeUndefined();
    });
  });
});
