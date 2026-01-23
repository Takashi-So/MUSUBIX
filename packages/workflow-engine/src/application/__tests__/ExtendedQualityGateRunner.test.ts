/**
 * ExtendedQualityGateRunner Unit Tests
 *
 * @see TSK-FR-055 - ExtendedQualityGateRunner
 * @trace DES-MUSUBIX-FR-001 Section 3.3.3
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import {
  ExtendedQualityGateRunner,
} from '../ExtendedQualityGateRunner.js';
import {
  type GateExecutionContext,
  createExtendedGate,
} from '../../domain/entities/ExtendedQualityGate.js';
import type { QualityCheckResult } from '../../domain/entities/QualityGate.js';

describe('ExtendedQualityGateRunner', () => {
  let runner: ExtendedQualityGateRunner;

  const createMockContext = (overrides: Partial<GateExecutionContext> = {}): GateExecutionContext => ({
    workflowId: 'WF-20260123-001',
    phase: 'design',
    artifacts: [],
    services: {},
    ...overrides,
  });

  const createSuccessResult = (message = 'Check passed'): QualityCheckResult => ({
    passed: true,
    message,
    severity: 'info',
  });

  const createFailureResult = (message = 'Check failed'): QualityCheckResult => ({
    passed: false,
    message,
    severity: 'error',
  });

  beforeEach(() => {
    runner = new ExtendedQualityGateRunner();
  });

  describe('registerExtendedGate', () => {
    it('should register an extended gate', () => {
      const gate = createExtendedGate({
        id: 'gate-test-001',
        name: 'Test Gate',
        phase: 'design',
        description: 'Test gate',
        timing: 'entry',
        check: async () => createSuccessResult(),
      });

      runner.registerExtendedGate(gate);

      const gates = runner.getExtendedGates('design');
      expect(gates).toHaveLength(1);
      expect(gates[0].id).toBe('gate-test-001');
    });

    it('should register multiple gates for same phase', () => {
      const gate1 = createExtendedGate({
        id: 'gate-1',
        name: 'Gate 1',
        phase: 'design',
        description: 'Test',
        timing: 'entry',
        check: async () => createSuccessResult(),
      });

      const gate2 = createExtendedGate({
        id: 'gate-2',
        name: 'Gate 2',
        phase: 'design',
        description: 'Test',
        timing: 'exit',
        check: async () => createSuccessResult(),
      });

      runner.registerExtendedGate(gate1);
      runner.registerExtendedGate(gate2);

      const gates = runner.getExtendedGates('design');
      expect(gates).toHaveLength(2);
    });
  });

  describe('runExtendedGates', () => {
    it('should run all gates for a phase and return results', async () => {
      const gate = createExtendedGate({
        id: 'gate-run-001',
        name: 'Test Gate',
        phase: 'design',
        description: 'Test',
        timing: 'exit',
        check: async () => createSuccessResult(),
      });

      runner.registerExtendedGate(gate);

      const context = createMockContext({ phase: 'design' });
      const result = await runner.runExtendedGates('design', 'exit', context);

      expect(result.phase).toBe('design');
      expect(result.timing).toBe('exit');
      expect(result.allPassed).toBe(true);
      expect(result.results).toHaveLength(1);
    });

    it('should filter gates by timing', async () => {
      const entryGate = createExtendedGate({
        id: 'gate-entry',
        name: 'Entry Gate',
        phase: 'design',
        description: 'Test',
        timing: 'entry',
        check: async () => createSuccessResult('entry'),
      });

      const exitGate = createExtendedGate({
        id: 'gate-exit',
        name: 'Exit Gate',
        phase: 'design',
        description: 'Test',
        timing: 'exit',
        check: async () => createSuccessResult('exit'),
      });

      runner.registerExtendedGate(entryGate);
      runner.registerExtendedGate(exitGate);

      const context = createMockContext({ phase: 'design' });

      // Run only entry gates
      const entryResult = await runner.runExtendedGates('design', 'entry', context);
      expect(entryResult.results).toHaveLength(1);
      expect(entryResult.results[0].gateName).toBe('Entry Gate');

      // Run only exit gates
      const exitResult = await runner.runExtendedGates('design', 'exit', context);
      expect(exitResult.results).toHaveLength(1);
      expect(exitResult.results[0].gateName).toBe('Exit Gate');
    });

    it('should pass context to gate check function', async () => {
      const checkFn = vi.fn().mockResolvedValue(createSuccessResult());
      const gate = createExtendedGate({
        id: 'gate-context',
        name: 'Context Gate',
        phase: 'implementation',
        description: 'Test',
        timing: 'exit',
        check: checkFn,
      });

      runner.registerExtendedGate(gate);

      const context = createMockContext({
        phase: 'implementation',
        changedFiles: ['src/index.ts'],
      });

      await runner.runExtendedGates('implementation', 'exit', context);

      expect(checkFn).toHaveBeenCalledWith(context);
    });

    it('should report failure when mandatory gate fails', async () => {
      const gate = createExtendedGate({
        id: 'gate-mandatory',
        name: 'Mandatory Gate',
        phase: 'design',
        description: 'Test',
        timing: 'exit',
        mandatory: true,
        check: async () => createFailureResult(),
      });

      runner.registerExtendedGate(gate);

      const context = createMockContext({ phase: 'design' });
      const result = await runner.runExtendedGates('design', 'exit', context);

      expect(result.allPassed).toBe(false);
      expect(result.mandatoryPassed).toBe(false);
    });

    it('should pass when optional gate fails but mandatory passes', async () => {
      const mandatoryGate = createExtendedGate({
        id: 'gate-mandatory',
        name: 'Mandatory Gate',
        phase: 'design',
        description: 'Test',
        timing: 'exit',
        mandatory: true,
        check: async () => createSuccessResult(),
      });

      const optionalGate = createExtendedGate({
        id: 'gate-optional',
        name: 'Optional Gate',
        phase: 'design',
        description: 'Test',
        timing: 'exit',
        mandatory: false,
        check: async () => createFailureResult(),
      });

      runner.registerExtendedGate(mandatoryGate);
      runner.registerExtendedGate(optionalGate);

      const context = createMockContext({ phase: 'design' });
      const result = await runner.runExtendedGates('design', 'exit', context);

      expect(result.allPassed).toBe(false);
      expect(result.mandatoryPassed).toBe(true);
    });

    it('should return empty result for phase with no gates', async () => {
      const context = createMockContext({ phase: 'completion' });
      const result = await runner.runExtendedGates('completion', 'exit', context);

      expect(result.results).toHaveLength(0);
      expect(result.allPassed).toBe(true);
      expect(result.mandatoryPassed).toBe(true);
    });

    it('should handle gate execution errors', async () => {
      const gate = createExtendedGate({
        id: 'gate-error',
        name: 'Error Gate',
        phase: 'design',
        description: 'Test',
        timing: 'exit',
        check: async () => {
          throw new Error('Gate execution failed');
        },
      });

      runner.registerExtendedGate(gate);

      const context = createMockContext({ phase: 'design' });
      const result = await runner.runExtendedGates('design', 'exit', context);

      expect(result.allPassed).toBe(false);
      expect(result.results[0].results[0].message).toContain('Gate execution failed');
    });

    it('should measure execution duration', async () => {
      const gate = createExtendedGate({
        id: 'gate-duration',
        name: 'Duration Gate',
        phase: 'design',
        description: 'Test',
        timing: 'exit',
        check: async () => {
          await new Promise(resolve => setTimeout(resolve, 10));
          return createSuccessResult();
        },
      });

      runner.registerExtendedGate(gate);

      const context = createMockContext({ phase: 'design' });
      const result = await runner.runExtendedGates('design', 'exit', context);

      // Allow some variance in timing (async scheduling)
      expect(result.duration).toBeGreaterThanOrEqual(5);
    });
  });

  describe('registerToStandardRunner', () => {
    it('should convert and register gates to standard runner', () => {
      const gate = createExtendedGate({
        id: 'gate-convert',
        name: 'Convert Gate',
        phase: 'design',
        description: 'Test',
        timing: 'exit',
        check: async () => createSuccessResult(),
      });

      runner.registerExtendedGate(gate);

      const mockStandardRunner = {
        registerGate: vi.fn(),
      };

      const context = createMockContext({ phase: 'design' });
      runner.registerToStandardRunner(mockStandardRunner as any, () => context);

      expect(mockStandardRunner.registerGate).toHaveBeenCalled();
    });
  });

  describe('getExtendedGates', () => {
    it('should return empty array for phase with no gates', () => {
      const gates = runner.getExtendedGates('completion');
      expect(gates).toEqual([]);
    });

    it('should return registered gates for phase', () => {
      const gate = createExtendedGate({
        id: 'gate-get',
        name: 'Get Gate',
        phase: 'requirements',
        description: 'Test',
        timing: 'entry',
        check: async () => createSuccessResult(),
      });

      runner.registerExtendedGate(gate);

      const gates = runner.getExtendedGates('requirements');
      expect(gates).toHaveLength(1);
      expect(gates[0].id).toBe('gate-get');
    });
  });
});
