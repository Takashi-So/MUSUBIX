/**
 * SingleStepEnforcer Unit Tests
 *
 * @see TSK-FR-013〜017 - SingleStepEnforcer
 * @see REQ-FR-090〜092 - SingleStepEnforcer
 * @trace DES-MUSUBIX-FR-001 DES-ORCH-003
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import {
  createSingleStepEnforcer,
  type ISingleStepEnforcer,
} from '../SingleStepEnforcer.js';
import {
  createStepDefinition,
  createSingleStepConfig,
  DEFAULT_SINGLE_STEP_CONFIG,
} from '../../value-objects/StepDefinition.js';

describe('SingleStepEnforcer', () => {
  let enforcer: ISingleStepEnforcer;

  beforeEach(() => {
    enforcer = createSingleStepEnforcer();
  });

  describe('createStepDefinition', () => {
    it('should create a step with auto-generated ID', () => {
      const step = createStepDefinition({
        name: 'Create File',
        description: 'Create a new TypeScript file',
        type: 'file-create',
        target: 'src/service.ts',
      });

      expect(step.id).toBeDefined();
      expect(step.id).toMatch(/^step-/);
      expect(step.name).toBe('Create File');
      expect(step.type).toBe('file-create');
    });

    it('should allow custom ID', () => {
      const step = createStepDefinition({
        id: 'STEP-001',
        name: 'Test Step',
        description: 'Test',
        type: 'test-run',
      });

      expect(step.id).toBe('STEP-001');
    });

    it('should be immutable', () => {
      const step = createStepDefinition({
        name: 'Immutable Step',
        description: 'Test',
        type: 'other',
      });

      expect(Object.isFrozen(step)).toBe(true);
    });
  });

  describe('DEFAULT_SINGLE_STEP_CONFIG', () => {
    it('should have sensible defaults', () => {
      expect(DEFAULT_SINGLE_STEP_CONFIG.maxFilesPerStep).toBe(1);
      expect(DEFAULT_SINGLE_STEP_CONFIG.maxLinesPerStep).toBe(100);
      expect(DEFAULT_SINGLE_STEP_CONFIG.allowMultiFile).toBe(false);
      expect(DEFAULT_SINGLE_STEP_CONFIG.requireConfirmation).toBe(true);
    });
  });

  describe('validateStep', () => {
    it('should validate a valid single-file step', () => {
      const step = createStepDefinition({
        name: 'Valid Step',
        description: 'Modify one file',
        type: 'file-modify',
        target: 'src/index.ts',
      });

      const result = enforcer.validateStep(step, {
        affectedFiles: ['src/index.ts'],
        linesChanged: 50,
      });

      expect(result.valid).toBe(true);
      expect(result.errors).toHaveLength(0);
    });

    it('should reject multi-file step when not allowed', () => {
      const step = createStepDefinition({
        name: 'Multi-file Step',
        description: 'Modify multiple files',
        type: 'file-modify',
      });

      const result = enforcer.validateStep(step, {
        affectedFiles: ['src/a.ts', 'src/b.ts', 'src/c.ts'],
        linesChanged: 30,
      });

      expect(result.valid).toBe(false);
      expect(result.errors.some(e => e.includes('files'))).toBe(true);
    });

    it('should reject step exceeding line limit', () => {
      const step = createStepDefinition({
        name: 'Large Change',
        description: 'Many lines changed',
        type: 'file-modify',
        target: 'src/index.ts',
      });

      const result = enforcer.validateStep(step, {
        affectedFiles: ['src/index.ts'],
        linesChanged: 150,
      });

      expect(result.valid).toBe(false);
      expect(result.errors.some(e => e.includes('lines'))).toBe(true);
    });

    it('should warn when approaching limits', () => {
      const step = createStepDefinition({
        name: 'Near Limit',
        description: 'Close to line limit',
        type: 'file-modify',
        target: 'src/index.ts',
      });

      const result = enforcer.validateStep(step, {
        affectedFiles: ['src/index.ts'],
        linesChanged: 85, // 85% of 100 limit
      });

      expect(result.valid).toBe(true);
      expect(result.warnings.length).toBeGreaterThan(0);
    });
  });

  describe('enforceStep', () => {
    it('should enforce and execute a valid step', async () => {
      const step = createStepDefinition({
        name: 'Execute Step',
        description: 'Test execution',
        type: 'file-modify',
        target: 'src/test.ts',
      });

      const executor = vi.fn().mockResolvedValue({
        success: true,
        affectedFiles: ['src/test.ts'],
        linesAdded: 10,
        linesRemoved: 5,
      });

      const result = await enforcer.enforceStep(step, executor);

      expect(result.status).toBe('completed');
      expect(executor).toHaveBeenCalled();
    });

    it('should block step that violates constraints', async () => {
      const enforcer = createSingleStepEnforcer(
        createSingleStepConfig({ maxFilesPerStep: 1 })
      );

      const step = createStepDefinition({
        name: 'Invalid Step',
        description: 'Too many files',
        type: 'file-modify',
      });

      const executor = vi.fn().mockResolvedValue({
        success: true,
        affectedFiles: ['a.ts', 'b.ts'], // 2 files
        linesAdded: 10,
        linesRemoved: 0,
      });

      const result = await enforcer.enforceStep(step, executor);

      expect(result.status).toBe('blocked');
    });

    it('should handle executor failure', async () => {
      const step = createStepDefinition({
        name: 'Failing Step',
        description: 'Will fail',
        type: 'file-modify',
        target: 'src/test.ts',
      });

      const executor = vi.fn().mockRejectedValue(new Error('Execution failed'));

      const result = await enforcer.enforceStep(step, executor);

      expect(result.status).toBe('failed');
      expect(result.error).toContain('Execution failed');
    });
  });

  describe('getCurrentStep', () => {
    it('should return null when no step is in progress', () => {
      expect(enforcer.getCurrentStep()).toBeNull();
    });

    it('should return current step when one is in progress', async () => {
      const step = createStepDefinition({
        name: 'Current Step',
        description: 'In progress',
        type: 'file-modify',
        target: 'src/test.ts',
      });

      // Start step without completing
      const promise = enforcer.enforceStep(step, async () => {
        await new Promise(resolve => setTimeout(resolve, 50));
        return { success: true, affectedFiles: ['src/test.ts'], linesAdded: 1, linesRemoved: 0 };
      });

      // Check current step while executing
      await new Promise(resolve => setTimeout(resolve, 10));
      const current = enforcer.getCurrentStep();

      expect(current?.name).toBe('Current Step');

      await promise;
    });
  });

  describe('getStepHistory', () => {
    it('should track completed steps', async () => {
      const step1 = createStepDefinition({
        id: 'step-1',
        name: 'Step 1',
        description: 'First step',
        type: 'file-create',
        target: 'src/a.ts',
      });

      const step2 = createStepDefinition({
        id: 'step-2',
        name: 'Step 2',
        description: 'Second step',
        type: 'file-create',
        target: 'src/b.ts',
      });

      await enforcer.enforceStep(step1, async () => ({
        success: true,
        affectedFiles: ['src/a.ts'],
        linesAdded: 10,
        linesRemoved: 0,
      }));

      await enforcer.enforceStep(step2, async () => ({
        success: true,
        affectedFiles: ['src/b.ts'],
        linesAdded: 20,
        linesRemoved: 0,
      }));

      const history = enforcer.getStepHistory();

      expect(history).toHaveLength(2);
      expect(history[0].step.id).toBe('step-1');
      expect(history[1].step.id).toBe('step-2');
    });
  });

  describe('reset', () => {
    it('should clear step history', async () => {
      const step = createStepDefinition({
        name: 'Step to Reset',
        description: 'Will be cleared',
        type: 'file-create',
        target: 'src/test.ts',
      });

      await enforcer.enforceStep(step, async () => ({
        success: true,
        affectedFiles: ['src/test.ts'],
        linesAdded: 5,
        linesRemoved: 0,
      }));

      expect(enforcer.getStepHistory()).toHaveLength(1);

      enforcer.reset();

      expect(enforcer.getStepHistory()).toHaveLength(0);
    });
  });

  describe('custom configuration', () => {
    it('should allow multi-file when configured', async () => {
      const multiFileEnforcer = createSingleStepEnforcer(
        createSingleStepConfig({
          allowMultiFile: true,
          maxFilesPerStep: 5,
        })
      );

      const step = createStepDefinition({
        name: 'Multi-file Step',
        description: 'Multiple files allowed',
        type: 'file-modify',
      });

      const result = await multiFileEnforcer.enforceStep(step, async () => ({
        success: true,
        affectedFiles: ['a.ts', 'b.ts', 'c.ts'],
        linesAdded: 30,
        linesRemoved: 10,
      }));

      expect(result.status).toBe('completed');
    });

    it('should use custom line limit', () => {
      const customEnforcer = createSingleStepEnforcer(
        createSingleStepConfig({
          maxLinesPerStep: 200,
        })
      );

      const step = createStepDefinition({
        name: 'Large Step',
        description: 'Many lines',
        type: 'file-modify',
        target: 'src/big.ts',
      });

      const result = customEnforcer.validateStep(step, {
        affectedFiles: ['src/big.ts'],
        linesChanged: 180,
      });

      expect(result.valid).toBe(true);
    });
  });
});
