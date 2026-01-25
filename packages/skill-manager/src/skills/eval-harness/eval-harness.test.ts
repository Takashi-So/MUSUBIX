/**
 * Eval Harness Tests
 *
 * @see REQ-EH-001〜005
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createEvalHarnessManager,
  formatCapabilityEvalMarkdown,
  formatRegressionEvalMarkdown,
  formatPassAtKMarkdown,
  type EvalHarnessConfig,
  type CapabilityEval,
  type RegressionEval,
  type PassAtKMetrics,
  DEFAULT_EVAL_HARNESS_CONFIG,
} from '../eval-harness/index.js';

describe('EvalHarnessManager', () => {
  let manager: ReturnType<typeof createEvalHarnessManager>;

  beforeEach(() => {
    manager = createEvalHarnessManager();
  });

  describe('createEvalHarnessManager', () => {
    it('should create manager with default config', () => {
      expect(manager).toBeDefined();
      expect(manager.getConfig).toBeDefined();
      const config = manager.getConfig();
      expect(config.evalsDir).toBe(DEFAULT_EVAL_HARNESS_CONFIG.evalsDir);
    });

    it('should create manager with custom config', () => {
      const customConfig: Partial<EvalHarnessConfig> = {
        defaultTimeout: 60000,
        maxRetries: 5,
      };
      const customManager = createEvalHarnessManager(customConfig);
      const config = customManager.getConfig();
      expect(config.defaultTimeout).toBe(60000);
      expect(config.maxRetries).toBe(5);
    });
  });

  describe('createCapabilityEval', () => {
    it('should create capability evaluation', async () => {
      const result = await manager.createCapabilityEval(
        'test-eval',
        'code-generation',
        ['Generates valid code'],
        'valid code',
      );

      expect(result.id).toBeDefined();
      expect(result.name).toBe('test-eval');
      expect(result.task).toBe('code-generation');
    });
  });

  describe('createRegressionEval', () => {
    it('should create regression evaluation', async () => {
      const testResults = [
        { name: 'test1', status: 'pass' as const },
        { name: 'test2', status: 'pass' as const },
      ];
      const result = await manager.createRegressionEval(
        'regression-test',
        'v1.0.0',
        testResults,
        0,
      );

      expect(result.id).toBeDefined();
      expect(result.name).toBe('regression-test');
      expect(result.baseline).toBe('v1.0.0');
    });
  });

  describe('calculatePassAtK', () => {
    it('should calculate pass@k metrics', async () => {
      const eval_ = await manager.createCapabilityEval(
        'test',
        'task',
        [],
        '',
      );
      const metrics = await manager.calculatePassAtK(eval_.id);

      expect(metrics.passAt1).toBeGreaterThanOrEqual(0);
      expect(metrics.passAt1).toBeLessThanOrEqual(1);
    });
  });
});

describe('Format functions', () => {
  it('should format capability eval as markdown', () => {
    const eval_: CapabilityEval = {
      id: 'eval-1',
      name: 'Test Eval',
      task: 'code-generation',
      successCriteria: [
        { id: 'c1', description: 'Valid code', status: 'passed' },
      ],
      expectedOutput: 'valid code',
      createdAt: new Date(),
      updatedAt: new Date(),
    };

    const markdown = formatCapabilityEvalMarkdown(eval_);
    expect(markdown).toContain('CAPABILITY');
    expect(markdown).toContain('Test Eval');
  });

  it('should format regression eval as markdown', () => {
    const eval_: RegressionEval = {
      id: 'eval-1',
      name: 'Regression Test',
      baseline: 'v1.0.0',
      tests: [{ name: 'test1', status: 'pass' }],
      passedCount: 1,
      totalCount: 1,
      previousPassedCount: 1,
      createdAt: new Date(),
    };

    const markdown = formatRegressionEvalMarkdown(eval_);
    expect(markdown).toContain('REGRESSION');
    expect(markdown).toContain('Regression Test');
  });

  it('should format pass@k metrics as markdown', () => {
    const metrics: PassAtKMetrics = {
      passAt1: 0.65,
      passAt3: 0.80,
      consecutiveAt3: 0.50,
      totalAttempts: 100,
      successfulAttempts: 65,
    };

    const markdown = formatPassAtKMarkdown(metrics);
    expect(markdown).toContain('pass@1');
    expect(markdown).toContain('65'); // 65.0% or 65
  });
});
