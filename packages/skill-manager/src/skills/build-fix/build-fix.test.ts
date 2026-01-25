/**
 * Build Fix Tests
 *
 * @see REQ-BF-001〜003
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createBuildFixManager,
  formatFixReportMarkdown,
  formatBuildErrorsMarkdown,
  type BuildFixConfig,
  type BuildError,
  type FixReport,
  type FixStrategy,
  DEFAULT_BUILD_FIX_CONFIG,
} from '../build-fix/index.js';

describe('BuildFixManager', () => {
  let manager: ReturnType<typeof createBuildFixManager>;

  beforeEach(() => {
    manager = createBuildFixManager();
  });

  describe('createBuildFixManager', () => {
    it('should create manager with default config', () => {
      expect(manager).toBeDefined();
      const config = manager.getConfig();
      expect(config.maxIterations).toBe(DEFAULT_BUILD_FIX_CONFIG.maxIterations);
      expect(config.autoFix).toBe(DEFAULT_BUILD_FIX_CONFIG.autoFix);
    });

    it('should create manager with custom config', () => {
      const customConfig: Partial<BuildFixConfig> = {
        maxIterations: 5,
        autoFix: true,
      };
      const customManager = createBuildFixManager(customConfig);
      const config = customManager.getConfig();
      expect(config.maxIterations).toBe(5);
      expect(config.autoFix).toBe(true);
    });
  });

  describe('runBuild', () => {
    it.skip('should run build and parse errors (slow test - runs actual build)', async () => {
      const result = await manager.runBuild();

      expect(result.success).toBeDefined();
      expect(result.errors).toBeInstanceOf(Array);
    });
  });

  describe('analyzeErrors', () => {
    it('should analyze build output', () => {
      const output = `
src/index.ts(10,5): error TS2345: Type 'string' is not assignable to type 'number'.
      `;
      const errors = manager.analyzeErrors(output);

      expect(errors).toBeInstanceOf(Array);
    });
  });

  describe('generateFixStrategy', () => {
    it('should generate fix strategy for error', () => {
      const error: BuildError = {
        id: 'err-1',
        category: 'type-error',
        priority: 'high',
        message: "Type 'string' is not assignable to type 'number'",
        file: 'src/index.ts',
        line: 10,
        column: 5,
        code: 'TS2345',
      };

      const strategy = manager.generateFixStrategy(error);

      expect(strategy.errorId).toBe('err-1');
      expect(strategy.steps).toBeInstanceOf(Array);
    });
  });

  describe('applyFix', () => {
    it('should apply fix and return result', async () => {
      const strategy: FixStrategy = {
        errorId: 'err-1',
        steps: ['Add type annotation'],
        estimatedImpact: 'high',
        requiresUserApproval: false,
      };

      const result = await manager.applyFix(strategy);

      expect(result).toBeDefined();
    });
  });

  describe('runIterativeFix', () => {
    it.skip('should run iterative build fix loop (slow test - runs actual build)', async () => {
      const report = await manager.runIterativeFix();

      expect(report.id).toBeDefined();
      expect(report.totalIterations).toBeGreaterThanOrEqual(0);
      expect(report.errorsFixed).toBeDefined();
      expect(report.errorsRemaining).toBeDefined();
    });
  });

  describe('getMostImpactfulErrors', () => {
    it('should get most impactful errors', () => {
      const errors: BuildError[] = [
        { id: 'e1', category: 'type-error', priority: 'high', message: 'msg1' },
        { id: 'e2', category: 'lint-error', priority: 'low', message: 'msg2' },
        { id: 'e3', category: 'import-error', priority: 'medium', message: 'msg3' },
      ];
      const result = manager.getMostImpactfulErrors(errors, 2);

      expect(result.length).toBe(2);
    });
  });
});

describe('Format functions', () => {
  it('should format fix report as markdown', () => {
    const report: FixReport = {
      id: 'report-1',
      startedAt: new Date(),
      completedAt: new Date(),
      totalIterations: 3,
      errorsFixed: 4,
      errorsRemaining: 1,
      filesModified: ['src/index.ts'],
      warnings: [],
      attempts: [],
    };

    const markdown = formatFixReportMarkdown(report);
    expect(markdown).toContain('Build Fix Report');
  });

  it('should format build errors as markdown', () => {
    const errors: BuildError[] = [
      {
        id: 'err-1',
        category: 'type-error',
        priority: 'high',
        message: 'Type mismatch',
        file: 'src/index.ts',
        line: 10,
        column: 5,
        code: 'TS2345',
      },
    ];

    const markdown = formatBuildErrorsMarkdown(errors);
    expect(markdown).toContain('Build');
    expect(markdown).toContain('src/index.ts');
  });
});
