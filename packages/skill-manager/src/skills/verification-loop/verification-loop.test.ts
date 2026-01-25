/**
 * Verification Loop Tests
 *
 * @see REQ-VL-001〜005
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createVerificationLoopManager,
  formatStopHookAuditMarkdown,
  type VerificationLoopConfig,
  type StopHookAuditReport,
  DEFAULT_VERIFICATION_LOOP_CONFIG,
} from '../verification-loop/index.js';

describe('VerificationLoopManager', () => {
  let manager: ReturnType<typeof createVerificationLoopManager>;

  beforeEach(() => {
    manager = createVerificationLoopManager();
  });

  describe('createVerificationLoopManager', () => {
    it('should create manager with default config', () => {
      expect(manager).toBeDefined();
      const config = manager.getConfig();
      expect(config.projectRoot).toBe(DEFAULT_VERIFICATION_LOOP_CONFIG.projectRoot);
    });

    it('should create manager with custom config', () => {
      const customConfig: Partial<VerificationLoopConfig> = {
        projectRoot: '/custom/path',
        continuousIntervalMinutes: 15,
      };
      const customManager = createVerificationLoopManager(customConfig);
      const config = customManager.getConfig();
      expect(config.projectRoot).toBe('/custom/path');
      expect(config.continuousIntervalMinutes).toBe(15);
    });
  });

  describe('runVerification', () => {
    it.skip('should run full verification loop (slow test)', async () => {
      const report = await manager.runVerification();

      expect(report.id).toBeDefined();
      expect(report.phases).toBeDefined();
    });
  });

  describe('runPhase', () => {
    it('should run type-check phase', async () => {
      const result = await manager.runPhase('type-check');

      expect(result.phase).toBe('type-check');
    });

    it('should run lint phase', async () => {
      const result = await manager.runPhase('lint');

      expect(result.phase).toBe('lint');
    });

    it.skip('should run test phase (slow test)', async () => {
      const result = await manager.runPhase('test');

      expect(result.phase).toBe('test');
    });

    it('should run diff phase', async () => {
      const result = await manager.runPhase('diff');

      expect(result.phase).toBe('diff');
    });
  });
});

describe('Format functions', () => {
  it('should format stop hook audit as markdown', () => {
    const report: StopHookAuditReport = {
      timestamp: new Date(),
      editedFiles: ['src/index.ts'],
      items: [
        {
          type: 'console-log',
          file: 'src/index.ts',
          line: 10,
          content: 'console.log("debug")',
        },
      ],
      hasIssues: true,
    };

    const markdown = formatStopHookAuditMarkdown(report);
    expect(markdown).toContain('Stop Hook');
    expect(markdown).toContain('console');
  });
});
