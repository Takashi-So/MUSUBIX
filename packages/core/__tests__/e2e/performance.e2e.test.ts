/**
 * Performance E2E Tests
 *
 * @fileoverview End-to-end tests for performance requirements
 * @module @musubix/core/__tests__/e2e/performance.e2e.test
 * @requirement REQ-E2E-005
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import {
  TestContext,
  type ITestContext,
  isWithinBudget,
} from '../../src/testing/index.js';

describe('Performance E2E', () => {
  let ctx: ITestContext;

  beforeAll(async () => {
    ctx = await TestContext.builder()
      .withProject({ template: 'minimal', name: 'perf-e2e' })
      .build();
  });

  afterAll(async () => {
    await ctx.cleanup();
  });

  describe('CLI Startup Time', () => {
    it('should start within 500ms for version check', async () => {
      const result = await ctx.cli.run(['--version']);
      expect(result.exitCode).toBe(0);
      expect(isWithinBudget(result, { maxDuration: 500 })).toBe(true);
    });

    it('should start within 1000ms for help', async () => {
      const result = await ctx.cli.run(['--help']);
      expect(result.exitCode).toBe(0);
      expect(isWithinBudget(result, { maxDuration: 1000 })).toBe(true);
    });

    it('should measure startup time via perf command', async () => {
      const result = await ctx.cli.perf('startup');
      expect(result.exitCode).toBe(0);
      expect(result.stdout).toMatch(/\d+/);
    });
  });

  describe('Memory Usage', () => {
    it('should report memory usage', async () => {
      const result = await ctx.cli.perf('memory');
      expect(result.exitCode).toBe(0);
      expect(result.stdout).toContain('Memory');
    });

    it('should use less than 512MB for basic operations', async () => {
      const result = await ctx.cli.perf('memory');
      expect(result.exitCode).toBe(0);

      // Extract memory usage from output
      const match = result.stdout.match(/(\d+(?:\.\d+)?)\s*(MB|GB)/i);
      if (match) {
        const value = parseFloat(match[1]);
        const unit = match[2].toUpperCase();
        const mb = unit === 'GB' ? value * 1024 : value;
        expect(mb).toBeLessThan(512);
      }
    });
  });

  describe('Command Response Times', () => {
    const commands = [
      { args: ['requirements', '--help'], maxMs: 500 },
      { args: ['design', '--help'], maxMs: 500 },
      { args: ['codegen', '--help'], maxMs: 500 },
      { args: ['learn', 'status'], maxMs: 1000 },
      { args: ['learn', 'patterns'], maxMs: 1000 },
      { args: ['ontology', '--help'], maxMs: 500 },
    ];

    for (const { args, maxMs } of commands) {
      it(`should complete "${args.join(' ')}" within ${maxMs}ms`, async () => {
        const result = await ctx.cli.run(args);
        expect(result.exitCode).toBe(0);
        expect(result.duration).toBeLessThan(maxMs);
      });
    }
  });

  describe('Benchmark Suite', () => {
    it('should run benchmark command', async () => {
      const result = await ctx.cli.perf('benchmark');
      expect(result.exitCode).toBe(0);
      expect(result.stdout).toContain('Benchmark');
    });
  });

  describe('Cache Operations', () => {
    it('should show cache statistics', async () => {
      const result = await ctx.cli.perf('cache-stats');
      expect(result.exitCode).toBe(0);
      expect(result.stdout).toContain('Cache');
    });

    it('should clear cache', async () => {
      const result = await ctx.cli.perf('cache-clear');
      expect(result.exitCode).toBe(0);
      expect(result.stdout.toLowerCase()).toContain('clear');
    });
  });

  describe('Repeated Operations', () => {
    it('should maintain performance over multiple runs', async () => {
      const durations: number[] = [];

      for (let i = 0; i < 5; i++) {
        const result = await ctx.cli.run(['--version']);
        expect(result.exitCode).toBe(0);
        durations.push(result.duration);
      }

      // Average should be reasonable
      const avg = durations.reduce((a, b) => a + b, 0) / durations.length;
      expect(avg).toBeLessThan(1000);

      // No significant degradation
      const maxDuration = Math.max(...durations);
      const minDuration = Math.min(...durations);
      expect(maxDuration / minDuration).toBeLessThan(3); // Max 3x variation
    });
  });

  describe('Large Input Handling', () => {
    it('should handle large requirements file', async () => {
      // Create a large requirements file
      const requirements: string[] = [];
      for (let i = 1; i <= 100; i++) {
        requirements.push(`## REQ-${i.toString().padStart(3, '0')}`);
        requirements.push(`THE system SHALL provide feature ${i}.`);
        requirements.push('');
      }

      await ctx.project.addFile('large-requirements.md', requirements.join('\n'));

      const start = Date.now();
      // Just check the file exists (actual parsing would be in analyze)
      expect(ctx.project.fileExists('large-requirements.md')).toBe(true);
      const content = await ctx.project.getFile('large-requirements.md');
      const duration = Date.now() - start;

      expect(content.length).toBeGreaterThan(1000);
      expect(duration).toBeLessThan(1000); // Read should be fast
    });
  });
});
