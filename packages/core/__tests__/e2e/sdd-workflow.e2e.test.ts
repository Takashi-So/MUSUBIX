/**
 * SDD Workflow E2E Tests
 *
 * @fileoverview End-to-end tests for the complete SDD workflow
 * @module @musubix/core/__tests__/e2e/sdd-workflow.e2e.test
 * @requirement REQ-E2E-002
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import {
  TestContext,
  type ITestContext,
  isValidEars,
  hasTraceability,
} from '../../src/testing/index.js';

describe('SDD Workflow E2E', () => {
  let ctx: ITestContext;

  beforeAll(async () => {
    ctx = await TestContext.builder()
      .withProject({ template: 'sdd', name: 'sdd-workflow-e2e' })
      .withFixtures()
      .build();
  });

  afterAll(async () => {
    await ctx.cleanup();
  });

  describe('Requirements Phase', () => {
    it('should display requirements help', async () => {
      const result = await ctx.cli.requirements('--help');
      expect(result.exitCode).toBe(0);
      expect(result.stdout).toContain('analyze');
      expect(result.stdout).toContain('validate');
    });

    it('should validate EARS requirements from fixtures', () => {
      for (const req of ctx.fixtures.requirements.valid) {
        expect(isValidEars(req.text)).toBe(true);
      }
    });

    it('should reject invalid requirements', () => {
      for (const text of ctx.fixtures.requirements.invalid) {
        expect(isValidEars(text)).toBe(false);
      }
    });
  });

  describe('Design Phase', () => {
    it('should display design help', async () => {
      const result = await ctx.cli.design('--help');
      expect(result.exitCode).toBe(0);
      expect(result.stdout).toContain('generate');
      expect(result.stdout).toContain('patterns');
    });

    it('should have design file in template', async () => {
      expect(ctx.project.fileExists('design.md')).toBe(true);
      const content = await ctx.project.getFile('design.md');
      expect(content).toContain('DES-001');
    });
  });

  describe('Code Generation Phase', () => {
    it('should display codegen help', async () => {
      const result = await ctx.cli.codegen('--help');
      expect(result.exitCode).toBe(0);
      expect(result.stdout).toContain('generate');
      expect(result.stdout).toContain('analyze');
    });

    it('should have code with traceability', async () => {
      expect(ctx.project.fileExists('src/auth/auth-service.ts')).toBe(true);
      const content = await ctx.project.getFile('src/auth/auth-service.ts');
      expect(hasTraceability(content, 'REQ-001')).toBe(true);
      expect(hasTraceability(content, 'DES-001')).toBe(true);
    });
  });

  describe('Traceability Phase', () => {
    it('should display trace help', async () => {
      const result = await ctx.cli.trace('--help');
      expect(result.exitCode).toBe(0);
      expect(result.stdout).toContain('matrix');
      expect(result.stdout).toContain('impact');
    });
  });

  describe('Learning Phase', () => {
    it('should display learning status', async () => {
      const result = await ctx.cli.learn('status');
      expect(result.exitCode).toBe(0);
      expect(result.stdout).toContain('Learning');
    });

    it('should list best practices', async () => {
      const result = await ctx.cli.learn('best-practices');
      expect(result.exitCode).toBe(0);
      expect(result.stdout).toContain('Best Practice');
    });

    it('should list patterns', async () => {
      const result = await ctx.cli.learn('patterns');
      expect(result.exitCode).toBe(0);
    });
  });

  describe('Ontology Phase', () => {
    it('should display ontology help', async () => {
      const result = await ctx.cli.ontology('--help');
      expect(result.exitCode).toBe(0);
      expect(result.stdout).toContain('validate');
      expect(result.stdout).toContain('check-circular');
      expect(result.stdout).toContain('stats');
    });

    it('should validate triples', async () => {
      const triplesPath = 'test-triples.json';
      await ctx.project.addFile(
        triplesPath,
        JSON.stringify(ctx.fixtures.triples.valid)
      );

      const result = await ctx.cli.ontology('validate', '-f', triplesPath);
      expect(result.exitCode).toBe(0);
      expect(result.stdout).toContain('Loaded');
    });

    it('should detect circular dependencies', async () => {
      const circularPath = 'circular-triples.json';
      await ctx.project.addFile(
        circularPath,
        JSON.stringify(ctx.fixtures.triples.circular)
      );

      const result = await ctx.cli.ontology('check-circular', '-f', circularPath);
      // Should detect the cycle
      expect(result.stdout.toLowerCase()).toMatch(/cycle|circular/i);
    });
  });

  describe('Performance Phase', () => {
    it('should display perf help', async () => {
      const result = await ctx.cli.perf('--help');
      expect(result.exitCode).toBe(0);
      expect(result.stdout).toContain('benchmark');
      expect(result.stdout).toContain('memory');
    });

    it('should show memory usage', async () => {
      const result = await ctx.cli.perf('memory');
      expect(result.exitCode).toBe(0);
      expect(result.stdout).toContain('Memory');
    });
  });

  describe('Full Workflow Integration', () => {
    it('should complete CLI startup within budget', async () => {
      const result = await ctx.cli.run(['--version']);
      expect(result.exitCode).toBe(0);
      expect(result.duration).toBeLessThan(2000); // 2 seconds max
    });

    it('should support multiple consecutive commands', async () => {
      const commands = [
        ['--version'],
        ['--help'],
        ['requirements', '--help'],
        ['design', '--help'],
        ['learn', 'status'],
      ];

      for (const args of commands) {
        const result = await ctx.cli.run(args);
        expect(result.exitCode).toBe(0);
      }
    });
  });
});
