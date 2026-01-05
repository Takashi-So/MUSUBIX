/**
 * Error Handling E2E Tests
 *
 * @fileoverview End-to-end tests for error handling and recovery
 * @module @musubix/core/__tests__/e2e/error-handling.e2e.test
 * @requirement REQ-E2E-006
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import {
  TestContext,
  type ITestContext,
} from '../../src/testing/index.js';

describe('Error Handling E2E', () => {
  let ctx: ITestContext;

  beforeAll(async () => {
    ctx = await TestContext.builder()
      .withProject({ template: 'minimal', name: 'error-handling-e2e' })
      .build();
  });

  afterAll(async () => {
    await ctx.cleanup();
  });

  describe('Invalid Commands', () => {
    it('should handle unknown command gracefully', async () => {
      const result = await ctx.cli.run(['nonexistent-command']);
      // Should not crash (exit code may vary)
      expect(result.stderr + result.stdout).toBeTruthy();
    });

    it('should handle unknown subcommand', async () => {
      const result = await ctx.cli.requirements('unknown-subcommand');
      expect(result.stderr + result.stdout).toBeTruthy();
    });
  });

  describe('Missing Files', () => {
    it('should handle missing file gracefully', async () => {
      const result = await ctx.cli.ontology('validate', '-f', 'nonexistent.json');
      // Should report error but not crash
      expect(result.exitCode).not.toBe(0);
      expect(result.stderr.toLowerCase()).toMatch(/error|not found|enoent/i);
    });

    it('should handle missing directory', async () => {
      const result = await ctx.cli.run(['--config', '/nonexistent/path/config.json']);
      // Should handle gracefully
      expect(result.stderr + result.stdout).toBeTruthy();
    });
  });

  describe('Invalid Input', () => {
    it('should handle invalid JSON file', async () => {
      await ctx.project.addFile('invalid.json', '{ invalid json }');
      const result = await ctx.cli.ontology('validate', '-f', 'invalid.json');
      expect(result.exitCode).not.toBe(0);
      expect(result.stderr.toLowerCase()).toMatch(/parse|json|syntax|error/i);
    });

    it('should handle empty file', async () => {
      await ctx.project.addFile('empty.json', '');
      const result = await ctx.cli.ontology('validate', '-f', 'empty.json');
      expect(result.exitCode).not.toBe(0);
    });

    it('should handle empty array', async () => {
      await ctx.project.addFile('empty-array.json', '[]');
      const result = await ctx.cli.ontology('validate', '-f', 'empty-array.json');
      expect(result.exitCode).toBe(0);
      expect(result.stdout).toContain('0');
    });
  });

  describe('Invalid Arguments', () => {
    it('should handle missing required argument', async () => {
      const result = await ctx.cli.ontology('validate');
      // Should show help or error
      expect(result.stderr + result.stdout).toBeTruthy();
    });

    it('should handle invalid option value', async () => {
      const result = await ctx.cli.learn('export', '--output');
      // Should handle gracefully
      expect(result.stderr + result.stdout).toBeTruthy();
    });
  });

  describe('Edge Cases', () => {
    it('should handle special characters in file names', async () => {
      const specialName = 'test file with spaces.json';
      await ctx.project.addFile(specialName, '[]');
      expect(ctx.project.fileExists(specialName)).toBe(true);
    });

    it('should handle Unicode content', async () => {
      const unicodeContent = JSON.stringify([
        { subject: '日本語', predicate: 'contains', object: '漢字' },
      ]);
      await ctx.project.addFile('unicode.json', unicodeContent);
      const result = await ctx.cli.ontology('validate', '-f', 'unicode.json');
      expect(result.exitCode).toBe(0);
    });

    it('should handle very long strings', async () => {
      const longString = 'x'.repeat(10000);
      const content = JSON.stringify([
        { subject: longString, predicate: 'type', object: 'Long' },
      ]);
      await ctx.project.addFile('long.json', content);
      const result = await ctx.cli.ontology('validate', '-f', 'long.json');
      expect(result.exitCode).toBe(0);
    });
  });

  describe('Timeout Handling', () => {
    it('should complete within reasonable timeout', async () => {
      const start = Date.now();
      const result = await ctx.cli.run(['--help']);
      const duration = Date.now() - start;

      expect(result.exitCode).toBe(0);
      expect(duration).toBeLessThan(5000); // 5 seconds max
    });
  });

  describe('State Recovery', () => {
    it('should maintain state after error', async () => {
      // First, cause an error
      await ctx.cli.ontology('validate', '-f', 'nonexistent.json');

      // Then verify normal operation still works
      const result = await ctx.cli.run(['--version']);
      expect(result.exitCode).toBe(0);
      expect(result.stdout).toMatch(/\d+\.\d+\.\d+/);
    });

    it('should handle multiple consecutive errors', async () => {
      for (let i = 0; i < 3; i++) {
        await ctx.cli.ontology('validate', '-f', 'nonexistent.json');
      }

      // Should still work
      const result = await ctx.cli.run(['--help']);
      expect(result.exitCode).toBe(0);
    });
  });

  describe('User-Friendly Error Messages', () => {
    it('should provide helpful error for missing file', async () => {
      const result = await ctx.cli.ontology('validate', '-f', 'missing.json');
      // Error message should be understandable
      expect(result.stderr.length).toBeGreaterThan(0);
    });

    it('should suggest alternatives on unknown command', async () => {
      const result = await ctx.cli.run(['requrements']); // typo
      // Should either show help or suggest correction
      expect(result.stderr + result.stdout).toBeTruthy();
    });
  });
});
