/**
 * E2E Testing Framework Tests
 *
 * @fileoverview Tests for the E2E testing utilities
 * @module @musubix/core/testing/__tests__
 * @requirement REQ-E2E-001
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import * as fs from 'fs';
import {
  createTestProject,
  withTestProject,
  getFixtures,
  getFixturesWith,
  createCliRunner,
  TestContext,
  createTestContext,
  withTestContext,
  isValidEars,
  getEarsPattern,
  hasExitCode,
  isWithinBudget,
  hasTraceability,
  containsPattern,
  matchesC4Schema,
  assertValidEars,
  assertExitCode,
  assertWithinBudget,
} from '../index.js';
import type { ITestProject, CliResult } from '../types.js';

describe('E2E Testing Framework', () => {
  describe('TestProject', () => {
    let project: ITestProject;

    beforeAll(async () => {
      project = createTestProject({ name: 'test-project-unit' });
      await project.create();
    });

    afterAll(async () => {
      await project.destroy();
    });

    it('should create project directory', () => {
      expect(fs.existsSync(project.path)).toBe(true);
    });

    it('should add files to project', async () => {
      await project.addFile('test.txt', 'Hello World');
      expect(project.fileExists('test.txt')).toBe(true);
      const content = await project.getFile('test.txt');
      expect(content).toBe('Hello World');
    });

    it('should add nested files', async () => {
      await project.addFile('src/main.ts', 'export const x = 1;');
      expect(project.fileExists('src/main.ts')).toBe(true);
    });
  });

  describe('TestProject with Templates', () => {
    it('should create minimal template', async () => {
      await withTestProject({ template: 'minimal' }, async (project) => {
        expect(project.fileExists('package.json')).toBe(true);
      });
    });

    it('should create full template', async () => {
      await withTestProject({ template: 'full' }, async (project) => {
        expect(project.fileExists('package.json')).toBe(true);
        expect(project.fileExists('tsconfig.json')).toBe(true);
        expect(project.fileExists('src/index.ts')).toBe(true);
      });
    });

    it('should create SDD template', async () => {
      await withTestProject({ template: 'sdd' }, async (project) => {
        expect(project.fileExists('requirements.md')).toBe(true);
        expect(project.fileExists('design.md')).toBe(true);
        expect(project.fileExists('src/auth/auth-service.ts')).toBe(true);
      });
    });

    it('should cleanup after withTestProject', async () => {
      let projectPath = '';
      await withTestProject({ template: 'minimal' }, async (project) => {
        projectPath = project.path;
        expect(fs.existsSync(projectPath)).toBe(true);
      });
      // Wait a bit for cleanup
      await new Promise((resolve) => setTimeout(resolve, 100));
      expect(fs.existsSync(projectPath)).toBe(false);
    });
  });

  describe('TestFixtures', () => {
    it('should provide valid requirements', () => {
      const fixtures = getFixtures();
      expect(fixtures.requirements.valid.length).toBeGreaterThan(0);
      for (const req of fixtures.requirements.valid) {
        expect(req.valid).toBe(true);
        expect(isValidEars(req.text)).toBe(true);
      }
    });

    it('should provide invalid requirements', () => {
      const fixtures = getFixtures();
      expect(fixtures.requirements.invalid.length).toBeGreaterThan(0);
    });

    it('should provide code samples', () => {
      const fixtures = getFixtures();
      expect(fixtures.code.typescript).toBeTruthy();
      expect(Object.keys(fixtures.code.patterns).length).toBeGreaterThan(0);
    });

    it('should provide triple samples', () => {
      const fixtures = getFixtures();
      expect(fixtures.triples.valid.length).toBeGreaterThan(0);
      expect(fixtures.triples.circular.length).toBeGreaterThan(0);
      expect(fixtures.triples.inconsistent.length).toBeGreaterThan(0);
    });

    it('should merge custom fixtures', () => {
      const custom = getFixturesWith({
        requirements: {
          valid: [{ id: 'CUSTOM', pattern: 'ubiquitous', text: 'Custom req', valid: true }],
          invalid: [],
        },
      });
      expect(custom.requirements.valid[0].id).toBe('CUSTOM');
    });
  });

  describe('CliRunner', () => {
    it('should run CLI commands', async () => {
      const cli = createCliRunner();
      const result = await cli.run(['--version']);
      expect(result.exitCode).toBe(0);
      expect(result.stdout).toMatch(/\d+\.\d+\.\d+/);
    });

    it('should capture duration', async () => {
      const cli = createCliRunner();
      const result = await cli.run(['--version']);
      expect(result.duration).toBeGreaterThan(0);
    });

    it('should provide command shortcuts', async () => {
      const cli = createCliRunner();
      const result = await cli.requirements('--help');
      expect(result.exitCode).toBe(0);
      expect(result.stdout).toContain('analyze');
    });
  });

  describe('TestContext', () => {
    it('should build context with builder pattern', async () => {
      const ctx = await TestContext.builder()
        .withProject({ template: 'minimal' })
        .withFixtures()
        .build();

      try {
        expect(ctx.project).toBeDefined();
        expect(ctx.fixtures).toBeDefined();
        expect(ctx.cli).toBeDefined();
        expect(ctx.project.fileExists('package.json')).toBe(true);
      } finally {
        await ctx.cleanup();
      }
    });

    it('should create context with options', async () => {
      const ctx = await createTestContext({
        project: { template: 'sdd' },
      });

      try {
        expect(ctx.project.fileExists('requirements.md')).toBe(true);
      } finally {
        await ctx.cleanup();
      }
    });

    it('should work with withTestContext', async () => {
      await withTestContext(
        { project: { template: 'minimal' } },
        async (ctx) => {
          expect(ctx.project.fileExists('package.json')).toBe(true);
          const result = await ctx.cli.run(['--version']);
          expect(result.exitCode).toBe(0);
        }
      );
    });
  });

  describe('Assertions', () => {
    describe('isValidEars', () => {
      it('should validate ubiquitous pattern', () => {
        expect(isValidEars('THE system SHALL provide authentication.')).toBe(true);
      });

      it('should validate event-driven pattern', () => {
        expect(isValidEars('WHEN user logs in, THE system SHALL create session.')).toBe(true);
      });

      it('should validate state-driven pattern', () => {
        expect(isValidEars('WHILE system is offline, THE system SHALL queue requests.')).toBe(true);
      });

      it('should validate unwanted pattern', () => {
        expect(isValidEars('THE system SHALL NOT store passwords in plain text.')).toBe(true);
      });

      it('should validate optional pattern', () => {
        expect(isValidEars('IF user is admin, THEN THE system SHALL show controls.')).toBe(true);
      });

      it('should reject invalid text', () => {
        expect(isValidEars('The system should work.')).toBe(false);
        expect(isValidEars('Users can log in.')).toBe(false);
      });
    });

    describe('getEarsPattern', () => {
      it('should identify patterns correctly', () => {
        expect(getEarsPattern('THE system SHALL work.')).toBe('ubiquitous');
        expect(getEarsPattern('WHEN x, THE system SHALL y.')).toBe('event-driven');
        expect(getEarsPattern('WHILE x, THE system SHALL y.')).toBe('state-driven');
        expect(getEarsPattern('THE system SHALL NOT x.')).toBe('unwanted');
        expect(getEarsPattern('IF x, THEN THE system SHALL y.')).toBe('optional');
        expect(getEarsPattern('invalid text')).toBe(null);
      });
    });

    describe('hasExitCode', () => {
      it('should check exit code', () => {
        const result: CliResult = { stdout: '', stderr: '', exitCode: 0, duration: 100 };
        expect(hasExitCode(result, 0)).toBe(true);
        expect(hasExitCode(result, 1)).toBe(false);
      });
    });

    describe('isWithinBudget', () => {
      it('should check duration budget', () => {
        const result: CliResult = { stdout: '', stderr: '', exitCode: 0, duration: 100 };
        expect(isWithinBudget(result, { maxDuration: 200 })).toBe(true);
        expect(isWithinBudget(result, { maxDuration: 50 })).toBe(false);
      });
    });

    describe('hasTraceability', () => {
      it('should find traceability IDs', () => {
        expect(hasTraceability('Implements REQ-001', 'REQ-001')).toBe(true);
        expect(hasTraceability('@requirement REQ-002', 'REQ-002')).toBe(true);
        expect(hasTraceability('@design DES-001', 'DES-001')).toBe(true);
        expect(hasTraceability('No reference here', 'REQ-001')).toBe(false);
      });
    });

    describe('containsPattern', () => {
      it('should find patterns', () => {
        expect(containsPattern('Using Repository pattern', 'repository')).toBe(true);
        expect(containsPattern('Factory implementation', 'factory')).toBe(true);
        expect(containsPattern('Simple code', 'singleton')).toBe(false);
      });
    });

    describe('matchesC4Schema', () => {
      it('should match C4 content', () => {
        expect(matchesC4Schema('Context diagram with Container and Component')).toBe(true);
        expect(matchesC4Schema('Just some random text')).toBe(false);
      });
    });

    describe('Assertion functions', () => {
      it('should create valid EARS assertion', () => {
        const result = assertValidEars('THE system SHALL work.');
        expect(result.pass).toBe(true);
        expect(result.actual).toBe('ubiquitous');
      });

      it('should create exit code assertion', () => {
        const cliResult: CliResult = { stdout: '', stderr: '', exitCode: 0, duration: 100 };
        const result = assertExitCode(cliResult, 0);
        expect(result.pass).toBe(true);
      });

      it('should create budget assertion', () => {
        const cliResult: CliResult = { stdout: '', stderr: '', exitCode: 0, duration: 100 };
        const result = assertWithinBudget(cliResult, { maxDuration: 200 });
        expect(result.pass).toBe(true);
      });
    });
  });
});
