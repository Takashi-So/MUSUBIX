/**
 * @fileoverview Git Hooks Tests
 * @module @nahisaho/musubix-security/tests/phase4/git-hooks
 */

import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest';
import { mkdirSync, writeFileSync, existsSync, rmSync, readFileSync } from 'fs';
import { join } from 'path';
import { tmpdir } from 'os';
import {
  GitHooksManager,
  createGitHooks,
  installPreCommitHook,
  installRecommendedHooks,
  type GitHooksConfig,
  type HookType,
} from '../../src/integrations/git-hooks.js';

describe('GitHooksManager', () => {
  let testDir: string;
  let gitDir: string;

  beforeEach(() => {
    // Create temporary test directory with .git structure
    testDir = join(tmpdir(), `musubix-test-${Date.now()}`);
    gitDir = join(testDir, '.git');
    mkdirSync(join(gitDir, 'hooks'), { recursive: true });
  });

  afterEach(() => {
    // Cleanup
    try {
      rmSync(testDir, { recursive: true, force: true });
    } catch {
      // Ignore cleanup errors
    }
  });

  describe('createGitHooks', () => {
    it('should create GitHooksManager with default options', () => {
      const hooks = createGitHooks({
        hooks: ['pre-commit'],
      });
      expect(hooks).toBeInstanceOf(GitHooksManager);
    });

    it('should create GitHooksManager with custom options', () => {
      const hooks = createGitHooks({
        hooks: ['pre-commit', 'pre-push'],
        failOn: ['critical'],
        stagedOnly: false,
        timeout: 120,
      });
      expect(hooks).toBeInstanceOf(GitHooksManager);
    });
  });

  describe('install', () => {
    it('should install hooks in .git/hooks directory', async () => {
      const hooks = createGitHooks({
        hooks: ['pre-commit'],
      });

      const result = await hooks.install(testDir);

      expect(result.installed).toContain('pre-commit');
      expect(result.gitDir).toBe(gitDir);
      expect(existsSync(join(gitDir, 'hooks', 'pre-commit'))).toBe(true);
    });

    it('should install multiple hooks', async () => {
      const hooks = createGitHooks({
        hooks: ['pre-commit', 'pre-push'],
      });

      const result = await hooks.install(testDir);

      expect(result.installed).toContain('pre-commit');
      expect(result.installed).toContain('pre-push');
      expect(result.installed.length).toBe(2);
    });

    it('should backup existing hooks', async () => {
      // Create existing hook
      const existingHookPath = join(gitDir, 'hooks', 'pre-commit');
      writeFileSync(existingHookPath, '#!/bin/sh\necho "existing hook"');

      const hooks = createGitHooks({
        hooks: ['pre-commit'],
      });

      const result = await hooks.install(testDir);

      expect(result.backupCreated).toBe(true);
      expect(existsSync(`${existingHookPath}.musubix-backup`)).toBe(true);
    });

    it('should not backup our own hooks', async () => {
      // Create existing musubix hook
      const existingHookPath = join(gitDir, 'hooks', 'pre-commit');
      writeFileSync(existingHookPath, '#!/bin/sh\n# musubix-security\necho "musubix hook"');

      const hooks = createGitHooks({
        hooks: ['pre-commit'],
      });

      const result = await hooks.install(testDir);

      expect(result.backupCreated).toBe(false);
    });

    it('should throw error for non-git directory', async () => {
      const nonGitDir = join(tmpdir(), `non-git-${Date.now()}`);
      mkdirSync(nonGitDir, { recursive: true });

      const hooks = createGitHooks({
        hooks: ['pre-commit'],
      });

      await expect(hooks.install(nonGitDir)).rejects.toThrow('Not a git repository');

      rmSync(nonGitDir, { recursive: true, force: true });
    });
  });

  describe('uninstall', () => {
    it('should uninstall hooks', async () => {
      const hooks = createGitHooks({
        hooks: ['pre-commit'],
      });

      // Install first
      await hooks.install(testDir);
      expect(existsSync(join(gitDir, 'hooks', 'pre-commit'))).toBe(true);

      // Uninstall
      const result = await hooks.uninstall(testDir);

      expect(result.removed.length + result.restored.length).toBeGreaterThan(0);
    });

    it('should restore backed up hooks', async () => {
      // Create existing hook
      const existingHookPath = join(gitDir, 'hooks', 'pre-commit');
      const originalContent = '#!/bin/sh\necho "original"';
      writeFileSync(existingHookPath, originalContent);

      const hooks = createGitHooks({
        hooks: ['pre-commit'],
      });

      // Install (creates backup)
      await hooks.install(testDir);

      // Uninstall (restores backup)
      const result = await hooks.uninstall(testDir);

      expect(result.restored).toContain('pre-commit');
      expect(readFileSync(existingHookPath, 'utf-8')).toBe(originalContent);
    });
  });

  describe('generateHookScript', () => {
    it('should generate pre-commit hook script', () => {
      const hooks = createGitHooks({
        hooks: ['pre-commit'],
        failOn: ['critical', 'high'],
        timeout: 60,
      });

      const script = hooks.generateHookScript('pre-commit');

      expect(script).toContain('#!/bin/sh');
      expect(script).toContain('musubix-security');
      expect(script).toContain('pre-commit');
      expect(script).toContain('critical,high');
      expect(script).toContain('timeout 60s');
    });

    it('should include CI skip when enabled', () => {
      const hooks = createGitHooks({
        hooks: ['pre-commit'],
        skipInCI: true,
      });

      const script = hooks.generateHookScript('pre-commit');

      expect(script).toContain('Skip in CI environment');
      expect(script).toContain('$CI');
    });

    it('should not include CI skip when disabled', () => {
      const hooks = createGitHooks({
        hooks: ['pre-commit'],
        skipInCI: false,
      });

      const script = hooks.generateHookScript('pre-commit');

      expect(script).not.toContain('Skip in CI environment');
    });

    it('should use custom script when provided', () => {
      const customScript = '#!/bin/sh\necho "custom hook"';
      const hooks = createGitHooks({
        hooks: ['pre-commit'],
        customScripts: {
          'pre-commit': customScript,
        },
      });

      const script = hooks.generateHookScript('pre-commit');

      expect(script).toBe(customScript);
    });
  });

  describe('shouldSkip', () => {
    let originalEnv: NodeJS.ProcessEnv;

    beforeEach(() => {
      originalEnv = { ...process.env };
      delete process.env.CI;
      delete process.env.GITHUB_ACTIONS;
      delete process.env.GITLAB_CI;
    });

    afterEach(() => {
      process.env = originalEnv;
    });

    it('should return false when not in CI', () => {
      const hooks = createGitHooks({
        hooks: ['pre-commit'],
        skipInCI: true,
      });

      expect(hooks.shouldSkip()).toBe(false);
    });

    it('should return true when in CI and skipInCI is true', () => {
      process.env.CI = 'true';
      
      const hooks = createGitHooks({
        hooks: ['pre-commit'],
        skipInCI: true,
      });

      expect(hooks.shouldSkip()).toBe(true);
    });

    it('should detect GitHub Actions', () => {
      process.env.GITHUB_ACTIONS = 'true';
      
      const hooks = createGitHooks({
        hooks: ['pre-commit'],
        skipInCI: true,
      });

      expect(hooks.shouldSkip()).toBe(true);
    });
  });

  describe('getStagedFiles', () => {
    it('should return empty array for non-git directory', async () => {
      const nonGitDir = join(tmpdir(), `non-git-${Date.now()}`);
      mkdirSync(nonGitDir, { recursive: true });

      const hooks = createGitHooks({
        hooks: ['pre-commit'],
      });

      const files = await hooks.getStagedFiles(nonGitDir);

      expect(files).toEqual([]);

      rmSync(nonGitDir, { recursive: true, force: true });
    });
  });

  describe('getStatus', () => {
    it('should return installed status for installed hooks', async () => {
      const hooks = createGitHooks({
        hooks: ['pre-commit', 'pre-push'],
      });

      await hooks.install(testDir);
      const status = await hooks.getStatus(testDir);

      expect(status['pre-commit']).toBe('installed');
      expect(status['pre-push']).toBe('installed');
    });

    it('should return not-installed for missing hooks', async () => {
      const hooks = createGitHooks({
        hooks: ['pre-commit'],
      });

      const status = await hooks.getStatus(testDir);

      expect(status['pre-commit']).toBe('not-installed');
    });

    it('should return other for non-musubix hooks', async () => {
      // Create a non-musubix hook
      writeFileSync(
        join(gitDir, 'hooks', 'pre-commit'),
        '#!/bin/sh\necho "other hook"'
      );

      const hooks = createGitHooks({
        hooks: ['pre-commit'],
      });

      const status = await hooks.getStatus(testDir);

      expect(status['pre-commit']).toBe('other');
    });
  });

  describe('runHook', () => {
    let originalEnv: NodeJS.ProcessEnv;

    beforeEach(() => {
      originalEnv = { ...process.env };
      delete process.env.CI;
    });

    afterEach(() => {
      process.env = originalEnv;
    });

    it('should skip in CI when configured', async () => {
      process.env.CI = 'true';
      
      const hooks = createGitHooks({
        hooks: ['pre-commit'],
        skipInCI: true,
      });

      const result = await hooks.runHook('pre-commit', testDir);

      expect(result.passed).toBe(true);
      expect(result.skippedReason).toContain('CI');
    });

    it('should pass with no files to scan', async () => {
      const hooks = createGitHooks({
        hooks: ['pre-commit'],
        stagedOnly: true,
      });

      const result = await hooks.runHook('pre-commit', testDir);

      expect(result.passed).toBe(true);
      expect(result.filesScanned).toEqual([]);
    });
  });

  describe('helper functions', () => {
    it('installPreCommitHook should install pre-commit hook', async () => {
      const result = await installPreCommitHook(testDir);

      expect(result.installed).toContain('pre-commit');
    });

    it('installRecommendedHooks should install pre-commit and pre-push', async () => {
      const result = await installRecommendedHooks(testDir);

      expect(result.installed).toContain('pre-commit');
      expect(result.installed).toContain('pre-push');
    });
  });
});
