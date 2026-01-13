/**
 * Init Command Tests
 *
 * @packageDocumentation
 * @module cli/commands/init.test
 *
 * @see REQ-CLI-001 - initコマンドパス正規化
 * @see TSK-CLI-001 - パス正規化タスク
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { executeInit, type InitOptions } from './init.js';
import { mkdir, writeFile, access } from 'fs/promises';

// Mock fs/promises
vi.mock('fs/promises', () => ({
  mkdir: vi.fn().mockResolvedValue(undefined),
  writeFile: vi.fn().mockResolvedValue(undefined),
  access: vi.fn().mockRejectedValue(new Error('ENOENT')),
  readFile: vi.fn().mockResolvedValue('{}'),
  readdir: vi.fn().mockResolvedValue([]),
  cp: vi.fn().mockResolvedValue(undefined),
}));

describe('init command', () => {
  const mockCwd = '/home/user/projects';

  beforeEach(() => {
    vi.spyOn(process, 'cwd').mockReturnValue(mockCwd);
    vi.clearAllMocks();
    // Reset mocks to default behavior
    vi.mocked(access).mockRejectedValue(new Error('ENOENT'));
    vi.mocked(mkdir).mockResolvedValue(undefined);
    vi.mocked(writeFile).mockResolvedValue(undefined);
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe('path normalization (REQ-CLI-001)', () => {
    const defaultOptions: InitOptions = { force: false };

    it('should handle relative path correctly', async () => {
      const result = await executeInit('./my-project', defaultOptions);

      expect(result.projectPath).toBe('/home/user/projects/my-project');
      expect(result.success).toBe(true);
    });

    it('should handle absolute path without double concatenation', async () => {
      // This was the bug: absolute paths were concatenated with cwd
      const result = await executeInit('/absolute/path/to/project', defaultOptions);

      expect(result.projectPath).toBe('/absolute/path/to/project');
      // Should NOT be: /home/user/projects/absolute/path/to/project
      expect(result.projectPath).not.toContain('/home/user/projects/absolute');
      expect(result.success).toBe(true);
    });

    it('should handle dot path (current directory)', async () => {
      const result = await executeInit('.', defaultOptions);

      expect(result.projectPath).toBe('/home/user/projects');
      expect(result.success).toBe(true);
    });

    it('should handle empty path', async () => {
      const result = await executeInit('', defaultOptions);

      expect(result.projectPath).toBe('/home/user/projects');
      expect(result.success).toBe(true);
    });

    it('should handle path with trailing slash', async () => {
      const result = await executeInit('./my-project/', defaultOptions);

      expect(result.projectPath).toBe('/home/user/projects/my-project');
      expect(result.success).toBe(true);
    });

    it('should handle parent directory navigation', async () => {
      const result = await executeInit('../sibling-project', defaultOptions);

      expect(result.projectPath).toBe('/home/user/sibling-project');
      expect(result.success).toBe(true);
    });

    it('should handle absolute path with trailing slash', async () => {
      const result = await executeInit('/absolute/path/', defaultOptions);

      expect(result.projectPath).toBe('/absolute/path');
      expect(result.success).toBe(true);
    });
  });

  describe('project initialization', () => {
    const defaultOptions: InitOptions = { force: false };

    it('should create directory structure', async () => {
      const result = await executeInit('./new-project', defaultOptions);

      expect(result.success).toBe(true);
      expect(result.filesCreated).toContain('steering/');
      expect(result.filesCreated).toContain('storage/');
      expect(result.filesCreated).toContain('musubix.config.json');
    });

    it('should use custom project name from options', async () => {
      const result = await executeInit('./new-project', {
        ...defaultOptions,
        name: 'custom-name',
      });

      expect(result.success).toBe(true);
      expect(result.message).toContain('custom-name');
    });

    it('should fail if project already initialized without force', async () => {
      // Mock that config file exists
      vi.mocked(access).mockResolvedValue(undefined);

      const result = await executeInit('./existing-project', defaultOptions);

      expect(result.success).toBe(false);
      expect(result.message).toContain('already initialized');
    });

    it('should overwrite if force option is true', async () => {
      // Mock that config file exists
      vi.mocked(access).mockResolvedValue(undefined);

      const result = await executeInit('./existing-project', {
        ...defaultOptions,
        force: true,
      });

      expect(result.success).toBe(true);
    });
  });

  describe('error messages', () => {
    it('should provide helpful message when project already exists', async () => {
      vi.mocked(access).mockResolvedValue(undefined);

      const result = await executeInit('./existing', { force: false });

      expect(result.success).toBe(false);
      expect(result.message).toContain('Use --force to overwrite');
    });
  });
});
