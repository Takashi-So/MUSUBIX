/**
 * Path Normalizer Tests
 *
 * @packageDocumentation
 * @module utils/path-normalizer.test
 *
 * @see REQ-CLI-001 - initコマンドパス正規化
 * @see TSK-CLI-001 - パス正規化タスク
 */

import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest';
import {
  normalizePath,
  normalizePathSimple,
  isPathWithinBase,
} from './path-normalizer.js';

describe('path-normalizer', () => {
  const mockCwd = '/home/user/projects';

  beforeEach(() => {
    vi.spyOn(process, 'cwd').mockReturnValue(mockCwd);
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe('normalizePath', () => {
    it('should normalize relative path', () => {
      const result = normalizePath('./my-project');

      expect(result.absolutePath).toBe('/home/user/projects/my-project');
      expect(result.wasAbsolute).toBe(false);
      expect(result.originalPath).toBe('./my-project');
    });

    it('should handle absolute path without double concatenation', () => {
      // This was the bug: absolute paths were joined with cwd causing double paths
      const result = normalizePath('/absolute/path/to/project');

      expect(result.absolutePath).toBe('/absolute/path/to/project');
      expect(result.wasAbsolute).toBe(true);
      // Should NOT be: /home/user/projects/absolute/path/to/project
    });

    it('should remove trailing slash', () => {
      const result = normalizePath('./my-project/');

      expect(result.absolutePath).toBe('/home/user/projects/my-project');
      expect(result.hadTrailingSlash).toBe(true);
    });

    it('should handle empty path', () => {
      const result = normalizePath('');

      expect(result.absolutePath).toBe('/home/user/projects');
      expect(result.wasAbsolute).toBe(false);
    });

    it('should handle dot path', () => {
      const result = normalizePath('.');

      expect(result.absolutePath).toBe('/home/user/projects');
      expect(result.wasAbsolute).toBe(false);
    });

    it('should handle parent directory navigation', () => {
      const result = normalizePath('../other-project');

      expect(result.absolutePath).toBe('/home/user/other-project');
      expect(result.wasAbsolute).toBe(false);
    });

    it('should use custom basePath when provided', () => {
      const result = normalizePath('./subdir', {
        basePath: '/custom/base',
      });

      expect(result.absolutePath).toBe('/custom/base/subdir');
    });

    it('should handle whitespace-only path', () => {
      const result = normalizePath('   ');

      expect(result.absolutePath).toBe('/home/user/projects');
    });

    it('should normalize double slashes', () => {
      const result = normalizePath('./path//to//project');

      expect(result.absolutePath).toBe('/home/user/projects/path/to/project');
    });

    it('should handle path with spaces', () => {
      const result = normalizePath('./my project');

      expect(result.absolutePath).toBe('/home/user/projects/my project');
    });
  });

  describe('normalizePathSimple', () => {
    it('should return just the absolute path string', () => {
      const result = normalizePathSimple('./my-project');

      expect(result).toBe('/home/user/projects/my-project');
    });

    it('should handle absolute path correctly', () => {
      const result = normalizePathSimple('/absolute/path');

      expect(result).toBe('/absolute/path');
    });

    it('should use custom basePath', () => {
      const result = normalizePathSimple('./subdir', '/custom/base');

      expect(result).toBe('/custom/base/subdir');
    });
  });

  describe('isPathWithinBase', () => {
    it('should return true for path within base', () => {
      expect(isPathWithinBase('./subdir', mockCwd)).toBe(true);
    });

    it('should return true for same path', () => {
      expect(isPathWithinBase('.', mockCwd)).toBe(true);
    });

    it('should return false for path outside base', () => {
      expect(isPathWithinBase('/other/path', mockCwd)).toBe(false);
    });

    it('should return false for parent directory', () => {
      expect(isPathWithinBase('../sibling', mockCwd)).toBe(false);
    });
  });

  describe('edge cases', () => {
    it('should handle path with multiple trailing slashes', () => {
      const result = normalizePath('./project///');

      expect(result.absolutePath).toBe('/home/user/projects/project');
      expect(result.hadTrailingSlash).toBe(true);
    });

    it('should handle absolute path with trailing slash', () => {
      const result = normalizePath('/absolute/path/');

      expect(result.absolutePath).toBe('/absolute/path');
      expect(result.wasAbsolute).toBe(true);
      expect(result.hadTrailingSlash).toBe(true);
    });
  });
});
