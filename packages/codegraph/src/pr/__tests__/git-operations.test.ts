/**
 * Tests for GitOperations
 *
 * @see REQ-CG-PR-002 - Git operations
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { GitOperations } from '../git-operations.js';
import { execSync } from 'node:child_process';

// Mock child_process.execSync
vi.mock('node:child_process', () => ({
  execSync: vi.fn(),
}));

describe('GitOperations', () => {
  const mockExecSync = execSync as unknown as ReturnType<typeof vi.fn>;

  beforeEach(() => {
    vi.clearAllMocks();
    // Default mock: repository is valid (returns string with utf-8 encoding)
    mockExecSync.mockReturnValue('.git\n');
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe('constructor', () => {
    it('should create instance with repository path', () => {
      const ops = new GitOperations({ repoPath: '/my/repo' });
      expect(ops).toBeDefined();
    });
    
    it('should throw for non-git directory', () => {
      mockExecSync.mockImplementation(() => {
        throw new Error('fatal: not a git repository');
      });
      expect(() => new GitOperations({ repoPath: '/not/a/repo' })).toThrow();
    });
  });

  describe('isGitRepository', () => {
    it('should return true for valid git repository', () => {
      mockExecSync.mockReturnValue('.git\n');
      const ops = new GitOperations({ repoPath: '/test/repo' });
      expect(ops.isGitRepository()).toBe(true);
    });
  });

  describe('getCurrentBranch', () => {
    it('should return current branch name', () => {
      mockExecSync.mockReturnValue('main\n');
      const ops = new GitOperations({ repoPath: '/test/repo' });
      const branch = ops.getCurrentBranch();
      expect(branch).toBe('main');
    });
  });

  describe('hasUncommittedChanges', () => {
    it('should return true when changes exist', () => {
      mockExecSync
        .mockReturnValueOnce('.git\n') // constructor - isGitRepository
        .mockReturnValueOnce('M src/file.ts\n'); // status
      const ops = new GitOperations({ repoPath: '/test/repo' });
      expect(ops.hasUncommittedChanges()).toBe(true);
    });

    it('should return false when no changes', () => {
      mockExecSync
        .mockReturnValueOnce('.git\n') // constructor
        .mockReturnValueOnce(''); // status
      const ops = new GitOperations({ repoPath: '/test/repo' });
      expect(ops.hasUncommittedChanges()).toBe(false);
    });
  });

  describe('createBranch', () => {
    it('should create new branch', () => {
      mockExecSync
        .mockReturnValueOnce('.git\n') // constructor - isGitRepository
        .mockReturnValueOnce('main\n') // getCurrentBranch
        .mockImplementationOnce(() => { throw new Error('not found'); }) // branchExists - not found
        .mockReturnValueOnce(''); // checkout -b
      const ops = new GitOperations({ repoPath: '/test/repo' });
      expect(() => ops.createBranch('feature/new-branch')).not.toThrow();
    });

    it('should handle branch already exists error', () => {
      mockExecSync
        .mockReturnValueOnce('.git\n') // constructor
        .mockReturnValueOnce('main\n') // getCurrentBranch
        .mockReturnValueOnce(''); // branchExists - found (no error)
      const ops = new GitOperations({ repoPath: '/test/repo' });
      expect(() => ops.createBranch('feature/new-branch')).toThrow('Branch already exists');
    });
  });

  describe('checkout', () => {
    it('should checkout branch', () => {
      mockExecSync.mockReturnValue('');
      const ops = new GitOperations({ repoPath: '/test/repo' });
      expect(() => ops.checkout('main')).not.toThrow();
    });
  });

  describe('stageFiles', () => {
    it('should stage specified files', () => {
      mockExecSync.mockReturnValue('');
      const ops = new GitOperations({ repoPath: '/test/repo' });
      expect(() => ops.stageFiles(['src/file.ts'])).not.toThrow();
    });
  });

  describe('commit', () => {
    it('should create commit with message', () => {
      mockExecSync
        .mockReturnValueOnce('.git\n') // constructor
        .mockReturnValueOnce('[main abc1234] Test commit\n') // commit
        .mockReturnValueOnce('abc1234|Test commit|John|john@example.com|2024-01-01T00:00:00+00:00\n'); // getLastCommit
      const ops = new GitOperations({ repoPath: '/test/repo' });
      const result = ops.commit('Test commit');
      expect(result).toBeDefined();
    });
  });

  describe('push', () => {
    it('should push to remote', () => {
      mockExecSync.mockReturnValue('');
      const ops = new GitOperations({ repoPath: '/test/repo' });
      expect(() => ops.push()).not.toThrow();
    });
  });

  describe('getCommitHistory', () => {
    it('should return commit history', () => {
      mockExecSync
        .mockReturnValueOnce('.git\n') // constructor
        .mockReturnValueOnce('abc1234|Test commit|John|john@example.com|2024-01-01T00:00:00+00:00\n'); // log
      const ops = new GitOperations({ repoPath: '/test/repo' });
      const history = ops.getCommitHistory(5);
      expect(history).toBeDefined();
      expect(Array.isArray(history)).toBe(true);
    });
  });

  describe('getDiffBetweenBranches', () => {
    it('should return diff between refs', () => {
      mockExecSync
        .mockReturnValueOnce('.git\n') // constructor
        .mockReturnValueOnce('diff --git a/file.ts b/file.ts\n'); // diff
      const ops = new GitOperations({ repoPath: '/test/repo' });
      const diff = ops.getDiffBetweenBranches('main', 'feature');
      expect(diff).toBeDefined();
      expect(typeof diff).toBe('string');
    });
  });
});
