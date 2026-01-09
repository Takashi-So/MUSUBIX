/**
 * Tests for GitOperations
 *
 * @see REQ-CG-PR-002 - Git operations
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { GitOperations } from '../git-operations.js';
import { exec } from 'node:child_process';
import { promisify } from 'node:util';

// Mock child_process.exec
vi.mock('node:child_process', () => ({
  exec: vi.fn(),
}));

vi.mock('node:util', () => ({
  promisify: vi.fn((fn) => fn),
}));

describe('GitOperations', () => {
  let gitOps: GitOperations;
  const mockExec = exec as unknown as ReturnType<typeof vi.fn>;

  beforeEach(() => {
    gitOps = new GitOperations('/test/repo');
    vi.clearAllMocks();
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe('constructor', () => {
    it('should create instance with repository path', () => {
      const ops = new GitOperations('/my/repo');
      expect(ops).toBeDefined();
    });
  });

  describe('isGitRepository', () => {
    it('should return true for valid git repository', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        cb(null, { stdout: '/test/repo/.git', stderr: '' });
      });

      const result = await gitOps.isGitRepository();
      expect(result).toBe(true);
    });

    it('should return false for non-git directory', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        cb(new Error('fatal: not a git repository'), { stdout: '', stderr: '' });
      });

      const result = await gitOps.isGitRepository();
      expect(result).toBe(false);
    });
  });

  describe('getCurrentBranch', () => {
    it('should return current branch name', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        cb(null, { stdout: 'main\n', stderr: '' });
      });

      const result = await gitOps.getCurrentBranch();
      expect(result.success).toBe(true);
      expect(result.branch).toBe('main');
    });

    it('should handle detached HEAD state', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        cb(new Error('HEAD detached'), { stdout: '', stderr: '' });
      });

      const result = await gitOps.getCurrentBranch();
      expect(result.success).toBe(false);
      expect(result.error).toBeDefined();
    });
  });

  describe('hasUncommittedChanges', () => {
    it('should return true when changes exist', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        cb(null, { stdout: 'M src/file.ts\n', stderr: '' });
      });

      const result = await gitOps.hasUncommittedChanges();
      expect(result).toBe(true);
    });

    it('should return false when no changes', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        cb(null, { stdout: '', stderr: '' });
      });

      const result = await gitOps.hasUncommittedChanges();
      expect(result).toBe(false);
    });
  });

  describe('createBranch', () => {
    it('should create new branch', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        cb(null, { stdout: '', stderr: '' });
      });

      const result = await gitOps.createBranch('feature/new-branch');
      expect(result.success).toBe(true);
    });

    it('should handle branch already exists error', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        cb(new Error('fatal: A branch named \'feature/new-branch\' already exists'), null);
      });

      const result = await gitOps.createBranch('feature/new-branch');
      expect(result.success).toBe(false);
      expect(result.error).toContain('already exists');
    });
  });

  describe('checkout', () => {
    it('should checkout branch', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        cb(null, { stdout: '', stderr: '' });
      });

      const result = await gitOps.checkout('main');
      expect(result.success).toBe(true);
    });

    it('should handle checkout error', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        cb(new Error('pathspec did not match'), null);
      });

      const result = await gitOps.checkout('nonexistent');
      expect(result.success).toBe(false);
    });
  });

  describe('commit', () => {
    it('should create commit with message', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        if (cmd.includes('git add')) {
          cb(null, { stdout: '', stderr: '' });
        } else if (cmd.includes('git commit')) {
          cb(null, { stdout: '[feature/test abc1234] Test commit\n', stderr: '' });
        } else if (cmd.includes('git rev-parse')) {
          cb(null, { stdout: 'abc1234567890\n', stderr: '' });
        }
      });

      const result = await gitOps.commit('Test commit', ['src/file.ts']);
      expect(result.success).toBe(true);
      expect(result.hash).toBeDefined();
    });
  });

  describe('push', () => {
    it('should push to remote', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        cb(null, { stdout: '', stderr: '' });
      });

      const result = await gitOps.push('feature/test');
      expect(result.success).toBe(true);
    });

    it('should push with force option', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        expect(cmd).toContain('--force');
        cb(null, { stdout: '', stderr: '' });
      });

      const result = await gitOps.push('feature/test', { force: true });
      expect(result.success).toBe(true);
    });

    it('should handle push rejection', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        cb(new Error('rejected - non-fast-forward'), null);
      });

      const result = await gitOps.push('feature/test');
      expect(result.success).toBe(false);
      expect(result.error).toContain('rejected');
    });
  });

  describe('parseRemoteUrl', () => {
    it('should parse HTTPS remote URL', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        cb(null, { stdout: 'https://github.com/owner/repo.git\n', stderr: '' });
      });

      const result = await gitOps.parseRemoteUrl();
      expect(result.success).toBe(true);
      expect(result.owner).toBe('owner');
      expect(result.repo).toBe('repo');
    });

    it('should parse SSH remote URL', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        cb(null, { stdout: 'git@github.com:owner/repo.git\n', stderr: '' });
      });

      const result = await gitOps.parseRemoteUrl();
      expect(result.success).toBe(true);
      expect(result.owner).toBe('owner');
      expect(result.repo).toBe('repo');
    });

    it('should handle no remote configured', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        cb(new Error('No remote configured'), null);
      });

      const result = await gitOps.parseRemoteUrl();
      expect(result.success).toBe(false);
    });
  });

  describe('stash', () => {
    it('should stash changes', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        cb(null, { stdout: 'Saved working directory\n', stderr: '' });
      });

      const result = await gitOps.stash('WIP: before PR');
      expect(result.success).toBe(true);
    });

    it('should handle nothing to stash', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        cb(null, { stdout: 'No local changes to save\n', stderr: '' });
      });

      const result = await gitOps.stash();
      expect(result.success).toBe(true);
    });
  });

  describe('stashPop', () => {
    it('should pop stashed changes', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        cb(null, { stdout: '', stderr: '' });
      });

      const result = await gitOps.stashPop();
      expect(result.success).toBe(true);
    });
  });
});
