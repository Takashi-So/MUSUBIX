/**
 * Tests for GitHubAdapter
 *
 * @see REQ-CG-PR-003 - GitHub integration
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { GitHubAdapter } from '../github-adapter.js';
import { exec } from 'node:child_process';

// Mock child_process.exec
vi.mock('node:child_process', () => ({
  exec: vi.fn(),
}));

describe('GitHubAdapter', () => {
  let adapter: GitHubAdapter;
  const mockExec = exec as unknown as ReturnType<typeof vi.fn>;

  beforeEach(() => {
    adapter = new GitHubAdapter();
    vi.clearAllMocks();
    // Clear environment
    delete process.env.GITHUB_TOKEN;
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe('authenticate', () => {
    it('should authenticate with GITHUB_TOKEN', async () => {
      process.env.GITHUB_TOKEN = 'test-token-123';

      const result = await adapter.authenticate();
      expect(result.success).toBe(true);
      expect(result.method).toBe('token');
    });

    it('should fall back to gh CLI', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        if (cmd.includes('gh auth status')) {
          cb(null, { stdout: 'Logged in to github.com as user\n', stderr: '' });
        }
      });

      const result = await adapter.authenticate();
      expect(result.success).toBe(true);
      expect(result.method).toBe('gh-cli');
    });

    it('should fail when no authentication available', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        if (cmd.includes('gh auth status')) {
          cb(new Error('not logged in'), { stdout: '', stderr: 'not logged in' });
        }
      });

      const result = await adapter.authenticate();
      expect(result.success).toBe(false);
      expect(result.error).toBeDefined();
    });
  });

  describe('createPullRequest', () => {
    beforeEach(() => {
      // Setup authenticated state
      process.env.GITHUB_TOKEN = 'test-token';
    });

    it('should create PR using gh CLI', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        if (cmd.includes('gh pr create')) {
          cb(null, { 
            stdout: JSON.stringify({
              url: 'https://github.com/owner/repo/pull/123',
              number: 123,
              id: 'PR_123',
            }),
            stderr: '' 
          });
        }
      });

      await adapter.authenticate();
      const result = await adapter.createPullRequest({
        owner: 'owner',
        repo: 'repo',
        head: 'feature/test',
        base: 'main',
        title: 'Test PR',
        body: 'Test body',
      });

      expect(result.success).toBe(true);
      expect(result.pr?.number).toBe(123);
      expect(result.pr?.url).toContain('pull/123');
    });

    it('should handle PR creation failure', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        if (cmd.includes('gh pr create')) {
          cb(new Error('PR creation failed'), null);
        }
      });

      await adapter.authenticate();
      const result = await adapter.createPullRequest({
        owner: 'owner',
        repo: 'repo',
        head: 'feature/test',
        base: 'main',
        title: 'Test PR',
        body: 'Test body',
      });

      expect(result.success).toBe(false);
      expect(result.error).toBeDefined();
    });

    it('should fail when not authenticated', async () => {
      delete process.env.GITHUB_TOKEN;

      const result = await adapter.createPullRequest({
        owner: 'owner',
        repo: 'repo',
        head: 'feature/test',
        base: 'main',
        title: 'Test PR',
        body: 'Test body',
      });

      expect(result.success).toBe(false);
      expect(result.error).toContain('Not authenticated');
    });

    it('should support draft PRs', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        expect(cmd).toContain('--draft');
        cb(null, { 
          stdout: JSON.stringify({
            url: 'https://github.com/owner/repo/pull/124',
            number: 124,
            id: 'PR_124',
          }),
          stderr: '' 
        });
      });

      await adapter.authenticate();
      const result = await adapter.createPullRequest({
        owner: 'owner',
        repo: 'repo',
        head: 'feature/test',
        base: 'main',
        title: 'Draft PR',
        body: 'Test body',
        draft: true,
      });

      expect(result.success).toBe(true);
    });
  });

  describe('addLabels', () => {
    it('should add labels to PR', async () => {
      process.env.GITHUB_TOKEN = 'test-token';
      mockExec.mockImplementation((cmd, opts, cb) => {
        if (cmd.includes('gh pr edit')) {
          cb(null, { stdout: '', stderr: '' });
        }
      });

      await adapter.authenticate();
      const result = await adapter.addLabels('owner', 'repo', 123, ['bug', 'enhancement']);

      expect(result.success).toBe(true);
    });

    it('should handle label addition failure', async () => {
      process.env.GITHUB_TOKEN = 'test-token';
      mockExec.mockImplementation((cmd, opts, cb) => {
        if (cmd.includes('gh pr edit')) {
          cb(new Error('Label not found'), null);
        }
      });

      await adapter.authenticate();
      const result = await adapter.addLabels('owner', 'repo', 123, ['nonexistent']);

      expect(result.success).toBe(false);
    });
  });

  describe('addReviewers', () => {
    it('should add reviewers to PR', async () => {
      process.env.GITHUB_TOKEN = 'test-token';
      mockExec.mockImplementation((cmd, opts, cb) => {
        if (cmd.includes('gh pr edit')) {
          expect(cmd).toContain('--add-reviewer');
          cb(null, { stdout: '', stderr: '' });
        }
      });

      await adapter.authenticate();
      const result = await adapter.addReviewers('owner', 'repo', 123, ['reviewer1', 'reviewer2']);

      expect(result.success).toBe(true);
    });
  });

  describe('addAssignees', () => {
    it('should add assignees to PR', async () => {
      process.env.GITHUB_TOKEN = 'test-token';
      mockExec.mockImplementation((cmd, opts, cb) => {
        if (cmd.includes('gh pr edit')) {
          expect(cmd).toContain('--add-assignee');
          cb(null, { stdout: '', stderr: '' });
        }
      });

      await adapter.authenticate();
      const result = await adapter.addAssignees('owner', 'repo', 123, ['assignee1']);

      expect(result.success).toBe(true);
    });
  });

  describe('isGhCliAvailable', () => {
    it('should return true when gh CLI is installed', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        if (cmd.includes('gh --version')) {
          cb(null, { stdout: 'gh version 2.40.0\n', stderr: '' });
        }
      });

      const result = await adapter.isGhCliAvailable();
      expect(result).toBe(true);
    });

    it('should return false when gh CLI is not installed', async () => {
      mockExec.mockImplementation((cmd, opts, cb) => {
        if (cmd.includes('gh --version')) {
          cb(new Error('command not found'), null);
        }
      });

      const result = await adapter.isGhCliAvailable();
      expect(result).toBe(false);
    });
  });
});
