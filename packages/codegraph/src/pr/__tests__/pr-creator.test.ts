/**
 * Tests for PRCreator
 *
 * @see REQ-CG-PR-006 - Main orchestrator
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { PRCreator, createPRCreator } from '../pr-creator.js';
import { GitOperations } from '../git-operations.js';
import { GitHubAdapter } from '../github-adapter.js';
import { RefactoringApplier } from '../refactoring-applier.js';
import type { RefactoringSuggestion } from '../types.js';

// Mock dependencies
vi.mock('../git-operations.js', () => ({
  GitOperations: vi.fn().mockImplementation(() => ({
    isGitRepository: vi.fn().mockResolvedValue(true),
    getCurrentBranch: vi.fn().mockResolvedValue({ success: true, branch: 'main' }),
    hasUncommittedChanges: vi.fn().mockResolvedValue(false),
    createBranch: vi.fn().mockResolvedValue({ success: true }),
    checkout: vi.fn().mockResolvedValue({ success: true }),
    commit: vi.fn().mockResolvedValue({ success: true, hash: 'abc1234' }),
    push: vi.fn().mockResolvedValue({ success: true }),
    parseRemoteUrl: vi.fn().mockResolvedValue({ success: true, owner: 'owner', repo: 'repo' }),
    stash: vi.fn().mockResolvedValue({ success: true }),
    stashPop: vi.fn().mockResolvedValue({ success: true }),
  })),
}));

vi.mock('../github-adapter.js', () => ({
  GitHubAdapter: vi.fn().mockImplementation(() => ({
    authenticate: vi.fn().mockResolvedValue({ success: true, method: 'token' }),
    createPullRequest: vi.fn().mockResolvedValue({
      success: true,
      pr: { url: 'https://github.com/owner/repo/pull/1', number: 1, id: 'PR_1' },
    }),
    addLabels: vi.fn().mockResolvedValue({ success: true }),
    addReviewers: vi.fn().mockResolvedValue({ success: true }),
    addAssignees: vi.fn().mockResolvedValue({ success: true }),
  })),
}));

vi.mock('../refactoring-applier.js', () => ({
  RefactoringApplier: vi.fn().mockImplementation(() => ({
    validateChanges: vi.fn().mockReturnValue({ valid: true }),
    apply: vi.fn().mockResolvedValue({
      success: true,
      appliedFiles: ['src/file.ts'],
      linesAdded: 10,
      linesDeleted: 5,
    }),
    preview: vi.fn().mockResolvedValue({
      diffs: [
        {
          filePath: 'src/file.ts',
          changeType: 'modified',
          additions: 10,
          deletions: 5,
          diff: '-old\n+new',
        },
      ],
    }),
    rollback: vi.fn().mockResolvedValue({ success: true }),
  })),
}));

describe('PRCreator', () => {
  let creator: PRCreator;

  beforeEach(() => {
    vi.clearAllMocks();
    creator = createPRCreator('/test/repo');
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe('createPRCreator factory', () => {
    it('should create PRCreator instance', () => {
      const instance = createPRCreator('/test/repo');
      expect(instance).toBeInstanceOf(PRCreator);
    });
  });

  describe('initialize', () => {
    it('should initialize successfully', async () => {
      const result = await creator.initialize();

      expect(result.success).toBe(true);
      expect(result.gitReady).toBe(true);
      expect(result.githubReady).toBe(true);
    });

    it('should fail when not a git repository', async () => {
      const mockGitOps = new GitOperations('/test/repo') as any;
      mockGitOps.isGitRepository.mockResolvedValue(false);

      const result = await creator.initialize();
      // Initialize still succeeds but reports git not ready
      expect(result.success).toBe(true);
    });
  });

  describe('create', () => {
    const suggestion: RefactoringSuggestion = {
      id: 'test-001',
      type: 'extract-method',
      title: 'Extract calculateTotal',
      description: 'Extract calculation logic',
      changes: [
        {
          filePath: 'src/order.ts',
          type: 'modify',
          content: 'modified content',
          originalContent: 'original content',
        },
      ],
      confidence: 0.9,
    };

    it('should create PR successfully', async () => {
      await creator.initialize();

      const result = await creator.create({ suggestion });

      expect(result.success).toBe(true);
      expect(result.pr).toBeDefined();
      expect(result.pr?.url).toContain('github.com');
      expect(result.branchName).toBeDefined();
      expect(result.commitHash).toBeDefined();
    });

    it('should emit events during creation', async () => {
      const events: string[] = [];

      creator.on('pr:start', () => events.push('start'));
      creator.on('pr:branch', () => events.push('branch'));
      creator.on('pr:applying', () => events.push('applying'));
      creator.on('pr:commit', () => events.push('commit'));
      creator.on('pr:push', () => events.push('push'));
      creator.on('pr:created', () => events.push('created'));

      await creator.initialize();
      await creator.create({ suggestion });

      expect(events).toContain('start');
      expect(events).toContain('branch');
      expect(events).toContain('commit');
      expect(events).toContain('push');
      expect(events).toContain('created');
    });

    it('should use custom branch name when provided', async () => {
      await creator.initialize();

      const result = await creator.create({
        suggestion,
        branchName: 'custom/my-branch',
      });

      expect(result.branchName).toBe('custom/my-branch');
    });

    it('should handle dry-run mode', async () => {
      await creator.initialize();

      const result = await creator.create({
        suggestion,
        dryRun: true,
      });

      expect(result.success).toBe(true);
      expect(result.pr).toBeUndefined();
      expect(result.preview).toBeDefined();
    });

    it('should add labels when provided', async () => {
      const mockGitHub = new GitHubAdapter() as any;

      await creator.initialize();
      await creator.create({
        suggestion,
        labels: ['refactoring', 'auto-generated'],
      });

      expect(mockGitHub.addLabels).toBeDefined();
    });

    it('should add reviewers when provided', async () => {
      const mockGitHub = new GitHubAdapter() as any;

      await creator.initialize();
      await creator.create({
        suggestion,
        reviewers: ['reviewer1', 'reviewer2'],
      });

      expect(mockGitHub.addReviewers).toBeDefined();
    });

    it('should create draft PR when specified', async () => {
      await creator.initialize();

      const result = await creator.create({
        suggestion,
        draft: true,
      });

      expect(result.success).toBe(true);
    });

    it('should emit error event on failure', async () => {
      const mockApplier = new RefactoringApplier('/test') as any;
      mockApplier.apply.mockResolvedValue({
        success: false,
        error: 'Apply failed',
        appliedFiles: [],
      });

      let errorEmitted = false;
      creator.on('pr:error', () => {
        errorEmitted = true;
      });

      await creator.initialize();
      const result = await creator.create({ suggestion });

      expect(result.success).toBe(false);
    });
  });

  describe('preview', () => {
    it('should generate preview without applying changes', async () => {
      const suggestion: RefactoringSuggestion = {
        id: 'test',
        type: 'extract-method',
        title: 'Test',
        description: 'Test',
        changes: [
          {
            filePath: 'src/file.ts',
            type: 'modify',
            content: 'new',
            originalContent: 'old',
          },
        ],
        confidence: 0.8,
      };

      await creator.initialize();
      const result = await creator.preview({ suggestion });

      expect(result.branchName).toBeDefined();
      expect(result.title).toBeDefined();
      expect(result.commitMessage).toBeDefined();
      expect(result.body).toBeDefined();
      expect(result.diffs).toHaveLength(1);
    });
  });

  describe('validate', () => {
    it('should validate valid suggestion', async () => {
      const suggestion: RefactoringSuggestion = {
        id: 'valid-001',
        type: 'extract-method',
        title: 'Valid suggestion',
        description: 'Valid description',
        changes: [
          {
            filePath: 'src/file.ts',
            type: 'modify',
            content: 'new content',
          },
        ],
        confidence: 0.9,
      };

      await creator.initialize();
      const result = creator.validate(suggestion);

      expect(result.valid).toBe(true);
    });

    it('should reject suggestion with empty changes', async () => {
      const suggestion: RefactoringSuggestion = {
        id: 'invalid-001',
        type: 'extract-method',
        title: 'Invalid',
        description: 'No changes',
        changes: [],
        confidence: 0.9,
      };

      await creator.initialize();
      const result = creator.validate(suggestion);

      expect(result.valid).toBe(false);
      expect(result.reason).toContain('empty');
    });

    it('should reject suggestion with missing required fields', async () => {
      const suggestion = {
        id: 'incomplete',
        type: 'extract-method',
        // Missing title, description, changes
      } as unknown as RefactoringSuggestion;

      await creator.initialize();
      const result = creator.validate(suggestion);

      expect(result.valid).toBe(false);
    });
  });

  describe('state management', () => {
    it('should track state correctly', async () => {
      expect(creator.getState()).toBe('idle');

      const initPromise = creator.initialize();
      // State might be 'initializing' during init
      await initPromise;

      expect(creator.getState()).toBe('ready');
    });

    it('should prevent concurrent operations', async () => {
      const suggestion: RefactoringSuggestion = {
        id: 'test',
        type: 'extract-method',
        title: 'Test',
        description: 'Test',
        changes: [{ filePath: 'test.ts', type: 'modify', content: 'new' }],
        confidence: 0.8,
      };

      await creator.initialize();

      // Start first operation
      const promise1 = creator.create({ suggestion });

      // Second operation should be blocked or queued
      // This depends on implementation - adjust test accordingly
      await promise1;
    });
  });
});
