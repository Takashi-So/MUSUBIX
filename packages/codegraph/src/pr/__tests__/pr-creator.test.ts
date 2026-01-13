/**
 * Tests for PRCreator
 *
 * @see REQ-CG-PR-006 - Main orchestrator
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { PRCreator, createPRCreator } from '../pr-creator.js';
import type { RefactoringSuggestion } from '../types.js';

// Mock modules with class implementations
vi.mock('../git-operations.js', () => {
  return {
    GitOperations: class MockGitOperations {
      isGitRepository() { return true; }
      getCurrentBranch() { return 'main'; }
      getDefaultBranch() { return 'main'; }
      hasUncommittedChanges() { return false; }
      createBranch() {}
      checkout() {}
      commit() { return { hash: 'abc1234', message: 'test' }; }
      push() {}
      parseRemoteUrl() { return { owner: 'owner', repo: 'repo' }; }
      stageFiles() {}
      getRemoteUrl() { return 'https://github.com/owner/repo.git'; }
    },
  };
});

vi.mock('../github-adapter.js', () => {
  return {
    GitHubAdapter: class MockGitHubAdapter {
      async authenticate() { return { authenticated: true, method: 'token' }; }
      async createPullRequest() {
        return { url: 'https://github.com/owner/repo/pull/1', number: 1, id: 'PR_1' };
      }
      async addLabels() {}
      async addReviewers() {}
      async addAssignees() {}
      isAuthenticated() { return true; }
    },
  };
});

vi.mock('../refactoring-applier.js', () => {
  return {
    RefactoringApplier: class MockRefactoringApplier {
      validateChanges() { return { valid: true, errors: [] }; }
      canApply(suggestion: { changes: unknown[] }) { 
        return { canApply: suggestion.changes.length > 0, reason: suggestion.changes.length === 0 ? 'No changes' : undefined }; 
      }
      async apply() {
        return { success: true, appliedFiles: ['src/file.ts'], linesAdded: 10, linesDeleted: 5 };
      }
      async preview() {
        return {
          success: true,
          diffs: [{ filePath: 'src/file.ts', changeType: 'modified', additions: 10, deletions: 5, diff: '-old\n+new' }],
        };
      }
      async rollback() { return { success: true }; }
    },
  };
});

describe('PRCreator', () => {
  let creator: PRCreator;

  beforeEach(() => {
    vi.clearAllMocks();
    creator = createPRCreator('/test/repo');
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
    });
  });

  describe('initializeOffline', () => {
    it('should initialize for offline operations', async () => {
      const result = await creator.initializeOffline();
      expect(result.success).toBe(true);
    });
  });

  describe('isInitialized', () => {
    it('should return false before initialization', () => {
      expect(creator.isInitialized()).toBe(false);
    });

    it('should return true after initialization', async () => {
      await creator.initialize();
      expect(creator.isInitialized()).toBe(true);
    });
  });

  describe('getState', () => {
    it('should return uninitialized state initially', () => {
      expect(creator.getState()).toBe('uninitialized');
    });

    it('should return full state after full initialization', async () => {
      await creator.initialize();
      expect(creator.getState()).toBe('full');
    });

    it('should return offline state after offline initialization', async () => {
      await creator.initializeOffline();
      expect(creator.getState()).toBe('offline');
    });
  });

  describe('validate', () => {
    const validSuggestion: RefactoringSuggestion = {
      id: 'test-001',
      type: 'extract_method',
      title: 'Extract method',
      description: 'Extract repeated code',
      changes: [
        { filePath: 'src/file.ts', type: 'modify', content: 'new content', description: 'Test' },
      ],
      confidence: 0.9,
    };

    it('should validate valid suggestion', async () => {
      await creator.initializeOffline();
      const result = creator.validate(validSuggestion);
      expect(result.valid).toBe(true);
    });

    it('should reject suggestion with empty changes', async () => {
      await creator.initializeOffline();
      const suggestion: RefactoringSuggestion = {
        ...validSuggestion,
        id: 'test-002',
        changes: [],
      };
      const result = creator.validate(suggestion);
      expect(result.valid).toBe(false);
    });
  });

  describe('preview', () => {
    it('should generate preview', async () => {
      await creator.initializeOffline();
      
      const suggestion: RefactoringSuggestion = {
        id: 'preview-001',
        type: 'extract_method',
        title: 'Preview test',
        description: 'Test preview',
        changes: [
          { filePath: 'src/file.ts', type: 'modify', content: 'new content', description: 'Test' },
        ],
        confidence: 0.85,
      };

      const result = await creator.preview({ suggestion });
      expect(result).toBeDefined();
      expect(result.branchName).toBeDefined();
    });
  });
});
