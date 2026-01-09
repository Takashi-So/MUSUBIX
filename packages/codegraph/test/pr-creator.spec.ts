/**
 * PRCreator Unit Tests
 *
 * @see REQ-CG-v234-001 - initializeOffline() for auth-free preview
 * @see REQ-CG-v234-003 - PRCreator state management
 * @see REQ-CG-v234-004 - Improved error messages
 * @see TSK-v234-009
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { PRCreator, PRCreatorError, PRErrorMessages, type PRCreatorState, type RefactoringSuggestion } from '../src/pr/index.js';
import { tmpdir } from 'node:os';
import { mkdtempSync, mkdirSync } from 'node:fs';
import { execSync } from 'node:child_process';
import { join } from 'node:path';

describe('PRCreator', () => {
  let prCreator: PRCreator;
  let tempRepoPath: string;

  beforeEach(() => {
    // Create a temporary git repository
    tempRepoPath = mkdtempSync(join(tmpdir(), 'musubix-pr-test-'));
    mkdirSync(join(tempRepoPath, 'src'), { recursive: true });
    execSync('git init', { cwd: tempRepoPath, stdio: 'ignore' });
    execSync('git config user.email "test@test.com"', { cwd: tempRepoPath, stdio: 'ignore' });
    execSync('git config user.name "Test User"', { cwd: tempRepoPath, stdio: 'ignore' });
    execSync('echo "initial" > README.md && git add . && git commit -m "Initial commit"', { cwd: tempRepoPath, stdio: 'ignore' });
    
    prCreator = new PRCreator({ repoPath: tempRepoPath });
  });

  describe('State Management', () => {
    it('should start in uninitialized state', () => {
      expect(prCreator.getState()).toBe('uninitialized');
    });

    it('should transition to offline state after initializeOffline()', async () => {
      const result = await prCreator.initializeOffline();
      expect(result.success).toBe(true);
      expect(prCreator.getState()).toBe('offline');
    });

    it('should not allow double offline initialization', async () => {
      await prCreator.initializeOffline();
      const result = await prCreator.initializeOffline();
      // Already initialized is still success (idempotent)
      expect(result.success).toBe(true);
    });
  });

  describe('Preview in Offline Mode', () => {
    const mockSuggestion: RefactoringSuggestion = {
      id: 'test-001',
      entityId: 'sql-query-fn',
      type: 'security',
      title: 'Fix SQL Injection',
      description: 'Use parameterized queries',
      reason: 'Direct string interpolation in SQL queries can lead to SQL injection attacks',
      severity: 'critical',
      changes: [{
        filePath: 'src/db.ts',
        originalCode: 'query(`SELECT * FROM users WHERE id = ${id}`)',
        newCode: 'query("SELECT * FROM users WHERE id = ?", [id])',
        startLine: 42,
        endLine: 42,
        description: 'Use parameterized query',
      }],
      impact: {
        filesAffected: 1,
        linesChanged: 1,
        dependencies: [],
      },
      confidence: 0.95,
      createdAt: new Date(),
    };

    it('should allow preview in offline mode', async () => {
      await prCreator.initializeOffline();

      const preview = prCreator.previewSuggestion(mockSuggestion);

      expect(preview).toBeDefined();
      expect(preview.title).toBeDefined();
      expect(preview.body).toBeDefined();
    });

    it('should not allow preview in uninitialized state', () => {
      expect(() => prCreator.previewSuggestion(mockSuggestion)).toThrow(PRCreatorError);
    });
  });

  describe('Create PR Requires Full Initialization', () => {
    const mockSuggestion: RefactoringSuggestion = {
      id: 'test-002',
      entityId: 'service-method',
      type: 'code_quality',
      title: 'Refactor Function',
      description: 'Extract method for better readability',
      reason: 'Long method can be split for better maintainability',
      severity: 'medium',
      changes: [{
        filePath: 'src/service.ts',
        originalCode: '// original code',
        newCode: '// suggested code',
        startLine: 100,
        endLine: 100,
        description: 'Extract method',
      }],
      impact: {
        filesAffected: 1,
        linesChanged: 1,
        dependencies: [],
      },
      confidence: 0.85,
      createdAt: new Date(),
    };

    it('should fail to create PR in offline mode with helpful error', async () => {
      await prCreator.initializeOffline();

      try {
        await prCreator.create({ suggestion: mockSuggestion });
        expect.fail('Should have thrown an error');
      } catch (error) {
        expect(error).toBeInstanceOf(PRCreatorError);
        const prError = error as PRCreatorError;
        expect(prError.code).toBe('OFFLINE_MODE');
        expect(prError.suggestion).toBeDefined();
        expect(prError.suggestion).toContain('initialize()');
      }
    });

    it('should fail to create PR in uninitialized state', async () => {
      try {
        await prCreator.create({ suggestion: mockSuggestion });
        expect.fail('Should have thrown an error');
      } catch (error) {
        expect(error).toBeInstanceOf(PRCreatorError);
        const prError = error as PRCreatorError;
        expect(prError.code).toBe('NOT_INITIALIZED');
      }
    });
  });
});

describe('PRCreatorError', () => {
  it('should create error from code', () => {
    const error = PRCreatorError.fromCode('NOT_INITIALIZED');
    expect(error.code).toBe('NOT_INITIALIZED');
    expect(error.message).toBe(PRErrorMessages.NOT_INITIALIZED.message);
    expect(error.suggestion).toBeDefined();
  });

  it('should include additional info in message', () => {
    const error = PRCreatorError.fromCode('AUTH_FAILED', 'Token expired');
    expect(error.message).toContain('Token expired');
  });

  it('should provide full message with suggestion', () => {
    const error = PRCreatorError.fromCode('NOT_INITIALIZED');
    const fullMessage = error.getFullMessage();
    expect(fullMessage).toContain(PRErrorMessages.NOT_INITIALIZED.message);
    expect(fullMessage).toContain('💡');
  });

  it('should have correct error codes', () => {
    expect(PRErrorMessages.NOT_INITIALIZED).toBeDefined();
    expect(PRErrorMessages.AUTH_FAILED).toBeDefined();
    expect(PRErrorMessages.OFFLINE_MODE).toBeDefined();
    expect(PRErrorMessages.PR_CREATE_FAILED).toBeDefined();
  });
});
