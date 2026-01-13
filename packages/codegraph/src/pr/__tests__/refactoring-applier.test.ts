/**
 * Tests for RefactoringApplier
 *
 * @see REQ-CG-PR-004 - Code change application
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { RefactoringApplier } from '../refactoring-applier.js';
import * as fs from 'node:fs';
import type { CodeChange } from '../types.js';

// Mock fs module
vi.mock('node:fs', () => ({
  existsSync: vi.fn(),
  readFileSync: vi.fn(),
  writeFileSync: vi.fn(),
  mkdirSync: vi.fn(),
  unlinkSync: vi.fn(),
  cpSync: vi.fn(),
  rmSync: vi.fn(),
  statSync: vi.fn(),
}));

describe('RefactoringApplier', () => {
  let applier: RefactoringApplier;
  const mockFs = fs as unknown as {
    existsSync: ReturnType<typeof vi.fn>;
    readFileSync: ReturnType<typeof vi.fn>;
    writeFileSync: ReturnType<typeof vi.fn>;
    mkdirSync: ReturnType<typeof vi.fn>;
    unlinkSync: ReturnType<typeof vi.fn>;
    cpSync: ReturnType<typeof vi.fn>;
    rmSync: ReturnType<typeof vi.fn>;
    statSync: ReturnType<typeof vi.fn>;
  };

  beforeEach(() => {
    applier = new RefactoringApplier({ repoPath: '/test/repo' });
    vi.clearAllMocks();
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe('constructor', () => {
    it('should create instance with options', () => {
      const instance = new RefactoringApplier({ repoPath: '/my/repo' });
      expect(instance).toBeDefined();
    });

    it('should create instance with all options', () => {
      const instance = new RefactoringApplier({
        repoPath: '/my/repo',
        createBackups: false,
        backupDir: '.backups',
        validate: false,
      });
      expect(instance).toBeDefined();
    });
  });

  describe('validateChanges', () => {
    it('should validate existing file for modify', () => {
      const fileContent = 'line1\nline2\nline3\nline4\nline5';
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readFileSync.mockReturnValue(fileContent);

      const changes: CodeChange[] = [
        {
          filePath: 'src/file.ts',
          startLine: 2,
          endLine: 3,
          originalCode: 'line2\nline3',
          newCode: 'modified line2\nmodified line3',
          description: 'Modify file',
        },
      ];

      const result = applier.validateChanges(changes);
      expect(result).toBeNull(); // null means valid
    });

    it('should fail validation when file does not exist for modify', () => {
      mockFs.existsSync.mockReturnValue(false);

      const changes: CodeChange[] = [
        {
          filePath: 'src/nonexistent.ts',
          startLine: 1,
          endLine: 2,
          originalCode: 'some code',
          newCode: 'new code',
          description: 'Modify nonexistent',
        },
      ];

      const result = applier.validateChanges(changes);
      expect(result).not.toBeNull();
      expect(result).toContain('not found');
    });

    it('should fail validation when original content does not match', () => {
      const fileContent = 'line1\ndifferent content\nline3';
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readFileSync.mockReturnValue(fileContent);

      const changes: CodeChange[] = [
        {
          filePath: 'src/file.ts',
          startLine: 2,
          endLine: 2,
          originalCode: 'expected content',
          newCode: 'new content',
          description: 'Modify file',
        },
      ];

      const result = applier.validateChanges(changes);
      expect(result).not.toBeNull();
      expect(result).toContain('mismatch');
    });

    it('should allow non-existing file for create (empty originalCode)', () => {
      mockFs.existsSync.mockReturnValue(false);

      const changes: CodeChange[] = [
        {
          filePath: 'src/new-file.ts',
          startLine: 1,
          endLine: 1,
          originalCode: '',
          newCode: 'new file content',
          description: 'Create new file',
        },
      ];

      const result = applier.validateChanges(changes);
      expect(result).toBeNull();
    });

    it('should fail validation when startLine is invalid', () => {
      const fileContent = 'line1\nline2\nline3';
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readFileSync.mockReturnValue(fileContent);

      const changes: CodeChange[] = [
        {
          filePath: 'src/file.ts',
          startLine: 0,
          endLine: 1,
          originalCode: 'line1',
          newCode: 'new content',
          description: 'Invalid startLine',
        },
      ];

      const result = applier.validateChanges(changes);
      expect(result).not.toBeNull();
      expect(result).toContain('Invalid start line');
    });

    it('should fail validation when endLine exceeds file length', () => {
      const fileContent = 'line1\nline2\nline3';
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readFileSync.mockReturnValue(fileContent);

      const changes: CodeChange[] = [
        {
          filePath: 'src/file.ts',
          startLine: 1,
          endLine: 10,
          originalCode: 'line1',
          newCode: 'new content',
          description: 'endLine too large',
        },
      ];

      const result = applier.validateChanges(changes);
      expect(result).not.toBeNull();
      expect(result).toContain('exceeds file length');
    });
  });

  describe('apply', () => {
    it('should apply modify changes', async () => {
      const fileContent = 'line1\nline2\nline3\nline4\nline5';
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readFileSync.mockReturnValue(fileContent);
      mockFs.writeFileSync.mockImplementation(() => {});

      const result = await applier.apply({
        id: 'test-001',
        entityId: 'entity-001',
        type: 'extract_method',
        title: 'Test',
        description: 'Test',
        changes: [
          {
            filePath: 'src/file.ts',
            startLine: 2,
            endLine: 3,
            originalCode: 'line2\nline3',
            newCode: 'modified line2\nmodified line3',
            description: 'Modify',
          },
        ],
        confidence: 0.9,
        priority: 'medium',
      });

      expect(result.success).toBe(true);
    });

    it('should return failure when validation fails', async () => {
      const validatingApplier = new RefactoringApplier({
        repoPath: '/test/repo',
        validate: true,
      });
      
      mockFs.existsSync.mockReturnValue(false);

      const result = await validatingApplier.apply({
        id: 'test-004',
        entityId: 'entity-004',
        type: 'extract_method',
        title: 'Test',
        description: 'Test',
        changes: [
          {
            filePath: 'src/nonexistent.ts',
            startLine: 1,
            endLine: 2,
            originalCode: 'some code',
            newCode: 'new code',
            description: 'Modify nonexistent',
          },
        ],
        confidence: 0.9,
        priority: 'medium',
      });

      expect(result.success).toBe(false);
    });
  });

  describe('preview', () => {
    it('should generate preview diff', () => {
      const fileContent = 'line1\nline2\nline3\nline4\nline5';
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readFileSync.mockReturnValue(fileContent);

      const result = applier.preview({
        id: 'preview-001',
        entityId: 'entity-001',
        type: 'extract_method',
        title: 'Preview',
        description: 'Preview test',
        changes: [
          {
            filePath: 'src/file.ts',
            startLine: 2,
            endLine: 3,
            originalCode: 'line2\nline3',
            newCode: 'modified line2\nmodified line3',
            description: 'Modify',
          },
        ],
        confidence: 0.9,
        priority: 'medium',
      });

      expect(result).toBeDefined();
      expect(Array.isArray(result)).toBe(true);
    });
  });
});
