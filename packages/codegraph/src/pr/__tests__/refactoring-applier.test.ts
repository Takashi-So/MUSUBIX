/**
 * Tests for RefactoringApplier
 *
 * @see REQ-CG-PR-004 - Code change application
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { RefactoringApplier } from '../refactoring-applier.js';
import * as fs from 'node:fs';
import * as path from 'node:path';
import type { RefactoringSuggestion, CodeChange } from '../types.js';

// Mock fs module
vi.mock('node:fs', () => ({
  existsSync: vi.fn(),
  readFileSync: vi.fn(),
  writeFileSync: vi.fn(),
  mkdirSync: vi.fn(),
  unlinkSync: vi.fn(),
  cpSync: vi.fn(),
  rmSync: vi.fn(),
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
  };

  beforeEach(() => {
    applier = new RefactoringApplier('/test/repo');
    vi.clearAllMocks();
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe('validateChanges', () => {
    it('should validate existing file for modify', () => {
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readFileSync.mockReturnValue('original content');

      const changes: CodeChange[] = [
        {
          filePath: 'src/file.ts',
          type: 'modify',
          content: 'new content',
          originalContent: 'original content',
        },
      ];

      const result = applier.validateChanges(changes);
      expect(result.valid).toBe(true);
    });

    it('should fail validation when file does not exist for modify', () => {
      mockFs.existsSync.mockReturnValue(false);

      const changes: CodeChange[] = [
        {
          filePath: 'src/nonexistent.ts',
          type: 'modify',
          content: 'new content',
        },
      ];

      const result = applier.validateChanges(changes);
      expect(result.valid).toBe(false);
      expect(result.reason).toContain('does not exist');
    });

    it('should fail validation when original content does not match', () => {
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readFileSync.mockReturnValue('different content');

      const changes: CodeChange[] = [
        {
          filePath: 'src/file.ts',
          type: 'modify',
          content: 'new content',
          originalContent: 'expected original',
        },
      ];

      const result = applier.validateChanges(changes);
      expect(result.valid).toBe(false);
      expect(result.reason).toContain('mismatch');
    });

    it('should validate non-existing file for create', () => {
      mockFs.existsSync.mockReturnValue(false);

      const changes: CodeChange[] = [
        {
          filePath: 'src/new-file.ts',
          type: 'create',
          content: 'new content',
        },
      ];

      const result = applier.validateChanges(changes);
      expect(result.valid).toBe(true);
    });

    it('should fail validation when file exists for create', () => {
      mockFs.existsSync.mockReturnValue(true);

      const changes: CodeChange[] = [
        {
          filePath: 'src/existing.ts',
          type: 'create',
          content: 'new content',
        },
      ];

      const result = applier.validateChanges(changes);
      expect(result.valid).toBe(false);
      expect(result.reason).toContain('already exists');
    });

    it('should validate existing file for delete', () => {
      mockFs.existsSync.mockReturnValue(true);

      const changes: CodeChange[] = [
        {
          filePath: 'src/to-delete.ts',
          type: 'delete',
          content: '',
        },
      ];

      const result = applier.validateChanges(changes);
      expect(result.valid).toBe(true);
    });
  });

  describe('apply', () => {
    it('should apply modify changes', async () => {
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readFileSync.mockReturnValue('original');

      const suggestion: RefactoringSuggestion = {
        id: 'test-001',
        type: 'extract-method',
        title: 'Test',
        description: 'Test refactoring',
        changes: [
          {
            filePath: 'src/file.ts',
            type: 'modify',
            content: 'modified content',
            originalContent: 'original',
          },
        ],
        confidence: 0.9,
      };

      const result = await applier.apply(suggestion);

      expect(result.success).toBe(true);
      expect(result.appliedFiles).toHaveLength(1);
      expect(mockFs.writeFileSync).toHaveBeenCalled();
    });

    it('should apply create changes', async () => {
      mockFs.existsSync.mockReturnValue(false);

      const suggestion: RefactoringSuggestion = {
        id: 'test-002',
        type: 'extract-class',
        title: 'Test',
        description: 'Test',
        changes: [
          {
            filePath: 'src/new-class.ts',
            type: 'create',
            content: 'export class NewClass {}',
          },
        ],
        confidence: 0.85,
      };

      const result = await applier.apply(suggestion);

      expect(result.success).toBe(true);
      expect(mockFs.writeFileSync).toHaveBeenCalled();
    });

    it('should apply delete changes', async () => {
      mockFs.existsSync.mockReturnValue(true);

      const suggestion: RefactoringSuggestion = {
        id: 'test-003',
        type: 'dead-code',
        title: 'Test',
        description: 'Test',
        changes: [
          {
            filePath: 'src/unused.ts',
            type: 'delete',
            content: '',
          },
        ],
        confidence: 0.95,
      };

      const result = await applier.apply(suggestion);

      expect(result.success).toBe(true);
      expect(mockFs.unlinkSync).toHaveBeenCalled();
    });

    it('should return failure when validation fails', async () => {
      mockFs.existsSync.mockReturnValue(false);

      const suggestion: RefactoringSuggestion = {
        id: 'test-004',
        type: 'modify',
        title: 'Test',
        description: 'Test',
        changes: [
          {
            filePath: 'src/nonexistent.ts',
            type: 'modify',
            content: 'new content',
          },
        ],
        confidence: 0.8,
      };

      const result = await applier.apply(suggestion);

      expect(result.success).toBe(false);
      expect(result.error).toBeDefined();
    });

    it('should create backup when enabled', async () => {
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readFileSync.mockReturnValue('original');

      const suggestion: RefactoringSuggestion = {
        id: 'test-005',
        type: 'extract-method',
        title: 'Test',
        description: 'Test',
        changes: [
          {
            filePath: 'src/file.ts',
            type: 'modify',
            content: 'modified',
            originalContent: 'original',
          },
        ],
        confidence: 0.9,
      };

      const result = await applier.apply(suggestion, { createBackup: true });

      expect(result.success).toBe(true);
      expect(result.backupPath).toBeDefined();
    });
  });

  describe('preview', () => {
    it('should generate preview diff', async () => {
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readFileSync.mockReturnValue('line 1\nline 2\nline 3');

      const suggestion: RefactoringSuggestion = {
        id: 'test-006',
        type: 'extract-method',
        title: 'Test',
        description: 'Test',
        changes: [
          {
            filePath: 'src/file.ts',
            type: 'modify',
            content: 'line 1\nmodified line 2\nline 3',
            originalContent: 'line 1\nline 2\nline 3',
          },
        ],
        confidence: 0.9,
      };

      const result = await applier.preview(suggestion);

      expect(result.diffs).toHaveLength(1);
      expect(result.diffs[0].filePath).toBe('src/file.ts');
      expect(result.diffs[0].changeType).toBe('modified');
    });

    it('should show additions and deletions count', async () => {
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readFileSync.mockReturnValue('a\nb\nc');

      const suggestion: RefactoringSuggestion = {
        id: 'test-007',
        type: 'modify',
        title: 'Test',
        description: 'Test',
        changes: [
          {
            filePath: 'src/file.ts',
            type: 'modify',
            content: 'a\nx\ny\nc',
            originalContent: 'a\nb\nc',
          },
        ],
        confidence: 0.8,
      };

      const result = await applier.preview(suggestion);

      expect(result.diffs[0].additions).toBeGreaterThan(0);
    });
  });

  describe('rollback', () => {
    it('should rollback changes from backup', async () => {
      mockFs.existsSync.mockReturnValue(true);

      const result = await applier.rollback('/test/repo/.musubix-backup');

      expect(result.success).toBe(true);
      expect(mockFs.cpSync).toHaveBeenCalled();
    });

    it('should fail rollback when backup does not exist', async () => {
      mockFs.existsSync.mockReturnValue(false);

      const result = await applier.rollback('/nonexistent/backup');

      expect(result.success).toBe(false);
      expect(result.error).toContain('not found');
    });
  });
});
