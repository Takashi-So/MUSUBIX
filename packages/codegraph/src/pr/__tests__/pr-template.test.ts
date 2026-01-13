/**
 * Tests for PRTemplateGenerator
 *
 * @see REQ-CG-PR-005 - PR body generation
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { PRTemplateGenerator } from '../pr-template.js';
import type { RefactoringSuggestion, FileDiff } from '../types.js';

describe('PRTemplateGenerator', () => {
  let generator: PRTemplateGenerator;

  beforeEach(() => {
    generator = new PRTemplateGenerator();
  });

  describe('generate', () => {
    it('should generate complete PR body', () => {
      const suggestion: RefactoringSuggestion = {
        id: 'extract-method-001',
        entityId: 'order-service',
        type: 'extract_method',
        title: 'Extract calculateTotal method',
        description: 'Extract repeated calculation logic into a reusable method',
        changes: [
          {
            filePath: 'src/order.ts',
            startLine: 10,
            endLine: 20,
            originalCode: 'old code',
            newCode: 'new code',
            description: 'Add calculateTotal method',
          },
        ],
        confidence: 0.92,
        priority: 'high',
        severity: 'medium',
        reason: 'Reduces code duplication',
      };

      const diffs: FileDiff[] = [
        {
          filePath: 'src/order.ts',
          changeType: 'modified',
          diff: '@@ -10,8 +10,15 @@\n-old code\n+new code',
          additions: 15,
          deletions: 8,
        },
      ];

      const body = generator.generate(suggestion, diffs);

      expect(body).toContain('Summary');
      expect(body).toContain('Extract repeated calculation logic');
      expect(body).toContain('src/order.ts');
      expect(body).toContain('Checklist');
    });

    it('should include confidence score', () => {
      const suggestion: RefactoringSuggestion = {
        id: 'test',
        entityId: 'test-entity',
        type: 'rename',
        title: 'Rename variable',
        description: 'Rename for clarity',
        changes: [],
        confidence: 0.87,
        priority: 'medium',
        severity: 'low',
        reason: 'Test reason',
      };

      const body = generator.generate(suggestion, []);

      expect(body).toContain('87%');
    });

    it('should include diff previews', () => {
      const suggestion: RefactoringSuggestion = {
        id: 'test',
        entityId: 'test-entity',
        type: 'extract_method',
        title: 'Test',
        description: 'Test',
        changes: [],
        confidence: 0.9,
        priority: 'medium',
        severity: 'medium',
        reason: 'Test reason',
      };

      const diffs: FileDiff[] = [
        {
          filePath: 'src/file.ts',
          changeType: 'modified',
          diff: '-old line\n+new line',
          additions: 1,
          deletions: 1,
        },
      ];

      const body = generator.generate(suggestion, diffs);

      expect(body).toContain('old line');
      expect(body).toContain('new line');
    });

    it('should include auto-generated footer', () => {
      const suggestion: RefactoringSuggestion = {
        id: 'auto-123',
        entityId: 'test-entity',
        type: 'extract_method',
        title: 'Test',
        description: 'Test',
        changes: [],
        confidence: 0.85,
        priority: 'medium',
        severity: 'medium',
        reason: 'Test reason',
      };

      const body = generator.generate(suggestion, []);

      expect(body).toContain('MUSUBIX CodeGraph');
      expect(body).toContain('auto-123');
    });
  });

  describe('generateTitle', () => {
    it('should generate PR title with type prefix', () => {
      const suggestion: RefactoringSuggestion = {
        id: 'test',
        entityId: 'test-entity',
        type: 'extract_method',
        title: 'Extract calculateTotal',
        description: 'Test',
        changes: [],
        confidence: 0.9,
        priority: 'medium',
        severity: 'medium',
        reason: 'Test reason',
      };

      const title = generator.generateTitle(suggestion);

      expect(title).toContain('Method Extraction');
      expect(title).toContain('Extract calculateTotal');
    });
  });

  describe('generateChecklist', () => {
    it('should include standard checklist items', () => {
      const suggestion: RefactoringSuggestion = {
        id: 'test',
        entityId: 'test-entity',
        type: 'extract_method',
        title: 'Test',
        description: 'Test',
        changes: [],
        confidence: 0.9,
        priority: 'medium',
        severity: 'medium',
        reason: 'Test reason',
      };

      const body = generator.generate(suggestion, []);

      expect(body).toContain('Checklist');
      expect(body).toContain('[ ]');
    });
  });

  describe('options', () => {
    it('should respect includeChecklist option', () => {
      const generator = new PRTemplateGenerator({ includeChecklist: false });
      
      const suggestion: RefactoringSuggestion = {
        id: 'test',
        entityId: 'test-entity',
        type: 'extract_method',
        title: 'Test',
        description: 'Test',
        changes: [],
        confidence: 0.9,
        priority: 'medium',
        severity: 'medium',
        reason: 'Test reason',
      };

      const body = generator.generate(suggestion, []);

      expect(body).not.toContain('Checklist');
    });

    it('should respect includeDiffs option', () => {
      const generator = new PRTemplateGenerator({ includeDiffs: false });
      
      const suggestion: RefactoringSuggestion = {
        id: 'test',
        entityId: 'test-entity',
        type: 'extract_method',
        title: 'Test',
        description: 'Test',
        changes: [],
        confidence: 0.9,
        priority: 'medium',
        severity: 'medium',
        reason: 'Test reason',
      };

      const diffs: FileDiff[] = [
        {
          filePath: 'src/file.ts',
          changeType: 'modified',
          diff: 'diff content',
          additions: 5,
          deletions: 2,
        },
      ];

      const body = generator.generate(suggestion, diffs);

      expect(body).not.toContain('diff content');
    });
  });
});
