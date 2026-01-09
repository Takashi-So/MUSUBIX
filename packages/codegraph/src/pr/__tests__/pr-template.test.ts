/**
 * Tests for PRTemplateGenerator
 *
 * @see REQ-CG-PR-005 - PR body generation
 */

import { describe, it, expect } from 'vitest';
import { PRTemplateGenerator } from '../pr-template.js';
import type { RefactoringSuggestion, DiffInfo } from '../types.js';

describe('PRTemplateGenerator', () => {
  let generator: PRTemplateGenerator;

  beforeEach(() => {
    generator = new PRTemplateGenerator();
  });

  describe('generate', () => {
    it('should generate complete PR body', () => {
      const suggestion: RefactoringSuggestion = {
        id: 'extract-method-001',
        type: 'extract-method',
        title: 'Extract calculateTotal method',
        description: 'Extract repeated calculation logic into a reusable method',
        changes: [
          {
            filePath: 'src/order.ts',
            type: 'modify',
            content: 'modified content',
            description: 'Add calculateTotal method',
          },
        ],
        confidence: 0.92,
        priority: 'high',
        source: 'static-analysis',
        rationale: 'Reduces code duplication and improves testability',
      };

      const diffs: DiffInfo[] = [
        {
          filePath: 'src/order.ts',
          changeType: 'modified',
          additions: 15,
          deletions: 8,
          diff: '@@ -10,8 +10,15 @@\n-old code\n+new code',
        },
      ];

      const body = generator.generate(suggestion, diffs);

      expect(body).toContain('## Summary');
      expect(body).toContain('Extract calculateTotal method');
      expect(body).toContain('## Changes');
      expect(body).toContain('src/order.ts');
      expect(body).toContain('+15');
      expect(body).toContain('-8');
      expect(body).toContain('## Checklist');
    });

    it('should include refactoring type badge', () => {
      const suggestion: RefactoringSuggestion = {
        id: 'test',
        type: 'dead-code',
        title: 'Remove unused code',
        description: 'Remove unused imports',
        changes: [],
        confidence: 0.95,
      };

      const body = generator.generate(suggestion, []);

      expect(body).toContain('dead-code');
      expect(body).toContain('🗑️'); // Dead code emoji
    });

    it('should include confidence score', () => {
      const suggestion: RefactoringSuggestion = {
        id: 'test',
        type: 'rename',
        title: 'Rename variable',
        description: 'Rename for clarity',
        changes: [],
        confidence: 0.87,
      };

      const body = generator.generate(suggestion, []);

      expect(body).toContain('87%');
    });

    it('should include diff previews', () => {
      const suggestion: RefactoringSuggestion = {
        id: 'test',
        type: 'extract-method',
        title: 'Test',
        description: 'Test',
        changes: [],
        confidence: 0.9,
      };

      const diffs: DiffInfo[] = [
        {
          filePath: 'src/file.ts',
          changeType: 'modified',
          additions: 5,
          deletions: 3,
          diff: '```diff\n-old line\n+new line\n```',
        },
      ];

      const body = generator.generate(suggestion, diffs);

      expect(body).toContain('```diff');
      expect(body).toContain('-old line');
      expect(body).toContain('+new line');
    });

    it('should handle multiple files', () => {
      const suggestion: RefactoringSuggestion = {
        id: 'test',
        type: 'move',
        title: 'Move class',
        description: 'Move to appropriate module',
        changes: [
          { filePath: 'src/old.ts', type: 'delete', content: '' },
          { filePath: 'src/new.ts', type: 'create', content: 'class {}' },
          { filePath: 'src/imports.ts', type: 'modify', content: 'updated', originalContent: 'old' },
        ],
        confidence: 0.88,
      };

      const diffs: DiffInfo[] = [
        { filePath: 'src/old.ts', changeType: 'deleted', additions: 0, deletions: 50, diff: '' },
        { filePath: 'src/new.ts', changeType: 'added', additions: 50, deletions: 0, diff: '' },
        { filePath: 'src/imports.ts', changeType: 'modified', additions: 1, deletions: 1, diff: '' },
      ];

      const body = generator.generate(suggestion, diffs);

      expect(body).toContain('src/old.ts');
      expect(body).toContain('src/new.ts');
      expect(body).toContain('src/imports.ts');
      expect(body).toContain('🗑️'); // Deleted
      expect(body).toContain('➕'); // Added
      expect(body).toContain('📝'); // Modified
    });

    it('should include related requirements', () => {
      const suggestion: RefactoringSuggestion = {
        id: 'test',
        type: 'other',
        title: 'Test',
        description: 'Test',
        changes: [],
        confidence: 0.8,
        relatedRequirements: ['REQ-001', 'REQ-002'],
      };

      const body = generator.generate(suggestion, []);

      expect(body).toContain('REQ-001');
      expect(body).toContain('REQ-002');
    });

    it('should include rationale when provided', () => {
      const suggestion: RefactoringSuggestion = {
        id: 'test',
        type: 'simplify-expression',
        title: 'Simplify conditional',
        description: 'Simplify nested conditionals',
        changes: [],
        confidence: 0.9,
        rationale: 'Reduces cyclomatic complexity and improves readability',
      };

      const body = generator.generate(suggestion, []);

      expect(body).toContain('Rationale');
      expect(body).toContain('cyclomatic complexity');
    });

    it('should include auto-generated footer', () => {
      const suggestion: RefactoringSuggestion = {
        id: 'auto-123',
        type: 'extract-method',
        title: 'Test',
        description: 'Test',
        changes: [],
        confidence: 0.85,
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
        type: 'extract-method',
        title: 'Extract calculateTotal',
        description: 'Test',
        changes: [],
        confidence: 0.9,
      };

      const title = generator.generateTitle(suggestion);

      expect(title).toContain('refactor');
      expect(title).toContain('Extract calculateTotal');
    });

    it('should use correct prefix for different types', () => {
      const types: Array<[RefactoringSuggestion['type'], string]> = [
        ['extract-method', 'refactor'],
        ['extract-class', 'refactor'],
        ['rename', 'refactor'],
        ['dead-code', 'cleanup'],
        ['simplify-expression', 'perf'],
      ];

      for (const [type, expectedPrefix] of types) {
        const suggestion: RefactoringSuggestion = {
          id: 'test',
          type,
          title: 'Test',
          description: 'Test',
          changes: [],
          confidence: 0.8,
        };

        const title = generator.generateTitle(suggestion);
        expect(title.toLowerCase()).toContain(expectedPrefix);
      }
    });
  });

  describe('generateChecklist', () => {
    it('should include standard checklist items', () => {
      const suggestion: RefactoringSuggestion = {
        id: 'test',
        type: 'extract-method',
        title: 'Test',
        description: 'Test',
        changes: [],
        confidence: 0.9,
      };

      const body = generator.generate(suggestion, []);

      expect(body).toContain('[ ] Code review completed');
      expect(body).toContain('[ ] Tests pass');
      expect(body).toContain('[ ] No breaking changes');
    });
  });

  describe('getTypeEmoji', () => {
    it('should return appropriate emoji for each type', () => {
      const emojiMap: Record<RefactoringSuggestion['type'], string> = {
        'extract-method': '🔧',
        'extract-class': '📦',
        'extract-interface': '📐',
        'inline-variable': '➡️',
        'rename': '✏️',
        'move': '📁',
        'simplify-expression': '✨',
        'dead-code': '🗑️',
        'parameter-object': '📋',
        'other': '🔨',
      };

      for (const [type, expectedEmoji] of Object.entries(emojiMap)) {
        const suggestion: RefactoringSuggestion = {
          id: 'test',
          type: type as RefactoringSuggestion['type'],
          title: 'Test',
          description: 'Test',
          changes: [],
          confidence: 0.8,
        };

        const body = generator.generate(suggestion, []);
        expect(body).toContain(expectedEmoji);
      }
    });
  });
});
