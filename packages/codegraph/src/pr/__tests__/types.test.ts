/**
 * Tests for PR creation types and utilities
 *
 * @see REQ-CG-PR-001 - Type definitions
 */

import { describe, it, expect } from 'vitest';
import {
  generateBranchName,
  generateCommitMessage,
  type RefactoringSuggestion,
  type CodeChange,
} from '../types.js';

describe('PR Types', () => {
  describe('generateBranchName', () => {
    it('should generate branch name from suggestion', () => {
      const suggestion: RefactoringSuggestion = {
        id: 'extract-method-001',
        type: 'extract-method',
        title: 'Extract Method calculateTotal',
        description: 'Extract calculateTotal method',
        changes: [],
        confidence: 0.9,
        priority: 'high',
        source: 'static-analysis',
      };

      const branch = generateBranchName(suggestion);
      expect(branch).toMatch(/^refactor\/extract-method\/[a-z-]+-[a-z0-9]+$/);
    });

    it('should sanitize branch name characters', () => {
      const suggestion: RefactoringSuggestion = {
        id: 'test-001',
        type: 'simplify',
        title: 'Fix "special" <chars> & more!',
        description: 'Test',
        changes: [],
        confidence: 0.8,
      };

      const branch = generateBranchName(suggestion);
      // Should not contain special characters
      expect(branch).not.toMatch(/["<>&!]/);
      expect(branch).toMatch(/^refactor\//);
    });

    it('should generate valid branch for complex types', () => {
      const types: RefactoringSuggestion['type'][] = ['extract_method', 'inline', 'rename', 'move', 'simplify'];
      
      for (const type of types) {
        const suggestion: RefactoringSuggestion = {
          id: `${type}-001`,
          type: type,
          title: `Test ${type}`,
          description: 'Test',
          changes: [],
          confidence: 0.8,
        };

        const branch = generateBranchName(suggestion);
        expect(branch).toMatch(/^refactor\/[a-z-]+\/[a-z-]+-[a-z0-9]+$/);
      }
    });
  });

  describe('generateCommitMessage', () => {
    it('should generate conventional commit message', () => {
      const suggestion: RefactoringSuggestion = {
        id: 'extract-method-001',
        type: 'extract_method',
        title: 'Extract Method calculateTotal',
        description: 'Extract repeated calculation logic into method',
        changes: [
          {
            filePath: 'src/calculator.ts',
            type: 'modify',
            content: 'new content',
            originalContent: 'original',
            startLine: 10,
            endLine: 20,
            description: 'Extract method',
          },
        ],
        confidence: 0.9,
      };

      const message = generateCommitMessage(suggestion);
      
      expect(message).toContain('refactor');
      expect(message).toContain('extract method calculatetotal');
    });

    it('should use correct commit type for different refactoring types', () => {
      const typeMapping: Record<string, string> = {
        'extract_method': 'refactor',
        'extract_class': 'refactor',
        'inline': 'refactor',
        'rename': 'refactor',
        'move': 'refactor',
        'simplify': 'refactor',
        'performance': 'perf',
        'security_fix': 'security',
      };

      for (const [suggestionType, commitType] of Object.entries(typeMapping)) {
        const suggestion: RefactoringSuggestion = {
          id: 'test',
          type: suggestionType as RefactoringSuggestion['type'],
          title: 'Test',
          description: 'Test description',
          changes: [],
          confidence: 0.8,
        };

        const message = generateCommitMessage(suggestion);
        expect(message.startsWith(`${commitType}(`)).toBe(true);
      }
    });

    it('should include file list in message body', () => {
      const suggestion: RefactoringSuggestion = {
        id: 'test',
        type: 'extract_method',
        title: 'Test',
        description: 'Test description',
        changes: [
          { filePath: 'src/a.ts', type: 'modify', content: 'a', description: 'mod a' },
          { filePath: 'src/b.ts', type: 'create', content: 'b', description: 'create b' },
        ],
        confidence: 0.8,
      };

      const message = generateCommitMessage(suggestion);
      
      expect(message).toContain('Files changed:');
      expect(message).toContain('src/a.ts');
      expect(message).toContain('src/b.ts');
    });

    it('should include suggestion ID', () => {
      const suggestion: RefactoringSuggestion = {
        id: 'unique-suggestion-id-123',
        type: 'rename',
        entityId: 'core.utils',
        title: 'Rename variable',
        description: 'Rename for clarity',
        changes: [],
        confidence: 0.85,
      };

      const message = generateCommitMessage(suggestion);
      expect(message).toContain('Suggestion-ID: unique-suggestion-id-123');
    });
  });

  describe('Type Definitions', () => {
    it('should allow all valid refactoring types', () => {
      const validTypes: RefactoringSuggestion['type'][] = [
        'extract_method',
        'extract_class',
        'extract_interface',
        'inline',
        'rename',
        'move',
        'simplify',
        'performance',
        'security_fix',
      ];

      for (const type of validTypes) {
        const suggestion: RefactoringSuggestion = {
          id: 'test',
          type,
          title: 'Test',
          description: 'Test',
          changes: [],
          confidence: 0.5,
        };
        expect(suggestion.type).toBe(type);
      }
    });

    it('should allow all valid CodeChange types', () => {
      const validTypes: CodeChange['type'][] = ['create', 'modify', 'delete'];

      for (const type of validTypes) {
        const change: CodeChange = {
          filePath: 'test.ts',
          type,
          content: 'content',
        };
        expect(change.type).toBe(type);
      }
    });

    it('should allow optional properties on RefactoringSuggestion', () => {
      const minimal: RefactoringSuggestion = {
        id: 'min',
        type: 'other',
        title: 'Minimal',
        description: 'Minimal suggestion',
        changes: [],
        confidence: 0.5,
      };

      const full: RefactoringSuggestion = {
        id: 'full',
        type: 'extract-method',
        title: 'Full',
        description: 'Full suggestion',
        changes: [],
        confidence: 0.95,
        priority: 'critical',
        impact: 'high',
        source: 'ai-analysis',
        category: 'maintainability',
        relatedRequirements: ['REQ-001'],
        estimatedEffort: '1 hour',
        rationale: 'Improves code quality',
        alternatives: ['Alternative approach'],
      };

      expect(minimal.priority).toBeUndefined();
      expect(full.priority).toBe('critical');
    });
  });
});
