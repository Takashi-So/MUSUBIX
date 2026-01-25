/**
 * Context Optimizer Tests
 *
 * @see REQ-CO-001 - Strategic Compact Suggestion
 * @see REQ-CO-002 - Tool Call Counter
 * @see REQ-CO-003 - Context Mode Injection
 * @see REQ-CO-004 - PostToolUse Hooks
 * @see REQ-CO-005 - PreToolUse Hooks
 * @see REQ-CO-006 - Doc Blocker
 */

import { describe, it, expect, beforeEach } from 'vitest';

import {
  createContextOptimizer,
  formatCompactSuggestion,
  formatPostToolUseChecks,
  formatPreToolUseWarning,
  formatModeConfig,
  type ContextOptimizer,
  CONTEXT_MODES,
} from '../../src/skills/context-optimizer/index.js';

describe('ContextOptimizer', () => {
  let optimizer: ContextOptimizer;

  beforeEach(() => {
    optimizer = createContextOptimizer();
  });

  describe('Tool Call Counter (REQ-CO-002)', () => {
    it('should start with zero count', () => {
      expect(optimizer.getToolCallCount()).toBe(0);
    });

    it('should increment count on tool call', () => {
      optimizer.recordToolCall({ toolName: 'read_file' });
      expect(optimizer.getToolCallCount()).toBe(1);

      optimizer.recordToolCall({ toolName: 'write_file' });
      expect(optimizer.getToolCallCount()).toBe(2);
    });

    it('should record tool call history', () => {
      optimizer.recordToolCall({ toolName: 'read_file', filePath: '/test.ts' });
      optimizer.recordToolCall({ toolName: 'write_file', filePath: '/test.ts' });

      const history = optimizer.getHistory();
      expect(history).toHaveLength(2);
      expect(history[0].toolName).toBe('read_file');
      expect(history[1].toolName).toBe('write_file');
    });
  });

  describe('Strategic Compact Suggestion (REQ-CO-001)', () => {
    it('should not suggest compact before threshold', () => {
      for (let i = 0; i < 49; i++) {
        optimizer.recordToolCall({ toolName: 'test' });
      }

      expect(optimizer.shouldSuggestCompact()).toBe(false);
      expect(optimizer.getCompactSuggestion()).toBeNull();
    });

    it('should suggest compact at threshold', () => {
      for (let i = 0; i < 50; i++) {
        optimizer.recordToolCall({ toolName: 'test' });
      }

      expect(optimizer.shouldSuggestCompact()).toBe(true);

      const suggestion = optimizer.getCompactSuggestion('Phase 4');
      expect(suggestion).not.toBeNull();
      expect(suggestion!.toolCallCount).toBe(50);
      expect(suggestion!.currentPhase).toBe('Phase 4');
      expect(suggestion!.checklist).toHaveLength(3);
    });

    it('should not repeat suggestion until next interval', () => {
      for (let i = 0; i < 50; i++) {
        optimizer.recordToolCall({ toolName: 'test' });
      }

      expect(optimizer.shouldSuggestCompact()).toBe(true);
      optimizer.markReminderShown();
      expect(optimizer.shouldSuggestCompact()).toBe(false);

      // Add more calls
      for (let i = 0; i < 20; i++) {
        optimizer.recordToolCall({ toolName: 'test' });
      }
      expect(optimizer.shouldSuggestCompact()).toBe(false);

      // Reach next interval (25 more)
      for (let i = 0; i < 5; i++) {
        optimizer.recordToolCall({ toolName: 'test' });
      }
      expect(optimizer.shouldSuggestCompact()).toBe(true);
    });

    it('should respect custom threshold', () => {
      const customOptimizer = createContextOptimizer({ compactThreshold: 10 });

      for (let i = 0; i < 10; i++) {
        customOptimizer.recordToolCall({ toolName: 'test' });
      }

      expect(customOptimizer.shouldSuggestCompact()).toBe(true);
    });
  });

  describe('Context Mode Injection (REQ-CO-003)', () => {
    it('should default to dev mode', () => {
      expect(optimizer.getCurrentMode()).toBe('dev');
    });

    it('should switch modes', () => {
      optimizer.setMode('review');
      expect(optimizer.getCurrentMode()).toBe('review');

      optimizer.setMode('research');
      expect(optimizer.getCurrentMode()).toBe('research');
    });

    it('should return correct mode config', () => {
      const devConfig = optimizer.getModeConfig('dev');
      expect(devConfig.focus).toBe('実装・コーディング');
      expect(devConfig.recommendedTools).toContain('Edit');

      const reviewConfig = optimizer.getModeConfig('review');
      expect(reviewConfig.focus).toBe('コードレビュー');
      expect(reviewConfig.recommendedTools).toContain('Read');

      const researchConfig = optimizer.getModeConfig('research');
      expect(researchConfig.focus).toBe('調査・探索');
      expect(researchConfig.recommendedTools).toContain('semantic_search');
    });

    it('should return current mode config when no mode specified', () => {
      optimizer.setMode('review');
      const config = optimizer.getModeConfig();
      expect(config.mode).toBe('review');
    });
  });

  describe('PostToolUse Hooks (REQ-CO-004)', () => {
    it('should return checks for TypeScript files', () => {
      const checks = optimizer.getPostToolUseChecks('/path/to/file.ts');

      expect(checks.length).toBeGreaterThan(0);
      expect(checks.some((c) => c.checkType === 'type-check')).toBe(true);
      expect(checks.some((c) => c.checkType === 'format')).toBe(true);
      expect(checks.some((c) => c.checkType === 'console-log')).toBe(true);
    });

    it('should return checks for TSX files', () => {
      const checks = optimizer.getPostToolUseChecks('/path/to/component.tsx');

      expect(checks.length).toBeGreaterThan(0);
      expect(checks.some((c) => c.checkType === 'type-check')).toBe(true);
    });

    it('should return test check for test files', () => {
      const checks = optimizer.getPostToolUseChecks('/path/to/file.test.ts');

      expect(checks.some((c) => c.checkType === 'test')).toBe(true);
    });

    it('should return empty for non-code files', () => {
      const checks = optimizer.getPostToolUseChecks('/path/to/data.json');
      expect(checks).toHaveLength(0);
    });

    it('should be disabled when config is false', () => {
      const disabled = createContextOptimizer({ enablePostToolUseHooks: false });
      const checks = disabled.getPostToolUseChecks('/path/to/file.ts');
      expect(checks).toHaveLength(0);
    });
  });

  describe('PreToolUse Hooks (REQ-CO-005)', () => {
    it('should warn for npm install', () => {
      const warnings = optimizer.checkPreToolUseWarnings('npm install lodash');

      expect(warnings.length).toBeGreaterThan(0);
      expect(warnings[0].warningType).toBe('long-running');
    });

    it('should warn for pnpm build', () => {
      const warnings = optimizer.checkPreToolUseWarnings('pnpm run build');

      expect(warnings.length).toBeGreaterThan(0);
      expect(warnings[0].warningType).toBe('long-running');
    });

    it('should warn for git push', () => {
      const warnings = optimizer.checkPreToolUseWarnings('git push origin main');

      expect(warnings.length).toBeGreaterThan(0);
      expect(warnings[0].warningType).toBe('dangerous');
    });

    it('should strongly warn for git push --force', () => {
      const warnings = optimizer.checkPreToolUseWarnings('git push --force origin main');

      expect(warnings.length).toBeGreaterThan(0);
      expect(warnings[0].warningType).toBe('destructive');
      expect(warnings[0].requireConfirmation).toBe(true);
    });

    it('should warn for rm -rf', () => {
      const warnings = optimizer.checkPreToolUseWarnings('rm -rf /tmp/test');

      expect(warnings.length).toBeGreaterThan(0);
      expect(warnings[0].warningType).toBe('destructive');
      expect(warnings[0].requireConfirmation).toBe(true);
    });

    it('should warn for git reset --hard', () => {
      const warnings = optimizer.checkPreToolUseWarnings('git reset --hard HEAD~1');

      expect(warnings.length).toBeGreaterThan(0);
      expect(warnings[0].warningType).toBe('destructive');
    });

    it('should return empty for safe commands', () => {
      const warnings = optimizer.checkPreToolUseWarnings('ls -la');
      expect(warnings).toHaveLength(0);
    });

    it('should be disabled when config is false', () => {
      const disabled = createContextOptimizer({ enablePreToolUseHooks: false });
      const warnings = disabled.checkPreToolUseWarnings('rm -rf /');
      expect(warnings).toHaveLength(0);
    });

    it('should sort warnings by severity', () => {
      const warnings = optimizer.checkPreToolUseWarnings('git push --force');

      // Should have both destructive (force) and dangerous (push)
      if (warnings.length > 1) {
        expect(warnings[0].warningType).toBe('destructive');
      }
    });
  });

  describe('Doc Blocker (REQ-CO-006)', () => {
    it('should allow README.md', () => {
      const result = optimizer.checkDocBlocker('README.md');
      expect(result.shouldBlock).toBe(false);
      expect(result.isAllowed).toBe(true);
    });

    it('should allow CHANGELOG.md', () => {
      const result = optimizer.checkDocBlocker('CHANGELOG.md');
      expect(result.shouldBlock).toBe(false);
    });

    it('should allow files in docs/', () => {
      const result = optimizer.checkDocBlocker('docs/guide.md');
      expect(result.shouldBlock).toBe(false);
    });

    it('should allow files in .github/', () => {
      const result = optimizer.checkDocBlocker('.github/CONTRIBUTING.md');
      expect(result.shouldBlock).toBe(false);
    });

    it('should allow files in storage/specs/', () => {
      const result = optimizer.checkDocBlocker('storage/specs/REQ-001.md');
      expect(result.shouldBlock).toBe(false);
    });

    it('should allow test files', () => {
      const result = optimizer.checkDocBlocker('test.spec.ts');
      expect(result.shouldBlock).toBe(false);
    });

    it('should block random .md files', () => {
      const result = optimizer.checkDocBlocker('random-notes.md');
      expect(result.shouldBlock).toBe(true);
      expect(result.confirmationMessage).toBeDefined();
    });

    it('should block .txt files', () => {
      const result = optimizer.checkDocBlocker('notes.txt');
      expect(result.shouldBlock).toBe(true);
    });

    it('should block temp files', () => {
      const result = optimizer.checkDocBlocker('temp.md');
      expect(result.shouldBlock).toBe(true);
    });

    it('should block draft files', () => {
      const result = optimizer.checkDocBlocker('draft.md');
      expect(result.shouldBlock).toBe(true);
    });

    it('should be disabled when config is false', () => {
      const disabled = createContextOptimizer({ enableDocBlocker: false });
      const result = disabled.checkDocBlocker('random.md');
      expect(result.shouldBlock).toBe(false);
    });
  });

  describe('reset', () => {
    it('should reset all state', () => {
      // Build up some state
      for (let i = 0; i < 60; i++) {
        optimizer.recordToolCall({ toolName: 'test' });
      }
      optimizer.setMode('review');

      // Reset
      optimizer.reset();

      expect(optimizer.getToolCallCount()).toBe(0);
      expect(optimizer.getHistory()).toHaveLength(0);
      expect(optimizer.getCurrentMode()).toBe('dev');
      expect(optimizer.shouldSuggestCompact()).toBe(false);
    });
  });
});

describe('Format Functions', () => {
  describe('formatCompactSuggestion', () => {
    it('should format suggestion correctly', () => {
      const suggestion = {
        trigger: 'threshold-reached' as const,
        toolCallCount: 50,
        currentPhase: 'Phase 4',
        message: 'Test message',
        checklist: ['Item 1', 'Item 2'],
      };

      const formatted = formatCompactSuggestion(suggestion);

      expect(formatted).toContain('Test message');
      expect(formatted).toContain('Item 1');
      expect(formatted).toContain('Item 2');
      expect(formatted).toContain('session-manager');
    });
  });

  describe('formatPostToolUseChecks', () => {
    it('should format checks correctly', () => {
      const checks = [
        {
          fileExtension: '.ts',
          checkType: 'type-check' as const,
          command: 'npx tsc --noEmit',
          description: '型チェック',
        },
      ];

      const formatted = formatPostToolUseChecks(checks, '/path/to/file.ts');

      expect(formatted).toContain('編集後チェック提案');
      expect(formatted).toContain('file.ts');
      expect(formatted).toContain('型チェック');
    });

    it('should return empty for no checks', () => {
      const formatted = formatPostToolUseChecks([], '/path/to/file.ts');
      expect(formatted).toBe('');
    });
  });

  describe('formatPreToolUseWarning', () => {
    it('should format destructive warning correctly', () => {
      const warning = {
        commandPattern: /rm -rf/,
        warningType: 'destructive' as const,
        message: 'Dangerous operation',
        suggestions: ['Be careful'],
        requireConfirmation: true,
      };

      const formatted = formatPreToolUseWarning(warning, 'rm -rf /tmp');

      expect(formatted).toContain('🚨');
      expect(formatted).toContain('危険な操作');
      expect(formatted).toContain('rm -rf /tmp');
      expect(formatted).toContain('本当に実行しますか？');
    });

    it('should format long-running warning correctly', () => {
      const warning = {
        commandPattern: /npm install/,
        warningType: 'long-running' as const,
        message: 'Long running',
        suggestions: [],
        requireConfirmation: false,
      };

      const formatted = formatPreToolUseWarning(warning, 'npm install');

      expect(formatted).toContain('⏱️');
      expect(formatted).toContain('長時間コマンド');
      expect(formatted).toContain('続行しますか？');
    });
  });

  describe('formatModeConfig', () => {
    it('should format mode config correctly', () => {
      const config = CONTEXT_MODES.dev;
      const formatted = formatModeConfig(config);

      expect(formatted).toContain('dev');
      expect(formatted).toContain('実装・コーディング');
      expect(formatted).toContain('推奨ツール');
    });
  });
});
