/**
 * Context Optimizer Implementation
 *
 * Tool call tracking, compact suggestions, mode injection, and hooks
 *
 * @see REQ-CO-001 - Strategic Compact Suggestion
 * @see REQ-CO-002 - Tool Call Counter
 * @see REQ-CO-003 - Context Mode Injection
 * @see REQ-CO-004 - PostToolUse Hooks
 * @see REQ-CO-005 - PreToolUse Hooks
 * @see REQ-CO-006 - Doc Blocker
 * @see DES-v3.7.0 Section 5 - Context Optimizer Design
 */

import * as path from 'node:path';

import type {
  ContextMode,
  ToolCallEvent,
  CompactSuggestion,
  ToolCallCounterState,
  ContextModeConfig,
  PostToolUseCheck,
  PreToolUseWarning,
  DocBlockerResult,
  ContextOptimizerConfig,
} from './types.js';
import {
  DEFAULT_CONTEXT_OPTIMIZER_CONFIG,
  CONTEXT_MODES,
  POST_TOOL_USE_CHECKS,
  PRE_TOOL_USE_WARNINGS,
  ALLOWED_DOC_PATTERNS,
  BLOCKED_DOC_PATTERNS,
} from './types.js';

/**
 * Context optimizer interface
 */
export interface ContextOptimizer {
  /**
   * Record a tool call
   */
  recordToolCall(event: Omit<ToolCallEvent, 'timestamp'>): void;

  /**
   * Get current tool call count
   */
  getToolCallCount(): number;

  /**
   * Check if compact suggestion should be shown
   */
  shouldSuggestCompact(): boolean;

  /**
   * Get compact suggestion
   */
  getCompactSuggestion(currentPhase?: string): CompactSuggestion | null;

  /**
   * Mark reminder as shown
   */
  markReminderShown(): void;

  /**
   * Get current context mode
   */
  getCurrentMode(): ContextMode;

  /**
   * Set context mode
   */
  setMode(mode: ContextMode): ContextModeConfig;

  /**
   * Get mode config
   */
  getModeConfig(mode?: ContextMode): ContextModeConfig;

  /**
   * Get post tool use checks for a file
   */
  getPostToolUseChecks(filePath: string): PostToolUseCheck[];

  /**
   * Check command for pre-tool use warnings
   */
  checkPreToolUseWarnings(command: string): PreToolUseWarning[];

  /**
   * Check if document creation should be blocked
   */
  checkDocBlocker(filePath: string): DocBlockerResult;

  /**
   * Get tool call history
   */
  getHistory(): ToolCallEvent[];

  /**
   * Reset state
   */
  reset(): void;
}

/**
 * Create context optimizer
 *
 * @param config - Optimizer configuration
 * @returns ContextOptimizer instance
 */
export function createContextOptimizer(
  config: Partial<ContextOptimizerConfig> = {}
): ContextOptimizer {
  const fullConfig: ContextOptimizerConfig = {
    ...DEFAULT_CONTEXT_OPTIMIZER_CONFIG,
    ...config,
  };

  let state: ToolCallCounterState = {
    count: 0,
    lastReminderAt: 0,
    history: [],
  };

  let currentMode: ContextMode = fullConfig.defaultMode;

  return {
    recordToolCall(event: Omit<ToolCallEvent, 'timestamp'>): void {
      const fullEvent: ToolCallEvent = {
        ...event,
        timestamp: new Date(),
      };

      state = {
        ...state,
        count: state.count + 1,
        history: [...state.history, fullEvent],
      };
    },

    getToolCallCount(): number {
      return state.count;
    },

    shouldSuggestCompact(): boolean {
      const { compactThreshold, reminderInterval } = fullConfig;

      // First threshold
      if (state.count >= compactThreshold && state.lastReminderAt < compactThreshold) {
        return true;
      }

      // Subsequent reminders
      const nextReminderAt =
        state.lastReminderAt + reminderInterval;
      if (state.count >= nextReminderAt && state.count > compactThreshold) {
        return true;
      }

      return false;
    },

    getCompactSuggestion(currentPhase?: string): CompactSuggestion | null {
      if (!this.shouldSuggestCompact()) {
        return null;
      }

      const { compactThreshold } = fullConfig;
      const isFirstSuggestion = state.lastReminderAt < compactThreshold;

      const trigger = isFirstSuggestion ? 'threshold-reached' : 'threshold-reached';
      const severity =
        state.count >= compactThreshold * 2 ? '強い警告' : 
        state.count >= compactThreshold * 1.5 ? 'リマインダー' : 
        '提案';

      const message = `💡 **コンテキスト圧縮の${severity}**

ツール呼び出しが**${state.count}回**に達しました。
${currentPhase ? `現在のフェーズ: ${currentPhase}` : ''}

コンテキストを圧縮する良いタイミングです。`;

      return {
        trigger,
        toolCallCount: state.count,
        currentPhase,
        message,
        checklist: [
          '現在のタスクの状態を保存しましたか？',
          '次のステップは明確ですか？',
          '重要なコンテキストをNotes for Next Sessionに記録しましたか？',
        ],
      };
    },

    markReminderShown(): void {
      state = {
        ...state,
        lastReminderAt: state.count,
      };
    },

    getCurrentMode(): ContextMode {
      return currentMode;
    },

    setMode(mode: ContextMode): ContextModeConfig {
      currentMode = mode;
      return CONTEXT_MODES[mode];
    },

    getModeConfig(mode?: ContextMode): ContextModeConfig {
      return CONTEXT_MODES[mode ?? currentMode];
    },

    getPostToolUseChecks(filePath: string): PostToolUseCheck[] {
      if (!fullConfig.enablePostToolUseHooks) {
        return [];
      }

      const ext = path.extname(filePath);
      const basename = path.basename(filePath);

      const checks = POST_TOOL_USE_CHECKS.filter((check) => {
        // Check if file matches the extension
        if (check.fileExtension.startsWith('.')) {
          // Simple extension match
          if (check.fileExtension === ext) return true;
          // Pattern match for .test.ts
          if (check.fileExtension === '.test.ts' && basename.endsWith('.test.ts')) return true;
        }
        return false;
      });

      return checks;
    },

    checkPreToolUseWarnings(command: string): PreToolUseWarning[] {
      if (!fullConfig.enablePreToolUseHooks) {
        return [];
      }

      const warnings = PRE_TOOL_USE_WARNINGS.filter((warning) =>
        warning.commandPattern.test(command)
      );

      // Sort by severity: destructive > dangerous > long-running
      return warnings.sort((a, b) => {
        const order = { destructive: 0, dangerous: 1, 'long-running': 2 };
        return order[a.warningType] - order[b.warningType];
      });
    },

    checkDocBlocker(filePath: string): DocBlockerResult {
      if (!fullConfig.enableDocBlocker) {
        return { shouldBlock: false, isAllowed: true };
      }

      const normalizedPath = filePath.replace(/\\/g, '/');

      // Check if explicitly allowed
      for (const pattern of ALLOWED_DOC_PATTERNS) {
        if (pattern.test(normalizedPath)) {
          return { shouldBlock: false, isAllowed: true };
        }
      }

      // Check if should be blocked
      for (const pattern of BLOCKED_DOC_PATTERNS) {
        if (pattern.test(normalizedPath)) {
          return {
            shouldBlock: true,
            isAllowed: false,
            reason: `ファイル「${path.basename(filePath)}」はドキュメントファイルです`,
            confirmationMessage: `📄 **ドキュメント作成の確認**

\`${path.basename(filePath)}\` を作成しようとしています。

このドキュメントは以下のいずれかに該当しますか？
- [ ] プロジェクトの公式ドキュメント
- [ ] 要件定義・設計・タスク分解
- [ ] 永続的に必要な情報

一時的なメモの場合は、session-managerの「Notes for Next Session」を使用してください。

作成を続行しますか？`,
          };
        }
      }

      return { shouldBlock: false, isAllowed: true };
    },

    getHistory(): ToolCallEvent[] {
      return [...state.history];
    },

    reset(): void {
      state = {
        count: 0,
        lastReminderAt: 0,
        history: [],
      };
      currentMode = fullConfig.defaultMode;
    },
  };
}

/**
 * Format compact suggestion for display
 *
 * @param suggestion - Compact suggestion
 * @returns Formatted message
 */
export function formatCompactSuggestion(suggestion: CompactSuggestion): string {
  const lines: string[] = [
    suggestion.message,
    '',
    '以下を確認してください：',
    '',
  ];

  for (const item of suggestion.checklist) {
    lines.push(`- [ ] ${item}`);
  }

  lines.push('');
  lines.push('圧縮を実行する場合は、session-managerスキルで事前に状態を保存してください。');

  return lines.join('\n');
}

/**
 * Format post tool use checks for display
 *
 * @param checks - Post tool use checks
 * @param filePath - File path
 * @returns Formatted message
 */
export function formatPostToolUseChecks(checks: PostToolUseCheck[], filePath: string): string {
  if (checks.length === 0) return '';

  const lines: string[] = [
    '📝 **編集後チェック提案**',
    '',
    `\`${path.basename(filePath)}\` を編集しました。以下のチェックを推奨します：`,
    '',
  ];

  for (const check of checks) {
    lines.push(`- [ ] ${check.description}: \`${check.command} ${filePath}\``);
  }

  lines.push('');
  lines.push('実行しますか？');

  return lines.join('\n');
}

/**
 * Format pre tool use warning for display
 *
 * @param warning - Pre tool use warning
 * @param command - Original command
 * @returns Formatted message
 */
export function formatPreToolUseWarning(warning: PreToolUseWarning, command: string): string {
  const icon =
    warning.warningType === 'destructive' ? '🚨' :
    warning.warningType === 'dangerous' ? '⚠️' : '⏱️';

  const title =
    warning.warningType === 'destructive' ? '危険な操作の検出' :
    warning.warningType === 'dangerous' ? '注意が必要な操作' : '長時間コマンドの検出';

  const lines: string[] = [
    `${icon} **${title}**`,
    '',
    `\`${command}\``,
    '',
    warning.message,
    '',
  ];

  if (warning.suggestions.length > 0) {
    lines.push('推奨：');
    for (const suggestion of warning.suggestions) {
      lines.push(`- ${suggestion}`);
    }
    lines.push('');
  }

  if (warning.requireConfirmation) {
    lines.push('**本当に実行しますか？**');
  } else {
    lines.push('続行しますか？');
  }

  return lines.join('\n');
}

/**
 * Format mode config for display
 *
 * @param config - Mode config
 * @returns Formatted message
 */
export function formatModeConfig(config: ContextModeConfig): string {
  const lines: string[] = [
    `**モード: ${config.mode}（${config.focus}）**`,
    '',
  ];

  for (const guideline of config.guidelines) {
    lines.push(`- ${guideline}`);
  }

  lines.push('');
  lines.push(`推奨ツール: ${config.recommendedTools.join(', ')}`);

  return lines.join('\n');
}
