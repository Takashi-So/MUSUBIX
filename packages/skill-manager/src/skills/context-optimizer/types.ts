/**
 * Context Optimizer Types
 *
 * Type definitions for context optimization skill
 *
 * @see REQ-CO-001 - Strategic Compact Suggestion
 * @see REQ-CO-002 - Tool Call Counter
 * @see REQ-CO-003 - Context Mode Injection
 * @see REQ-CO-004 - PostToolUse Hooks
 * @see REQ-CO-005 - PreToolUse Hooks
 * @see REQ-CO-006 - Doc Blocker
 * @see DES-v3.7.0 Section 5 - Context Optimizer Design
 */

/**
 * Context mode for session focus
 *
 * @see REQ-CO-003 - Context Mode Injection
 */
export type ContextMode = 'dev' | 'review' | 'research';

/**
 * Tool call event
 */
export interface ToolCallEvent {
  readonly toolName: string;
  readonly timestamp: Date;
  readonly parameters?: Record<string, unknown>;
  readonly filePath?: string;
}

/**
 * Compact suggestion trigger
 */
export type CompactSuggestionTrigger =
  | 'threshold-reached' // ツール呼び出し閾値到達
  | 'phase-complete' // フェーズ完了
  | 'debug-complete' // デバッグ完了
  | 'milestone-reached'; // マイルストーン達成

/**
 * Compact suggestion
 *
 * @see REQ-CO-001 - Strategic Compact Suggestion
 */
export interface CompactSuggestion {
  readonly trigger: CompactSuggestionTrigger;
  readonly toolCallCount: number;
  readonly currentPhase?: string;
  readonly message: string;
  readonly checklist: string[];
}

/**
 * Tool call counter state
 *
 * @see REQ-CO-002 - Tool Call Counter
 */
export interface ToolCallCounterState {
  readonly count: number;
  readonly lastReminderAt: number;
  readonly history: ToolCallEvent[];
}

/**
 * Context mode config
 */
export interface ContextModeConfig {
  readonly mode: ContextMode;
  readonly focus: string;
  readonly recommendedTools: string[];
  readonly guidelines: string[];
}

/**
 * Post tool use check
 *
 * @see REQ-CO-004 - PostToolUse Hooks
 */
export interface PostToolUseCheck {
  readonly fileExtension: string;
  readonly checkType: 'type-check' | 'format' | 'console-log' | 'test';
  readonly command: string;
  readonly description: string;
}

/**
 * Pre tool use warning
 *
 * @see REQ-CO-005 - PreToolUse Hooks
 */
export interface PreToolUseWarning {
  readonly commandPattern: RegExp;
  readonly warningType: 'long-running' | 'dangerous' | 'destructive';
  readonly message: string;
  readonly suggestions: string[];
  readonly requireConfirmation: boolean;
}

/**
 * Doc blocker check result
 *
 * @see REQ-CO-006 - Doc Blocker
 */
export interface DocBlockerResult {
  readonly shouldBlock: boolean;
  readonly reason?: string;
  readonly isAllowed: boolean;
  readonly confirmationMessage?: string;
}

/**
 * Context optimizer configuration
 */
export interface ContextOptimizerConfig {
  readonly compactThreshold: number;
  readonly reminderInterval: number;
  readonly defaultMode: ContextMode;
  readonly enableDocBlocker: boolean;
  readonly enablePostToolUseHooks: boolean;
  readonly enablePreToolUseHooks: boolean;
}

/**
 * Default context optimizer configuration
 */
export const DEFAULT_CONTEXT_OPTIMIZER_CONFIG: ContextOptimizerConfig = {
  compactThreshold: 50,
  reminderInterval: 25,
  defaultMode: 'dev',
  enableDocBlocker: true,
  enablePostToolUseHooks: true,
  enablePreToolUseHooks: true,
};

/**
 * Context mode definitions
 */
export const CONTEXT_MODES: Record<ContextMode, ContextModeConfig> = {
  dev: {
    mode: 'dev',
    focus: '実装・コーディング',
    recommendedTools: ['Edit', 'Write', 'Bash', 'run_in_terminal'],
    guidelines: [
      'コード品質を重視',
      'テスト駆動開発（Red-Green-Blue）',
      '型安全性の確保',
      'エラーハンドリングの実装',
    ],
  },
  review: {
    mode: 'review',
    focus: 'コードレビュー',
    recommendedTools: ['Read', 'Grep', 'Glob', 'read_file', 'grep_search'],
    guidelines: [
      'コードの読みやすさを確認',
      '潜在的なバグを検出',
      'セキュリティ問題を確認',
      'パフォーマンス問題を確認',
      'ベストプラクティスへの準拠',
    ],
  },
  research: {
    mode: 'research',
    focus: '調査・探索',
    recommendedTools: ['Read', 'Grep', 'semantic_search', 'fetch_webpage'],
    guidelines: [
      '幅広い情報収集',
      '関連コードの探索',
      'ドキュメントの確認',
      '類似実装の調査',
    ],
  },
};

/**
 * Post tool use checks definition
 */
export const POST_TOOL_USE_CHECKS: PostToolUseCheck[] = [
  {
    fileExtension: '.ts',
    checkType: 'type-check',
    command: 'npx tsc --noEmit',
    description: '型チェック',
  },
  {
    fileExtension: '.tsx',
    checkType: 'type-check',
    command: 'npx tsc --noEmit',
    description: '型チェック',
  },
  {
    fileExtension: '.ts',
    checkType: 'format',
    command: 'npx prettier --check',
    description: 'フォーマット確認',
  },
  {
    fileExtension: '.tsx',
    checkType: 'format',
    command: 'npx prettier --check',
    description: 'フォーマット確認',
  },
  {
    fileExtension: '.js',
    checkType: 'format',
    command: 'npx prettier --check',
    description: 'フォーマット確認',
  },
  {
    fileExtension: '.ts',
    checkType: 'console-log',
    command: 'grep -n "console\\.log"',
    description: 'console.log検出',
  },
  {
    fileExtension: '.tsx',
    checkType: 'console-log',
    command: 'grep -n "console\\.log"',
    description: 'console.log検出',
  },
  {
    fileExtension: '.test.ts',
    checkType: 'test',
    command: 'npx vitest run',
    description: 'テスト実行',
  },
];

/**
 * Pre tool use warnings definition
 */
export const PRE_TOOL_USE_WARNINGS: PreToolUseWarning[] = [
  {
    commandPattern: /^(npm|pnpm|yarn)\s+install/i,
    warningType: 'long-running',
    message: 'パッケージインストールは時間がかかる可能性があります',
    suggestions: ['tmux内で実行', 'バックグラウンドで実行'],
    requireConfirmation: false,
  },
  {
    commandPattern: /^(npm|pnpm)\s+run\s+build/i,
    warningType: 'long-running',
    message: 'ビルドは時間がかかる可能性があります',
    suggestions: ['tmux内で実行', 'バックグラウンドで実行'],
    requireConfirmation: false,
  },
  {
    commandPattern: /^cargo\s+build/i,
    warningType: 'long-running',
    message: 'Cargoビルドは時間がかかる可能性があります',
    suggestions: ['tmux内で実行'],
    requireConfirmation: false,
  },
  {
    commandPattern: /^docker\s+build/i,
    warningType: 'long-running',
    message: 'Dockerビルドは時間がかかる可能性があります',
    suggestions: ['バックグラウンドで実行'],
    requireConfirmation: false,
  },
  {
    commandPattern: /^git\s+push\s+--force/i,
    warningType: 'destructive',
    message: 'Force pushはリモートの履歴を破壊します',
    suggestions: ['git push --force-with-lease を使用', '変更内容を再確認'],
    requireConfirmation: true,
  },
  {
    commandPattern: /^git\s+push/i,
    warningType: 'dangerous',
    message: 'リモートに変更をプッシュします',
    suggestions: ['git diff でプッシュ内容を確認', 'git status で状態を確認'],
    requireConfirmation: false,
  },
  {
    commandPattern: /^rm\s+-rf/i,
    warningType: 'destructive',
    message: '再帰的な強制削除は復元できません',
    suggestions: ['削除対象を再確認', 'バックアップを作成'],
    requireConfirmation: true,
  },
  {
    commandPattern: /^git\s+reset\s+--hard/i,
    warningType: 'destructive',
    message: '未コミットの変更がすべて失われます',
    suggestions: ['git stash で変更を保存', 'git status で状態を確認'],
    requireConfirmation: true,
  },
  {
    commandPattern: /DROP\s+TABLE/i,
    warningType: 'destructive',
    message: 'テーブルが完全に削除されます',
    suggestions: ['バックアップを作成', 'テーブル名を再確認'],
    requireConfirmation: true,
  },
  {
    commandPattern: /DELETE\s+FROM.*WHERE/i,
    warningType: 'dangerous',
    message: 'データが削除されます',
    suggestions: ['WHERE句を確認', 'SELECT文で対象を確認'],
    requireConfirmation: true,
  },
];

/**
 * Allowed doc patterns (not blocked)
 */
export const ALLOWED_DOC_PATTERNS: RegExp[] = [
  /^README\.md$/i,
  /^CHANGELOG\.md$/i,
  /^LICENSE$/i,
  /^docs\//i,
  /^\.github\//i,
  /^storage\/specs\//i,
  /^storage\/design\//i,
  /^storage\/tasks\//i,
  /^storage\/reviews\//i,
  /\.test\./i,
  /\.spec\./i,
];

/**
 * Blocked doc patterns
 */
export const BLOCKED_DOC_PATTERNS: RegExp[] = [
  /\.md$/i,
  /\.txt$/i,
  /^notes\./i,
  /^temp\./i,
  /^scratch\./i,
  /^draft\./i,
];
