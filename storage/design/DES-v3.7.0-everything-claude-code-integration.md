# MUSUBIX v3.7.0 設計書
## Everything Claude Code Agent Skills 統合

**文書ID**: DES-v3.7.0-001  
**作成日**: 2026-01-25  
**ステータス**: Draft  
**対応要件**: REQ-v3.7.0-001  
**実装方式**: GitHub Copilot Agent Skills  

---

## 1. エグゼクティブサマリー

本設計書は、`REQ-v3.7.0-everything-claude-code-integration.md`で定義された42要件を実現するための詳細設計を記述する。10個のAgent Skillsを通じて、セッション管理、コンテキスト最適化、継続学習、評価フレームワーク等の機能を提供する。

### 設計概要

| スキル | 設計ID | 要件数 | 主要コンポーネント |
|--------|--------|--------|-------------------|
| session-manager | DES-SM-001〜004 | 4 | SessionStore, TodoTracker |
| context-optimizer | DES-CO-001〜006 | 6 | ToolCallCounter, HookManager |
| learning-hooks | DES-LH-001〜003 | 3 | PatternExtractor, SkillWriter |
| eval-harness | DES-EH-001〜005 | 5 | EvalRunner, MetricsCalculator |
| verification-loop | DES-VL-001〜005 | 5 | VerificationPipeline, ReportGenerator |
| checkpoint | DES-CP-001〜005 | 5 | CheckpointManager, GitIntegration |
| build-fix | DES-BF-001〜003 | 3 | ErrorAnalyzer, IterativeFixer |
| codemap | DES-CM-001〜004 | 4 | StructureAnalyzer, CodemapGenerator |
| refactor-cleaner | DES-RC-001〜004 | 4 | DeadCodeDetector, SafeDeleter |
| e2e-runner | DES-E2E-001〜003 | 3 | TestGenerator, PlaywrightRunner |

---

## 2. C4モデル設計

### 2.1 Context Diagram（システムコンテキスト）

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              External Systems                                │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌──────────────┐     ┌──────────────┐     ┌──────────────┐                │
│  │   GitHub     │     │    VS Code   │     │   File       │                │
│  │   Copilot    │     │   Extension  │     │   System     │                │
│  └──────┬───────┘     └──────┬───────┘     └──────┬───────┘                │
│         │                    │                    │                         │
│         │    Agent Skills    │                    │                         │
│         │    (SKILL.md)      │                    │                         │
│         ▼                    ▼                    ▼                         │
│  ┌─────────────────────────────────────────────────────────────────┐       │
│  │                    MUSUBIX Agent Skills                          │       │
│  │  ┌──────────────────────────────────────────────────────────┐   │       │
│  │  │  10 Skills: session-manager, context-optimizer,          │   │       │
│  │  │  learning-hooks, eval-harness, verification-loop,        │   │       │
│  │  │  checkpoint, build-fix, codemap, refactor-cleaner,       │   │       │
│  │  │  e2e-runner                                               │   │       │
│  │  └──────────────────────────────────────────────────────────┘   │       │
│  └──────────────────────────┬──────────────────────────────────────┘       │
│                             │                                               │
│                             ▼                                               │
│  ┌─────────────────────────────────────────────────────────────────┐       │
│  │                    MUSUBIX MCP Server                            │       │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐           │       │
│  │  │ pattern-mcp  │  │ workflow-    │  │ knowledge    │           │       │
│  │  │              │  │ engine       │  │ store        │           │       │
│  │  └──────────────┘  └──────────────┘  └──────────────┘           │       │
│  └─────────────────────────────────────────────────────────────────┘       │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 2.2 Container Diagram（コンテナ図）

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         MUSUBIX Agent Skills Container                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                      Project Skills Layer                            │   │
│  │                    .github/skills/<skill>/SKILL.md                   │   │
│  │  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────────┐    │   │
│  │  │  session-   │ │  context-   │ │  learning-  │ │   eval-     │    │   │
│  │  │  manager    │ │  optimizer  │ │  hooks      │ │   harness   │    │   │
│  │  └──────┬──────┘ └──────┬──────┘ └──────┬──────┘ └──────┬──────┘    │   │
│  │         │               │               │               │           │   │
│  │  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────────┐    │   │
│  │  │verification-│ │ checkpoint  │ │  build-fix  │ │  codemap    │    │   │
│  │  │   loop      │ │             │ │             │ │             │    │   │
│  │  └──────┬──────┘ └──────┬──────┘ └──────┬──────┘ └──────┬──────┘    │   │
│  │         │               │               │               │           │   │
│  │  ┌─────────────┐ ┌─────────────┐                                    │   │
│  │  │  refactor-  │ │  e2e-runner │                                    │   │
│  │  │  cleaner    │ │             │                                    │   │
│  │  └─────────────┘ └─────────────┘                                    │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                     Shared Resources Layer                           │   │
│  │  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐      │   │
│  │  │ ~/.musubix/     │  │ ~/.musubix/     │  │ ~/.musubix/     │      │   │
│  │  │ sessions/       │  │ checkpoints/    │  │ skills/learned/ │      │   │
│  │  └─────────────────┘  └─────────────────┘  └─────────────────┘      │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                      Personal Skills Layer                           │   │
│  │                   ~/.copilot/skills/musubix-common/                  │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 2.3 Component Diagram（コンポーネント図）

#### Session Manager コンポーネント

```
┌─────────────────────────────────────────────────────────────────┐
│                    session-manager Skill                         │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────┐    ┌─────────────────┐                    │
│  │  SessionStore   │◄───│  SessionHook    │                    │
│  │  ─────────────  │    │  ─────────────  │                    │
│  │  save()         │    │  onStart()      │                    │
│  │  load()         │    │  onEnd()        │                    │
│  │  list()         │    │  onPreCompact() │                    │
│  └────────┬────────┘    └─────────────────┘                    │
│           │                                                     │
│           ▼                                                     │
│  ┌─────────────────┐    ┌─────────────────┐                    │
│  │  TodoTracker    │    │  StateManager   │                    │
│  │  ─────────────  │    │  ─────────────  │                    │
│  │  addTask()      │    │  snapshot()     │                    │
│  │  complete()     │    │  restore()      │                    │
│  │  getProgress()  │    │  diff()         │                    │
│  └─────────────────┘    └─────────────────┘                    │
│                                                                 │
│  Storage: ~/.musubix/sessions/YYYY-MM-DD-HH-MM.md              │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

#### Context Optimizer コンポーネント

```
┌─────────────────────────────────────────────────────────────────┐
│                   context-optimizer Skill                        │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────┐    ┌─────────────────┐                    │
│  │ ToolCallCounter │    │   HookManager   │                    │
│  │  ─────────────  │    │  ─────────────  │                    │
│  │  increment()    │    │  preToolUse()   │                    │
│  │  getCount()     │    │  postToolUse()  │                    │
│  │  reset()        │    │  docBlocker()   │                    │
│  │  shouldCompact()│    └────────┬────────┘                    │
│  └────────┬────────┘             │                             │
│           │                      │                             │
│           ▼                      ▼                             │
│  ┌─────────────────┐    ┌─────────────────┐                    │
│  │ CompactAdvisor  │    │  ModeInjector   │                    │
│  │  ─────────────  │    │  ─────────────  │                    │
│  │  suggest()      │    │  inject()       │                    │
│  │  getPhase()     │    │  getModes()     │                    │
│  └─────────────────┘    └─────────────────┘                    │
│                                                                 │
│  Contexts: .github/skills/context-optimizer/contexts/*.md      │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 3. トレーサビリティマトリクス

### REQ → DES マッピング

| 要件ID | 設計ID | コンポーネント | 実装ファイル |
|--------|--------|---------------|-------------|
| **session-manager** | | | |
| REQ-SM-001 | DES-SM-001 | SessionHook.onStart | session-manager/SKILL.md |
| REQ-SM-002 | DES-SM-002 | SessionHook.onEnd, SessionStore | session-manager/SKILL.md |
| REQ-SM-003 | DES-SM-003 | SessionHook.onPreCompact | session-manager/SKILL.md |
| REQ-SM-004 | DES-SM-004 | TodoTracker | session-manager/SKILL.md |
| **context-optimizer** | | | |
| REQ-CO-001 | DES-CO-001 | CompactAdvisor.suggest | context-optimizer/SKILL.md |
| REQ-CO-002 | DES-CO-002 | ToolCallCounter | context-optimizer/SKILL.md |
| REQ-CO-003 | DES-CO-003 | ModeInjector | context-optimizer/SKILL.md |
| REQ-CO-004 | DES-CO-004 | HookManager.postToolUse | context-optimizer/SKILL.md |
| REQ-CO-005 | DES-CO-005 | HookManager.preToolUse | context-optimizer/SKILL.md |
| REQ-CO-006 | DES-CO-006 | HookManager.docBlocker | context-optimizer/SKILL.md |
| **learning-hooks** | | | |
| REQ-LH-001 | DES-LH-001 | PatternExtractor | learning-hooks/SKILL.md |
| REQ-LH-002 | DES-LH-002 | SkillWriter | learning-hooks/SKILL.md |
| REQ-LH-003 | DES-LH-003 | PatternFilter | learning-hooks/SKILL.md |
| **eval-harness** | | | |
| REQ-EH-001 | DES-EH-001 | CapabilityEval | eval-harness/SKILL.md |
| REQ-EH-002 | DES-EH-002 | RegressionEval | eval-harness/SKILL.md |
| REQ-EH-003 | DES-EH-003 | MetricsCalculator | eval-harness/SKILL.md |
| REQ-EH-004 | DES-EH-004 | Grader (Code/Model) | eval-harness/SKILL.md |
| REQ-EH-005 | DES-EH-005 | HumanGrader | eval-harness/SKILL.md |
| **verification-loop** | | | |
| REQ-VL-001 | DES-VL-001 | VerificationPipeline | verification-loop/SKILL.md |
| REQ-VL-002 | DES-VL-002 | ReportGenerator | verification-loop/SKILL.md |
| REQ-VL-003 | DES-VL-003 | ContinuousVerifier | verification-loop/SKILL.md |
| REQ-VL-004 | DES-VL-004 | VerificationMode | verification-loop/SKILL.md |
| REQ-VL-005 | DES-VL-005 | StopHookAuditor | verification-loop/SKILL.md |
| **checkpoint** | | | |
| REQ-CP-001 | DES-CP-001 | CheckpointManager.create | checkpoint/SKILL.md |
| REQ-CP-002 | DES-CP-002 | CheckpointManager.verify | checkpoint/SKILL.md |
| REQ-CP-003 | DES-CP-003 | CheckpointManager.list | checkpoint/SKILL.md |
| REQ-CP-004 | DES-CP-004 | CheckpointManager.restore | checkpoint/SKILL.md |
| REQ-CP-005 | DES-CP-005 | RetentionPolicy | checkpoint/SKILL.md |
| **build-fix** | | | |
| REQ-BF-001 | DES-BF-001 | ErrorAnalyzer | build-fix/SKILL.md |
| REQ-BF-002 | DES-BF-002 | IterativeFixer | build-fix/SKILL.md |
| REQ-BF-003 | DES-BF-003 | FixReporter | build-fix/SKILL.md |
| **codemap** | | | |
| REQ-CM-001 | DES-CM-001 | StructureAnalyzer | codemap/SKILL.md |
| REQ-CM-002 | DES-CM-002 | ModuleAnalyzer | codemap/SKILL.md |
| REQ-CM-003 | DES-CM-003 | CodemapGenerator | codemap/SKILL.md |
| REQ-CM-004 | DES-CM-004 | DiffAnalyzer | codemap/SKILL.md |
| **refactor-cleaner** | | | |
| REQ-RC-001 | DES-RC-001 | DeadCodeDetector | refactor-cleaner/SKILL.md |
| REQ-RC-002 | DES-RC-002 | SafeDeleter | refactor-cleaner/SKILL.md |
| REQ-RC-003 | DES-RC-003 | DeletionLogger | refactor-cleaner/SKILL.md |
| REQ-RC-004 | DES-RC-004 | RiskClassifier | refactor-cleaner/SKILL.md |
| **e2e-runner** | | | |
| REQ-E2E-001 | DES-E2E-001 | TestGenerator | e2e-runner/SKILL.md |
| REQ-E2E-002 | DES-E2E-002 | PlaywrightRunner | e2e-runner/SKILL.md |
| REQ-E2E-003 | DES-E2E-003 | E2EReporter | e2e-runner/SKILL.md |

---

## 4. 詳細設計

### 4.1 Session Manager スキル詳細設計

#### DES-SM-001: SessionStart Hook

**対応要件**: REQ-SM-001

**コンポーネント**: `SessionHook.onStart`

**処理フロー**:
```
┌─────────────────┐
│ セッション開始   │
└────────┬────────┘
         │
         ▼
┌─────────────────────────────────────┐
│ 1. ~/.musubix/sessions/ を検索      │
│    - 過去7日間のファイルを取得       │
│    - ファイル名: YYYY-MM-DD-HH-MM.md │
└────────┬────────────────────────────┘
         │
         ▼
┌─────────────────────────────────────┐
│ 2. 直近セッションを解析              │
│    - "Notes for Next Session"を抽出 │
│    - "In Progress"タスクを抽出      │
│    - "Context to Load"を抽出        │
└────────┬────────────────────────────┘
         │
         ▼
┌─────────────────────────────────────┐
│ 3. ユーザーに通知                    │
│    「前回セッションのコンテキストが   │
│     利用可能です。継続しますか？」   │
└─────────────────────────────────────┘
```

**SKILL.md指示設計**:
```markdown
## セッション開始時の手順

セッションを開始する際は、以下を実行してください：

1. **過去セッションの検索**
   ```bash
   ls -t ~/.musubix/sessions/*.md 2>/dev/null | head -5
   ```

2. **直近セッションの確認**
   最新のセッションファイルが存在する場合：
   - "Notes for Next Session" セクションを読み込む
   - 未完了タスクがあれば報告する

3. **コンテキスト復元の提案**
   ```
   📋 前回セッション (YYYY-MM-DD) のコンテキストが利用可能です：
   - 未完了タスク: X件
   - 次回向けメモ: あり
   
   継続しますか？ (yes/no)
   ```
```

**データモデル**:
```typescript
interface SessionFile {
  filename: string;          // YYYY-MM-DD-HH-MM.md
  date: Date;
  started: string;           // HH:MM
  lastUpdated: string;       // HH:MM
  completed: Task[];
  inProgress: Task[];
  notesForNextSession: string;
  contextToLoad: string[];
}

interface Task {
  id: string;
  description: string;
  completed: boolean;
}
```

---

#### DES-SM-002: SessionEnd Hook

**対応要件**: REQ-SM-002

**コンポーネント**: `SessionHook.onEnd`, `SessionStore`

**処理フロー**:
```
┌─────────────────┐
│ セッション終了   │
└────────┬────────┘
         │
         ▼
┌─────────────────────────────────────┐
│ 1. 現在状態を収集                    │
│    - 完了タスクリスト                │
│    - 進行中タスクリスト              │
│    - 編集されたファイル一覧          │
└────────┬────────────────────────────┘
         │
         ▼
┌─────────────────────────────────────┐
│ 2. ユーザーに確認                    │
│    「次回セッション向けのメモは      │
│     ありますか？」                   │
└────────┬────────────────────────────┘
         │
         ▼
┌─────────────────────────────────────┐
│ 3. セッションファイルを生成・保存    │
│    ~/.musubix/sessions/              │
│    YYYY-MM-DD-HH-MM.md              │
└─────────────────────────────────────┘
```

**セッションファイルテンプレート**:
```markdown
# Session: {{date}}
**Date:** {{date}}
**Started:** {{startTime}}
**Last Updated:** {{endTime}}

---

## Current State

### Completed
{{#each completed}}
- [x] {{description}}
{{/each}}

### In Progress
{{#each inProgress}}
- [ ] {{description}}
{{/each}}

### Notes for Next Session
{{notesForNextSession}}

### Context to Load
\```
{{#each contextToLoad}}
{{this}}
{{/each}}
\```

### Files Modified
{{#each filesModified}}
- {{this}}
{{/each}}
```

---

#### DES-SM-003: Pre-Compact State Saving

**対応要件**: REQ-SM-003

**コンポーネント**: `SessionHook.onPreCompact`

**トリガー条件**:
- ツール呼び出し回数が閾値（50回）に到達
- ユーザーが明示的にcompactを要求
- システムが自動compactを実行

**保存データ**:
```typescript
interface PreCompactSnapshot {
  timestamp: Date;
  toolCallCount: number;
  currentPhase: 'planning' | 'implementation' | 'debugging' | 'review';
  criticalContext: {
    activeFiles: string[];
    currentTask: Task | null;
    recentDecisions: string[];
    unresolvedIssues: string[];
  };
}
```

---

#### DES-SM-004: TodoWrite統合

**対応要件**: REQ-SM-004

**コンポーネント**: `TodoTracker`

**インターフェース**:
```typescript
interface TodoTracker {
  // タスク追加
  addTask(task: {
    id: string;
    description: string;
    parentId?: string;      // サブタスクの場合
    order: number;
  }): void;
  
  // タスク完了
  completeTask(id: string): void;
  
  // 進捗取得
  getProgress(): {
    total: number;
    completed: number;
    inProgress: number;
    percentage: number;
  };
  
  // 順序検証
  validateOrder(): {
    isValid: boolean;
    issues: OrderIssue[];
  };
  
  // 欠落検出
  detectMissingSteps(context: string): string[];
}
```

**SKILL.md指示設計**:
```markdown
## マルチステップタスク管理

マルチステップタスクを開始する際は、TodoWriteツールで管理してください：

### タスクリスト作成
```
1. [ ] ステップ1: 〇〇を実装
2. [ ] ステップ2: △△を追加
3. [ ] ステップ3: テストを作成
4. [ ] ステップ4: ドキュメント更新
```

### 進捗更新
各ステップ完了時：
```
1. [x] ステップ1: 〇〇を実装 ✅
2. [ ] ステップ2: △△を追加 ← 現在
3. [ ] ステップ3: テストを作成
4. [ ] ステップ4: ドキュメント更新
```

### 検証ポイント
- 順序が論理的か確認
- 欠落ステップがないか確認
- 粒度が適切か確認（1ステップ = 1-2時間目安）
```

---

### 4.2 Context Optimizer スキル詳細設計

#### DES-CO-001: Strategic Compact Suggestion

**対応要件**: REQ-CO-001

**コンポーネント**: `CompactAdvisor`

**フェーズ検出ロジック**:
```typescript
interface PhaseDetector {
  detectCurrentPhase(context: SessionContext): Phase;
  isPhaseTransition(previous: Phase, current: Phase): boolean;
  getSuggestedCompactPoints(): CompactPoint[];
}

type Phase = 
  | 'planning'      // 計画・設計フェーズ
  | 'implementation' // 実装フェーズ
  | 'debugging'      // デバッグフェーズ
  | 'testing'        // テストフェーズ
  | 'review';        // レビューフェーズ

interface CompactPoint {
  phase: Phase;
  reason: string;
  priority: 'high' | 'medium' | 'low';
}
```

**提案メッセージテンプレート**:
```
💡 Strategic Compact Suggestion

現在のツール呼び出し回数: {{count}}回
現在のフェーズ: {{phase}}

推奨アクション: コンテキストの圧縮を検討してください

理由:
- {{reason}}

圧縮前に保存される情報:
- 完了タスク一覧
- 現在の作業コンテキスト
- 次回向けメモ

続行しますか？ (/compact で圧縮実行)
```

---

#### DES-CO-002: Tool Call Counter

**対応要件**: REQ-CO-002

**コンポーネント**: `ToolCallCounter`

**状態管理**:
```typescript
interface ToolCallCounter {
  count: number;
  threshold: number;        // デフォルト: 50
  reminderInterval: number; // デフォルト: 25
  lastReminder: number;
  
  increment(): void;
  shouldRemind(): boolean;
  shouldSuggestCompact(): boolean;
  reset(): void;
}
```

**リマインダーロジック**:
```
if (count >= threshold && (count - lastReminder) >= reminderInterval) {
  showReminder();
  lastReminder = count;
}
```

---

#### DES-CO-003: Context Mode Injection

**対応要件**: REQ-CO-003

**コンポーネント**: `ModeInjector`

**モード定義ファイル構造**:
```
.github/skills/context-optimizer/contexts/
├── dev.md       # 開発モード
├── review.md    # レビューモード
└── research.md  # 調査モード
```

**dev.md例**:
```markdown
# Development Mode Context

## Focus
実装・コーディングに集中します。

## Recommended Tools
- Edit: ファイル編集
- Write: 新規ファイル作成
- Bash: ビルド・テスト実行

## Guidelines
- テスト駆動開発（TDD）を推奨
- 小さなコミット単位で作業
- 型安全性を重視
```

---

#### DES-CO-004: PostToolUse Hooks

**対応要件**: REQ-CO-004

**コンポーネント**: `HookManager.postToolUse`

**Hook定義**:
```typescript
interface PostToolUseHook {
  trigger: {
    tools: ('Edit' | 'Write')[];
    filePatterns: string[];  // e.g., ['*.ts', '*.tsx']
  };
  actions: PostToolAction[];
}

interface PostToolAction {
  type: 'typeCheck' | 'format' | 'lint' | 'consoleLogDetect';
  command?: string;
  severity: 'error' | 'warning' | 'info';
}
```

**SKILL.md指示設計**:
```markdown
## ファイル編集後の自動チェック

TypeScript/JavaScriptファイルを編集した後は、以下を確認してください：

### 1. 型チェック（.ts, .tsx）
```bash
npx tsc --noEmit
```
エラーがある場合は修正を提案してください。

### 2. フォーマット確認
```bash
npx prettier --check <edited-file>
```

### 3. console.log検出
```bash
grep -n "console.log" <edited-file>
```
⚠️ console.logが残っている場合は警告してください。

### 4. 報告フォーマット
```
📝 PostToolUse Check Results
- Type Check: ✅ PASS / ❌ X errors
- Format: ✅ PASS / ❌ needs formatting
- Console.log: ✅ None / ⚠️ Found at line X
```
```

---

#### DES-CO-005: PreToolUse Hooks

**対応要件**: REQ-CO-005

**コンポーネント**: `HookManager.preToolUse`

**Hook定義**:
```typescript
interface PreToolUseHook {
  trigger: {
    tool: 'Bash';
    commandPatterns: RegExp[];
  };
  action: 'suggest' | 'warn' | 'block';
  message: string;
}

const PRE_TOOL_USE_HOOKS: PreToolUseHook[] = [
  {
    trigger: {
      tool: 'Bash',
      commandPatterns: [/^(npm|pnpm|yarn)\s+install/]
    },
    action: 'suggest',
    message: '⏳ 長時間コマンド検出。tmux内での実行を推奨します。'
  },
  {
    trigger: {
      tool: 'Bash',
      commandPatterns: [/^git\s+push/]
    },
    action: 'warn',
    message: '⚠️ git push前に変更内容を確認してください: git diff --stat'
  },
  {
    trigger: {
      tool: 'Bash',
      commandPatterns: [/^rm\s+-rf/, /^git\s+reset\s+--hard/]
    },
    action: 'warn',
    message: '🚨 破壊的操作です。本当に実行しますか？'
  }
];
```

---

#### DES-CO-006: Doc Blocker

**対応要件**: REQ-CO-006

**コンポーネント**: `HookManager.docBlocker`

**許可リスト**:
```typescript
const ALLOWED_DOC_PATTERNS = [
  /^README\.md$/i,
  /^CHANGELOG\.md$/i,
  /^LICENSE$/i,
  /^docs\//,
  /^\.github\//,
  /^\.claude\//
];

function shouldBlockDocCreation(filePath: string): boolean {
  const isMarkdown = /\.(md|txt)$/i.test(filePath);
  if (!isMarkdown) return false;
  
  return !ALLOWED_DOC_PATTERNS.some(pattern => pattern.test(filePath));
}
```

---

### 4.3 Learning Hooks スキル詳細設計

#### DES-LH-001: Continuous Learning Evaluation

**対応要件**: REQ-LH-001

**コンポーネント**: `PatternExtractor`

**抽出アルゴリズム**:
```typescript
interface PatternExtractor {
  analyze(session: SessionContext): ExtractedPattern[];
}

interface ExtractedPattern {
  type: PatternType;
  context: string;
  problem: string;
  solution: string;
  confidence: number;  // 0.0 - 1.0
  examples: string[];
}

type PatternType = 
  | 'error_resolution'      // エラー解決
  | 'user_corrections'      // ユーザー修正
  | 'workarounds'           // 回避策
  | 'debugging_techniques'  // デバッグ技法
  | 'project_specific';     // プロジェクト固有

// 抽出トリガー条件
const EXTRACTION_CONDITIONS = {
  minUserMessages: 10,
  minToolCalls: 20,
  sessionDuration: 30 * 60 * 1000  // 30分
};
```

---

#### DES-LH-002: Learned Skills Storage

**対応要件**: REQ-LH-002

**コンポーネント**: `SkillWriter`

**ストレージ構造**:
```
~/.musubix/skills/learned/
├── error-resolution-ts2322-fix/
│   └── SKILL.md
├── workaround-nextjs-cache/
│   └── SKILL.md
└── debugging-async-await/
    └── SKILL.md
```

**生成されるSKILL.md形式**:
```markdown
---
name: {{pattern-name}}
description: |
  {{pattern-description}}
extracted: {{date}}
confidence: {{confidence}}
license: MIT
---

# {{Descriptive Pattern Name}}

**Extracted:** {{date}}
**Context:** {{when-this-applies}}
**Confidence:** {{confidence}}

## Problem
{{problem-description}}

## Solution
{{solution-description}}

## Example
\```{{language}}
{{code-example}}
\```

## When to Use
{{trigger-conditions}}

## Related
- {{related-patterns}}
```

---

#### DES-LH-003: Pattern Ignore List

**対応要件**: REQ-LH-003

**コンポーネント**: `PatternFilter`

**フィルタールール**:
```typescript
interface PatternFilter {
  shouldIgnore(pattern: ExtractedPattern): boolean;
}

const IGNORE_RULES: IgnoreRule[] = [
  {
    name: 'typo-fix',
    condition: (p) => p.solution.length < 10 && p.type === 'user_corrections'
  },
  {
    name: 'temporary-issue',
    condition: (p) => p.context.includes('temporary') || p.context.includes('one-time')
  },
  {
    name: 'external-api-failure',
    condition: (p) => p.type === 'error_resolution' && 
                      (p.context.includes('API timeout') || 
                       p.context.includes('network error'))
  },
  {
    name: 'low-confidence',
    condition: (p) => p.confidence < 0.6
  }
];
```

---

### 4.4 Eval Harness スキル詳細設計

#### DES-EH-001〜002: Capability & Regression Eval

**対応要件**: REQ-EH-001, REQ-EH-002

**コンポーネント**: `CapabilityEval`, `RegressionEval`

**評価定義インターフェース**:
```typescript
interface CapabilityEval {
  name: string;
  task: string;
  successCriteria: Criterion[];
  expectedOutput: string;
}

interface RegressionEval {
  name: string;
  baseline: string;  // SHA or checkpoint name
  tests: TestResult[];
}

interface Criterion {
  description: string;
  met: boolean;
}

interface TestResult {
  name: string;
  status: 'PASS' | 'FAIL';
  previousStatus?: 'PASS' | 'FAIL';
}
```

---

#### DES-EH-003: pass@k Metrics

**対応要件**: REQ-EH-003

**コンポーネント**: `MetricsCalculator`

**計算ロジック**:
```typescript
interface MetricsCalculator {
  calculatePassAt1(results: boolean[]): number;
  calculatePassAt3(results: boolean[]): number;
  calculateConsecutiveAt3(results: boolean[]): number;
}

// pass@k = 1 - C(n-c, k) / C(n, k)
// n = 試行回数, c = 成功回数, k = target
function calculatePassAtK(n: number, c: number, k: number): number {
  if (n < k) return c > 0 ? 1 : 0;
  const numerator = combination(n - c, k);
  const denominator = combination(n, k);
  return 1 - (numerator / denominator);
}
```

---

#### DES-EH-004〜005: Grader Types

**対応要件**: REQ-EH-004, REQ-EH-005

**コンポーネント**: `Grader`

**Graderインターフェース**:
```typescript
interface Grader {
  grade(submission: Submission): GradeResult;
}

interface CodeBasedGrader extends Grader {
  command: string;
  expectedOutput?: string;
  expectedExitCode?: number;
}

interface ModelBasedGrader extends Grader {
  prompt: string;
  rubric: string[];
}

interface HumanGrader extends Grader {
  checklist: ChecklistItem[];
  reviewer?: string;
}

interface GradeResult {
  verdict: 'PASS' | 'FAIL';
  score?: number;
  notes?: string;
}
```

---

### 4.5 Verification Loop スキル詳細設計

#### DES-VL-001: Multi-Phase Verification

**対応要件**: REQ-VL-001

**コンポーネント**: `VerificationPipeline`

**パイプライン設計**:
```typescript
interface VerificationPipeline {
  phases: VerificationPhase[];
  execute(mode: 'quick' | 'full'): VerificationResult;
}

interface VerificationPhase {
  name: string;
  order: number;
  command: string;
  parser: OutputParser;
  failureAction: 'stop' | 'continue' | 'report';
}

const VERIFICATION_PHASES: VerificationPhase[] = [
  { name: 'Build', order: 1, command: 'npm run build', failureAction: 'stop' },
  { name: 'Type Check', order: 2, command: 'npx tsc --noEmit', failureAction: 'stop' },
  { name: 'Lint', order: 3, command: 'npm run lint', failureAction: 'report' },
  { name: 'Tests', order: 4, command: 'npm run test', failureAction: 'report' },
  { name: 'Security', order: 5, command: 'npm audit', failureAction: 'report' },
  { name: 'Diff Review', order: 6, command: 'git diff --stat', failureAction: 'report' }
];
```

---

#### DES-VL-002: Verification Report

**対応要件**: REQ-VL-002

**コンポーネント**: `ReportGenerator`

**レポートテンプレート**:
```
VERIFICATION REPORT
==================

Build:     {{buildStatus}} {{buildDetails}}
Types:     {{typeStatus}} ({{typeErrorCount}} errors)
Lint:      {{lintStatus}} ({{lintWarningCount}} warnings)
Tests:     {{testStatus}} ({{testsPassed}}/{{testsTotal}} passed, {{coverage}}% coverage)
Security:  {{securityStatus}} ({{securityIssues}} issues)
Diff:      {{diffFiles}} files changed

Overall:   {{overallStatus}} for PR

{{#if issues}}
Issues to Fix:
{{#each issues}}
{{@index}}. {{this}}
{{/each}}
{{/if}}
```

---

#### DES-VL-003: Continuous Verification

**対応要件**: REQ-VL-003

**コンポーネント**: `ContinuousVerifier`

**自動検証トリガー**:
```typescript
interface ContinuousVerifier {
  config: VerificationConfig;
  lastVerification: Date;
  changeTracker: ChangeTracker;
  
  shouldTriggerVerification(): boolean;
  scheduleNextVerification(): void;
}

interface VerificationConfig {
  intervalMinutes: number;      // デフォルト: 15分
  changeThreshold: number;      // デフォルト: 5ファイル
  autoSuggest: boolean;         // デフォルト: true
}

interface ChangeTracker {
  filesChanged: string[];
  lastChangeTime: Date;
  significantChanges: boolean;  // 構造的変更を検出
}
```

**トリガー条件**:
```
shouldTrigger = 
  (now - lastVerification >= intervalMinutes) ||
  (filesChanged.length >= changeThreshold) ||
  (significantChanges === true)
```

**提案メッセージ**:
```
⏰ Continuous Verification Suggestion

前回の検証から15分が経過しました。
変更されたファイル: {{count}}件

`/verify quick` を実行して状態を確認しますか？
```

---

#### DES-VL-004: Verification Modes

**対応要件**: REQ-VL-004

**コンポーネント**: `VerificationMode`

**モード定義**:
```typescript
interface VerificationMode {
  name: 'quick' | 'full';
  phases: string[];
  timeout: number;
}

const MODES: Record<string, VerificationMode> = {
  quick: {
    name: 'quick',
    phases: ['Type Check', 'Tests', 'Diff Review'],
    timeout: 60000  // 1分
  },
  full: {
    name: 'full',
    phases: ['Build', 'Type Check', 'Lint', 'Tests', 'Security', 'Diff Review'],
    timeout: 300000 // 5分
  }
};
```

---

#### DES-VL-005: Stop Hook監査

**対応要件**: REQ-VL-005

**コンポーネント**: `StopHookAuditor`

**監査ロジック**:
```typescript
interface StopHookAuditor {
  audit(editedFiles: string[]): AuditResult;
}

interface AuditResult {
  consoleLogFindings: Finding[];
  debuggerFindings: Finding[];
  todoFindings: Finding[];
  uncommittedChanges: string[];
}

interface Finding {
  file: string;
  line: number;
  content: string;
}

const AUDIT_PATTERNS = {
  consoleLog: /console\.(log|warn|error|info|debug)\(/,
  debugger: /\bdebugger\b/,
  todo: /\b(TODO|FIXME|XXX|HACK)\b/i
};
```

---

### 4.6 Checkpoint スキル詳細設計

#### DES-CP-001〜005: Checkpoint Management

**対応要件**: REQ-CP-001〜005

**コンポーネント**: `CheckpointManager`

**インターフェース**:
```typescript
interface CheckpointManager {
  create(name: string): Promise<Checkpoint>;
  verify(name: string): Promise<VerifyResult>;
  list(): Promise<Checkpoint[]>;
  restore(name: string): Promise<void>;
  cleanup(): Promise<void>;
}

interface Checkpoint {
  name: string;
  timestamp: Date;
  gitSha: string;
  verificationStatus: 'passed' | 'failed' | 'skipped';
  metadata: {
    filesChanged: number;
    testsStatus: string;
    coverage?: number;
  };
}
```

**ストレージ**:
```
~/.musubix/checkpoints/
└── checkpoints.log

# checkpoints.log format
2026-01-25-14:30 | feature-complete | abc123 | passed
2026-01-25-15:45 | debug-done | def456 | passed
```

---

### 4.7 Build Fix スキル詳細設計

#### DES-BF-001〜003: Build Error Resolution

**対応要件**: REQ-BF-001〜003

**コンポーネント**: `ErrorAnalyzer`, `IterativeFixer`

**エラー分類**:
```typescript
interface ErrorAnalyzer {
  analyze(output: string): CategorizedError[];
}

interface CategorizedError {
  category: ErrorCategory;
  code?: string;       // e.g., TS2322
  file: string;
  line: number;
  message: string;
  priority: 'high' | 'medium' | 'low';
  suggestedFix?: string;
}

type ErrorCategory = 
  | 'type_error'
  | 'import_error'
  | 'syntax_error'
  | 'lint_error'
  | 'config_error'
  | 'dependency_error';
```

**反復修正ロジック**:
```typescript
interface IterativeFixer {
  maxIterations: number;  // default: 10
  
  async fix(errors: CategorizedError[]): Promise<FixReport>;
}

interface FixReport {
  iterations: number;
  fixedErrors: number;
  remainingErrors: CategorizedError[];
  changedFiles: string[];
}
```

---

### 4.8 Codemap スキル詳細設計

#### DES-CM-001〜004: Codemap Generation

**対応要件**: REQ-CM-001〜004

**コンポーネント**: `StructureAnalyzer`, `CodemapGenerator`

**解析結果**:
```typescript
interface RepositoryStructure {
  workspaces: Workspace[];
  entryPoints: string[];
  frameworks: string[];
}

interface ModuleAnalysis {
  exports: Export[];
  imports: Import[];
  routes?: Route[];
  models?: Model[];
  workers?: Worker[];
}

interface CodemapOutput {
  index: string;           // INDEX.md
  frontend?: string;       // frontend.md
  backend?: string;        // backend.md
  database?: string;       // database.md
  integrations?: string;   // integrations.md
  workers?: string;        // workers.md
}
```

**差分閾値**:
```typescript
interface DiffAnalyzer {
  calculateDiffPercentage(old: string, new: string): number;
  shouldRequireApproval(diffPercent: number, threshold?: number): boolean;
}

const DEFAULT_DIFF_THRESHOLD = 30; // 30%以上の変更で承認要求
```

---

### 4.9 Refactor Cleaner スキル詳細設計

#### DES-RC-001〜004: Dead Code Detection & Cleanup

**対応要件**: REQ-RC-001〜004

**コンポーネント**: `DeadCodeDetector`, `SafeDeleter`, `RiskClassifier`

**検出ツール統合**:
```typescript
interface DeadCodeDetector {
  tools: DetectionTool[];
  detect(): Promise<DeadCodeCandidate[]>;
}

interface DetectionTool {
  name: 'knip' | 'depcheck' | 'ts-prune';
  command: string;
  parser: (output: string) => DeadCodeCandidate[];
}

interface DeadCodeCandidate {
  type: 'file' | 'export' | 'dependency';
  path: string;
  name?: string;
  risk: 'SAFE' | 'CAUTION' | 'DANGER';
  reason: string;
}
```

**リスク分類**:
```typescript
interface RiskClassifier {
  classify(candidate: DeadCodeCandidate): RiskLevel;
}

const RISK_RULES = {
  SAFE: [
    'no references in static analysis',
    'internal module only',
    'test file only'
  ],
  CAUTION: [
    'dynamic import possible',
    'reflection usage nearby',
    'string-based reference'
  ],
  DANGER: [
    'public API',
    'entry point',
    'exported from index'
  ]
};
```

---

### 4.10 E2E Runner スキル詳細設計

#### DES-E2E-001〜003: E2E Test Management

**対応要件**: REQ-E2E-001〜003

**コンポーネント**: `TestGenerator`, `PlaywrightRunner`, `E2EReporter`

**テスト生成**:
```typescript
interface TestGenerator {
  generate(flow: UserFlow): GeneratedTest;
}

interface UserFlow {
  name: string;
  steps: FlowStep[];
}

interface FlowStep {
  action: 'navigate' | 'click' | 'fill' | 'assert' | 'wait';
  selector?: string;
  value?: string;
  expected?: string;
}

interface GeneratedTest {
  specFile: string;
  fixtureFile?: string;
}
```

**実行オプション**:
```typescript
interface PlaywrightRunner {
  run(options: RunOptions): Promise<E2EResult>;
}

interface RunOptions {
  flow?: string;
  headed?: boolean;
  debug?: boolean;
  trace?: boolean;
}
```

---

## 5. 設計パターン適用

### 5.1 適用パターン一覧

| パターン | 適用箇所 | 理由 |
|---------|---------|------|
| **Strategy** | VerificationMode, Grader | モード/評価方式の切り替え |
| **Observer** | HookManager | ツール実行の監視・通知 |
| **Template Method** | VerificationPipeline | 検証フェーズの順序制御 |
| **Factory** | PatternExtractor | パターンタイプごとの生成 |
| **Repository** | SessionStore, CheckpointManager | データ永続化の抽象化 |
| **Chain of Responsibility** | ErrorAnalyzer | エラー分類の連鎖処理 |
| **Command** | PreToolUseHook, PostToolUseHook | Hook実行のカプセル化 |

### 5.2 SOLID原則準拠

| 原則 | 適用例 |
|------|--------|
| **S**ingle Responsibility | 各コンポーネントは単一責務（SessionStore=保存のみ） |
| **O**pen/Closed | Graderインターフェースで拡張可能 |
| **L**iskov Substitution | Grader実装は互換性を維持 |
| **I**nterface Segregation | 小さなインターフェース（Grader, Detector等） |
| **D**ependency Inversion | 具象クラスではなくインターフェースに依存 |

---

## 6. ディレクトリ構造（最終形）

```
.github/skills/
├── session-manager/
│   ├── SKILL.md
│   └── scripts/
│       ├── session-start.sh
│       └── session-end.sh
├── context-optimizer/
│   ├── SKILL.md
│   └── contexts/
│       ├── dev.md
│       ├── review.md
│       └── research.md
├── learning-hooks/
│   ├── SKILL.md
│   └── templates/
│       └── learned-skill-template.md
├── eval-harness/
│   ├── SKILL.md
│   └── examples/
│       ├── capability-eval.md
│       └── regression-eval.md
├── verification-loop/
│   ├── SKILL.md
│   └── scripts/
│       └── verify.sh
├── checkpoint/
│   └── SKILL.md
├── codemap/
│   ├── SKILL.md
│   └── templates/
│       └── codemap-index.md
├── refactor-cleaner/
│   └── SKILL.md
├── build-fix/
│   └── SKILL.md
└── e2e-runner/
    └── SKILL.md

~/.musubix/
├── sessions/
│   └── YYYY-MM-DD-HH-MM.md
├── checkpoints/
│   └── checkpoints.log
└── skills/
    └── learned/
        └── <pattern-name>/
            └── SKILL.md
```

---

## 7. 非機能要件への対応

### 7.1 パフォーマンス（NFR-001）

| 要件 | 設計対応 |
|------|---------|
| Hook実行 100ms以下 | 軽量なShellスクリプト使用、非同期処理 |
| セッション保存 500ms以下 | Markdown形式で即時書き込み |
| パターン抽出 5秒以下 | バックグラウンド処理、キャッシュ活用 |
| 検証ループ 60秒以下 | quick/fullモードの分離、並列実行 |

### 7.2 ストレージ（NFR-002）

| 要件 | 設計対応 |
|------|---------|
| セッションファイル 1MB以下 | 差分のみ保存、圧縮前スナップショット |
| 30日自動削除 | cleanup()メソッドでcron/スケジュール実行 |
| チェックポイント 10件 | RetentionPolicyによる自動整理 |
| 学習パターン 500件 | 信頼度閾値、古いパターン整理 |

### 7.3 互換性（NFR-003）

| 環境 | 対応方式 |
|------|---------|
| GitHub Copilot | `.github/skills/`配置 |
| Claude Code | `.claude/skills/`へのシンボリックリンク |
| Copilot CLI | `~/.copilot/skills/`へのコピー |
| MUSUBIX MCP | MCPツール呼び出し指示をSKILL.mdに記載 |

### 7.4 セキュリティ（NFR-004）

| 要件 | 設計対応 |
|------|----------|
| 学習データローカル保存 | `~/.musubix/`配下のみ、外部API送信なし |
| 機密情報フィルタ | `SensitiveDataFilter`による自動検出・除外 |
| セッションデータ共有禁止 | 明示的同意なしの共有を禁止 |

**機密情報フィルタ設計**:
```typescript
interface SensitiveDataFilter {
  patterns: SensitivePattern[];
  filter(content: string): string;
  detect(content: string): SensitiveMatch[];
}

const SENSITIVE_PATTERNS: SensitivePattern[] = [
  { name: 'api_key', pattern: /['"]?[a-zA-Z_]*(?:api[_-]?key|apikey)['"]?\s*[:=]\s*['"][^'"]+['"]/gi },
  { name: 'password', pattern: /['"]?password['"]?\s*[:=]\s*['"][^'"]+['"]/gi },
  { name: 'secret', pattern: /['"]?[a-zA-Z_]*secret['"]?\s*[:=]\s*['"][^'"]+['"]/gi },
  { name: 'token', pattern: /['"]?[a-zA-Z_]*token['"]?\s*[:=]\s*['"][^'"]+['"]/gi },
  { name: 'aws_key', pattern: /AKIA[0-9A-Z]{16}/g },
  { name: 'private_key', pattern: /-----BEGIN (?:RSA |EC )?PRIVATE KEY-----/g },
];

function filterSensitiveData(content: string): string {
  let filtered = content;
  for (const pattern of SENSITIVE_PATTERNS) {
    filtered = filtered.replace(pattern.pattern, `[REDACTED:${pattern.name}]`);
  }
  return filtered;
}
```

**適用箇所**:
- `SessionStore.save()`: セッション保存前にフィルタ適用
- `PatternExtractor.analyze()`: パターン抽出前にフィルタ適用
- `SkillWriter.write()`: 学習スキル保存前にフィルタ適用

---

## 8. リスク軽減策

| リスク | 軽減策設計 |
|--------|-----------|
| コンテキスト消費 | ToolCallCounterによる早期警告、Strategic Compact |
| Hook実行オーバーヘッド | 条件付きHook実行、キャッシュ活用 |
| パターン誤抽出 | PatternFilter、信頼度閾値0.6、ユーザー確認 |
| チェックポイント肥大化 | RetentionPolicy（最新10件）、cleanup() |

---

## 9. MUSUBIXワークフロー統合設計

### 9.1 統合アーキテクチャ

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    MUSUBIX + Agent Skills 統合アーキテクチャ                  │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌───────────────────────────────────────────────────────────────────────┐ │
│  │                     GitHub Copilot / Claude Code                       │ │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │ │
│  │  │              Agent Skills (.github/skills/)                      │  │ │
│  │  │  session-manager | context-optimizer | learning-hooks | ...     │  │ │
│  │  └──────────────────────────┬──────────────────────────────────────┘  │ │
│  └─────────────────────────────┼─────────────────────────────────────────┘ │
│                                │                                           │
│                                │ MCP Protocol                              │
│                                ▼                                           │
│  ┌───────────────────────────────────────────────────────────────────────┐ │
│  │                      MUSUBIX MCP Server                                │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  │ │
│  │  │ workflow-   │  │  pattern-   │  │  knowledge  │  │  policy     │  │ │
│  │  │ engine      │  │  mcp        │  │  store      │  │  engine     │  │ │
│  │  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘  │ │
│  └─────────┼────────────────┼────────────────┼────────────────┼─────────┘ │
│            │                │                │                │           │
│            ▼                ▼                ▼                ▼           │
│  ┌───────────────────────────────────────────────────────────────────────┐ │
│  │                         統合レイヤー                                   │ │
│  │  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐       │ │
│  │  │ SkillWorkflow   │  │ SkillPattern    │  │ SkillKnowledge  │       │ │
│  │  │ Bridge          │  │ Bridge          │  │ Bridge          │       │ │
│  │  └─────────────────┘  └─────────────────┘  └─────────────────┘       │ │
│  └───────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 9.2 ワークフローフェーズとスキルのマッピング

MUSUBIX Workflow Engine（5フェーズ）とAgent Skillsの連携：

| Workflowフェーズ | 対応スキル | 連携内容 |
|-----------------|-----------|----------|
| **Phase 1: 要件定義** | session-manager | セッション開始時にコンテキスト復元 |
| | context-optimizer | 調査モード（research）注入 |
| **Phase 2: 設計** | context-optimizer | 開発モード（dev）注入 |
| | codemap | 既存アーキテクチャの可視化 |
| **Phase 3: タスク分解** | session-manager | TodoWrite統合でタスク追跡 |
| | checkpoint | 設計完了時にチェックポイント作成 |
| **Phase 4: 実装** | build-fix | ビルドエラー自動解決 |
| | verification-loop | 継続的検証（15分間隔） |
| | learning-hooks | パターン抽出（バックグラウンド） |
| **Phase 5: レビュー** | verification-loop | Full検証実行 |
| | context-optimizer | レビューモード（review）注入 |
| | eval-harness | pass@k評価 |
| | refactor-cleaner | デッドコード検出 |

### 9.3 SkillWorkflowBridge設計

```typescript
interface SkillWorkflowBridge {
  // ワークフロー状態とスキル連携
  onPhaseChange(phase: WorkflowPhase): Promise<void>;
  getCurrentPhase(): WorkflowPhase;
  
  // スキルからワークフローへの通知
  notifyVerificationResult(result: VerificationResult): Promise<void>;
  notifyCheckpointCreated(checkpoint: Checkpoint): Promise<void>;
  notifyPatternLearned(pattern: LearnedPattern): Promise<void>;
}

type WorkflowPhase = 
  | 'requirements'  // Phase 1
  | 'design'        // Phase 2
  | 'tasks'         // Phase 3
  | 'implementation'// Phase 4
  | 'review';       // Phase 5

// フェーズ変更時の自動アクション
const PHASE_SKILL_ACTIONS: Record<WorkflowPhase, SkillAction[]> = {
  requirements: [
    { skill: 'session-manager', action: 'loadContext' },
    { skill: 'context-optimizer', action: 'injectMode', params: { mode: 'research' } },
  ],
  design: [
    { skill: 'codemap', action: 'generateOverview' },
    { skill: 'context-optimizer', action: 'injectMode', params: { mode: 'dev' } },
  ],
  tasks: [
    { skill: 'session-manager', action: 'enableTodoTracking' },
    { skill: 'checkpoint', action: 'create', params: { name: 'design-complete' } },
  ],
  implementation: [
    { skill: 'verification-loop', action: 'enableContinuous' },
    { skill: 'build-fix', action: 'watchErrors' },
  ],
  review: [
    { skill: 'verification-loop', action: 'runFull' },
    { skill: 'context-optimizer', action: 'injectMode', params: { mode: 'review' } },
    { skill: 'refactor-cleaner', action: 'detectDeadCode' },
  ],
};
```

### 9.4 SkillPatternBridge設計

learning-hooksスキルとpattern-mcp MCPツールの連携：

```typescript
interface SkillPatternBridge {
  // 学習スキルからパターンライブラリへの保存
  saveLearnedPattern(pattern: LearnedPattern): Promise<void>;
  
  // パターンライブラリからスキル候補の取得
  suggestSkillsForContext(context: string): Promise<SkillSuggestion[]>;
  
  // パターン圧縮・統合
  consolidatePatterns(): Promise<ConsolidationResult>;
}

interface LearnedPattern {
  type: PatternType;
  name: string;
  problem: string;
  solution: string;
  confidence: number;
  source: 'session' | 'user_correction' | 'error_resolution';
}

// 連携フロー
// 1. learning-hooks → LearnedPattern抽出
// 2. SkillPatternBridge.saveLearnedPattern()
// 3. pattern-mcp.pattern_store() でライブラリに保存
// 4. 次回セッション開始時に pattern-mcp.pattern_query() で関連パターン取得
// 5. session-manager がコンテキストに注入
```

### 9.5 SkillKnowledgeBridge設計

スキルとKnowledge Store（@musubix/knowledge）の連携：

```typescript
interface SkillKnowledgeBridge {
  // セッション情報をKnowledge Graphに保存
  persistSession(session: SessionData): Promise<void>;
  
  // チェックポイントをエンティティとして保存
  persistCheckpoint(checkpoint: Checkpoint): Promise<void>;
  
  // 学習パターンをエンティティとして保存
  persistLearnedPattern(pattern: LearnedPattern): Promise<void>;
  
  // 関連コンテキストの検索
  queryRelatedContext(query: string): Promise<RelatedContext[]>;
}

// Knowledge Graph エンティティ構造
const SESSION_ENTITY = {
  id: 'session:2026-01-25-14-30',
  type: 'session',
  properties: {
    date: '2026-01-25',
    duration: 180,  // minutes
    tasksCompleted: 5,
    patternsLearned: 2,
  },
  relations: [
    { target: 'checkpoint:design-complete', type: 'created' },
    { target: 'pattern:ts2322-fix', type: 'learned' },
  ],
};
```

### 9.6 MCPツール呼び出し統合

Agent SkillsからMUSUBIX MCPツールを呼び出す指示テンプレート：

```markdown
## MCPツール統合（SKILL.md共通セクション）

このスキルは以下のMUSUBIX MCPツールと連携します。
MCPツールが利用可能な場合は、それらを優先的に使用してください。

### workflow-engine連携
- `workflow_get_status`: 現在のワークフローフェーズを取得
- `workflow_advance_phase`: 次フェーズへの遷移（品質ゲート検証付き）

### pattern-mcp連携
- `pattern_query`: 関連パターンの検索
- `pattern_store`: 新規パターンの保存

### knowledge連携
- `knowledge_query`: 関連コンテキストの検索
- `knowledge_put_entity`: エンティティの保存

### policy連携
- `policy_validate`: ポリシー準拠の検証

使用例:
```
MCPツール workflow_get_status を呼び出して現在のフェーズを確認
→ Phase 4 (implementation) の場合、build-fix と verification-loop を有効化
```
```

### 9.7 品質ゲート統合

verification-loopスキルとExtendedQualityGate（v3.6.0）の連携：

```typescript
interface QualityGateIntegration {
  // verification-loopの結果をQualityGateに反映
  mapVerificationToGate(result: VerificationResult): QualityGateResult;
  
  // 品質ゲート通過判定
  checkGatePass(phase: WorkflowPhase): Promise<boolean>;
}

// マッピング
const VERIFICATION_TO_GATE_MAP = {
  build: 'build_success',
  typeCheck: 'type_safety',
  lint: 'code_quality',
  tests: 'test_coverage',
  security: 'security_scan',
  diff: 'pr_readiness',
};

// フェーズごとの必須ゲート
const PHASE_REQUIRED_GATES: Record<WorkflowPhase, string[]> = {
  requirements: [],
  design: ['architecture_review'],
  tasks: ['task_decomposition'],
  implementation: ['build_success', 'type_safety', 'test_coverage'],
  review: ['build_success', 'type_safety', 'code_quality', 'test_coverage', 'security_scan'],
};
```

### 9.8 イベントフロー図

```
┌──────────────┐     ┌──────────────┐     ┌──────────────┐
│  User Action │────▶│ Agent Skill  │────▶│  MCP Tool    │
└──────────────┘     └──────┬───────┘     └──────┬───────┘
                            │                    │
                            │  Skill Event       │  MCP Response
                            ▼                    ▼
                     ┌──────────────┐     ┌──────────────┐
                     │ SkillBridge  │◀────│   MUSUBIX    │
                     │              │     │   Backend    │
                     └──────┬───────┘     └──────────────┘
                            │
                            │  Workflow Update
                            ▼
                     ┌──────────────┐
                     │  Knowledge   │
                     │    Graph     │
                     └──────────────┘
```

**イベント例**:
1. ユーザーが「実装開始」と入力
2. session-manager がセッション状態を復元
3. context-optimizer が`dev`モードを注入
4. workflow_get_status MCPツールでPhase確認
5. Phase 4の場合、build-fixとverification-loopを有効化
6. 変更検出時にverification-loopが自動検証を提案
7. 検証結果をQualityGateに反映
8. 品質ゲート通過でPhase 5への遷移を提案

---

## 10. 次ステップ（タスク分解への入力）

設計完了後、Phase 3（タスク分解）で以下のTSKファイルを生成予定：

### 10.1 スキル実装タスク

| タスクID | 対象スキル | 概要 |
|---------|-----------|------|
| TSK-SM-001〜004 | session-manager | SKILL.md作成、scripts/作成 |
| TSK-CO-001〜006 | context-optimizer | SKILL.md作成、contexts/作成 |
| TSK-LH-001〜003 | learning-hooks | SKILL.md作成、templates/作成 |
| TSK-EH-001〜005 | eval-harness | SKILL.md作成、examples/作成 |
| TSK-VL-001〜005 | verification-loop | SKILL.md作成、scripts/作成 |
| TSK-CP-001〜005 | checkpoint | SKILL.md作成 |
| TSK-BF-001〜003 | build-fix | SKILL.md作成 |
| TSK-CM-001〜004 | codemap | SKILL.md作成、templates/作成 |
| TSK-RC-001〜004 | refactor-cleaner | SKILL.md作成 |
| TSK-E2E-001〜003 | e2e-runner | SKILL.md作成 |

### 10.2 統合タスク（追加）

| タスクID | 対象 | 概要 |
|---------|------|------|
| TSK-INT-001 | SkillWorkflowBridge | ワークフロー統合インターフェース実装 |
| TSK-INT-002 | SkillPatternBridge | パターンライブラリ連携実装 |
| TSK-INT-003 | SkillKnowledgeBridge | Knowledge Graph連携実装 |
| TSK-INT-004 | SensitiveDataFilter | セキュリティフィルタ実装 |
| TSK-INT-005 | QualityGateIntegration | 品質ゲート連携実装 |

---

**Author**: MUSUBIX Team  
**Version**: 3.7.0-draft  
**Date**: 2026-01-25
