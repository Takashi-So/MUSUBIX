# DES-ENHANCEMENT-v2.4.0: Claude Code統合設計

**Version**: 2.4.0  
**Created**: 2026-01-11  
**Status**: Draft  
**Traceability**: REQ-ENHANCEMENT-v2.4.0-Claude-Code-Integration.md

---

## 1. 設計概要

### 1.1 目的

Claude Code Templates（davila7/claude-code-templates）から抽出したベストプラクティスをMUSUBIXに統合し、以下を実現する：

1. **Subagent-Driven Development**: 複雑なタスクを専門エージェントに分解
2. **Parallel Agent Dispatching**: 独立タスクの並列実行
3. **Skills Architecture**: モジュラーな能力定義
4. **Structured Workflow**: Phase 1-5の自動オーケストレーション

### 1.2 設計原則

| 原則 | 適用 |
|------|------|
| Library-First (Art. I) | 新機能は独立パッケージとして実装 |
| CLI Interface (Art. II) | 全機能にCLIエントリーポイント |
| Test-First (Art. III) | Red-Green-Blue開発サイクル |
| Traceability (Art. V) | REQ→DES→TSK→Code完全追跡 |

### 1.3 トレーサビリティマトリクス

| 要件ID | 設計ID | 概要 |
|--------|--------|------|
| REQ-SDD-001 | DES-SDD-001 | タスク複雑度評価 |
| REQ-SDD-002 | DES-SDD-002 | サブエージェント分解 |
| REQ-SDD-003 | DES-SDD-003 | コンテキスト共有 |
| REQ-PAD-001 | DES-PAD-001 | 依存関係分析 |
| REQ-PAD-002 | DES-PAD-002 | 並列実行 |
| REQ-PAD-003 | DES-PAD-003 | 結果統合 |
| REQ-SKILL-001 | DES-SKILL-001 | Progressive Disclosure |
| REQ-SKILL-002 | DES-SKILL-002 | ディレクトリ構造 |
| REQ-AGENT-001 | DES-AGENT-001 | AGENTS.md拡張 |
| REQ-AGENT-002 | DES-AGENT-002 | 役割ベースエージェント |
| REQ-ORCH-001 | DES-ORCH-001 | Phase遷移 |
| REQ-ORCH-002 | DES-ORCH-002 | 状態管理 |
| REQ-ORCH-003 | DES-ORCH-003 | 品質ゲート |
| REQ-MCP-001 | DES-MCP-001 | ツール命名規則 |
| REQ-MCP-002 | DES-MCP-002 | アノテーション |
| REQ-MCP-003 | DES-MCP-003 | 例外処理 |
| REQ-NFR-001 | DES-NFR-001 | パフォーマンス |
| REQ-NFR-002 | DES-NFR-002 | 後方互換性 |

---

## 2. C4モデル - Context

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           MUSUBIX v2.4.0 Context                            │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│    ┌──────────────┐          ┌──────────────────────────────────┐          │
│    │   Developer  │          │         IDE / Editor              │          │
│    │   (Human)    │◄────────►│  (VS Code + Copilot Extension)   │          │
│    └──────────────┘          └───────────────┬──────────────────┘          │
│                                              │                              │
│                                              │ MCP Protocol                 │
│                                              ▼                              │
│    ┌──────────────┐          ┌──────────────────────────────────┐          │
│    │ AI Assistants│          │                                  │          │
│    │ (Claude,     │◄────────►│        MUSUBIX System            │          │
│    │  Copilot)    │  stdio   │                                  │          │
│    └──────────────┘          └───────────────┬──────────────────┘          │
│                                              │                              │
│                              ┌───────────────┼───────────────┐              │
│                              ▼               ▼               ▼              │
│                     ┌────────────┐   ┌────────────┐   ┌────────────┐       │
│                     │    YATA    │   │  Project   │   │  External  │       │
│                     │ Knowledge  │   │   Files    │   │   APIs     │       │
│                     │   Graph    │   │            │   │            │       │
│                     └────────────┘   └────────────┘   └────────────┘       │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 外部アクター

| アクター | 役割 | インタラクション |
|---------|------|-----------------|
| Developer | システム利用者 | CLI/IDE経由で操作 |
| AI Assistant | コード生成・分析 | MCP Protocol経由 |
| YATA | 知識グラフ | Query/Update |
| Project Files | ソースコード | Read/Write |

---

## 3. C4モデル - Container

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         MUSUBIX v2.4.0 Containers                           │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                        MCP Server Layer                              │   │
│  │  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐            │   │
│  │  │  Agent Tools  │  │ Workflow Tools│  │  Skill Tools  │            │   │
│  │  │  (agent_*)    │  │ (workflow_*)  │  │  (skill_*)    │            │   │
│  │  └───────┬───────┘  └───────┬───────┘  └───────┬───────┘            │   │
│  │          │                  │                  │                     │   │
│  │  ┌───────┴──────────────────┴──────────────────┴───────┐            │   │
│  │  │              Existing SDD Tools (sdd_*)             │◄──┐        │   │
│  │  │  sdd_create_requirements, sdd_validate_requirements │   │        │   │
│  │  │  sdd_create_design, sdd_create_tasks, etc.          │   │        │   │
│  │  └─────────────────────────┬───────────────────────────┘   │        │   │
│  └────────────────────────────┼───────────────────────────────┼────────┘   │
│                               │                               │            │
│  ┌────────────────────────────┼───────────────────────────────┼────────┐   │
│  │                    Core Services Layer                     │        │   │
│  │                            │                               │        │   │
│  │  ┌─────────────────────────▼───────────────────────────┐   │        │   │
│  │  │              Agent Orchestrator (NEW)                │   │        │   │
│  │  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  │   │        │   │
│  │  │  │ Complexity  │  │  Subagent   │  │  Context    │  │   │        │   │
│  │  │  │  Analyzer   │  │ Dispatcher  │  │  Manager    │  │   │        │   │
│  │  │  └─────────────┘  └─────────────┘  └─────────────┘  │   │        │   │
│  │  └─────────────────────────┬───────────────────────────┘   │        │   │
│  │                            │                               │        │   │
│  │  ┌─────────────────────────▼───────────────────────────┐   │        │   │
│  │  │             Workflow Engine (NEW)                    │   │        │   │
│  │  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  │   │        │   │
│  │  │  │   Phase     │  │   State     │  │  Quality    │  │   │        │   │
│  │  │  │ Controller  │  │  Tracker    │  │   Gate      │  │   │ Back-  │   │
│  │  │  └─────────────┘  └─────────────┘  └─────────────┘  │   │ compat │   │
│  │  └─────────────────────────┬───────────────────────────┘   │        │   │
│  │                            │                               │        │   │
│  │  ┌─────────────────────────▼───────────────────────────┐   │        │   │
│  │  │              Skill Manager (NEW)                     │   │        │   │
│  │  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  │   │        │   │
│  │  │  │   Skill     │  │   Skill     │  │   Skill     │  │   │        │   │
│  │  │  │  Registry   │  │   Loader    │  │  Validator  │  │   │        │   │
│  │  │  └─────────────┘  └─────────────┘  └─────────────┘  │   │        │   │
│  │  └─────────────────────────────────────────────────────┘   │        │   │
│  │                                                            │        │   │
│  │  ┌─────────────────────────────────────────────────────────┘        │   │
│  │  │  Existing Core Services                                          │   │
│  │  │  (EARS Validator, Code Generator, Design Generator, etc.)        │   │
│  │  └──────────────────────────────────────────────────────────────────┘   │
│  └─────────────────────────────────────────────────────────────────────────┘
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 新規コンテナ

| コンテナ | パッケージ | 役割 |
|---------|-----------|------|
| Agent Orchestrator | `packages/agent-orchestrator/` | サブエージェント管理 |
| Workflow Engine | `packages/workflow-engine/` | Phase遷移・状態管理 |
| Skill Manager | `packages/skill-manager/` | スキル読み込み・検証 |

### 既存コンテナ（維持）

| コンテナ | パッケージ | 変更 |
|---------|-----------|------|
| MCP Server | `packages/mcp-server/` | 新ツール追加 |
| Core | `packages/core/` | 変更なし |
| YATA Client | `packages/yata-client/` | 変更なし |

---

## 4. C4モデル - Component

### 4.1 Agent Orchestrator コンポーネント

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    packages/agent-orchestrator/                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  src/                                                                       │
│  ├── domain/                                                                │
│  │   ├── entities/                                                          │
│  │   │   ├── Task.ts              # タスクエンティティ                      │
│  │   │   ├── SubagentSpec.ts      # サブエージェント仕様                    │
│  │   │   └── ExecutionContext.ts  # 実行コンテキスト                        │
│  │   ├── value-objects/                                                     │
│  │   │   ├── ComplexityScore.ts   # 複雑度スコア (1-10)                     │
│  │   │   ├── TaskPriority.ts      # タスク優先度                            │
│  │   │   └── AgentRole.ts         # エージェント役割                        │
│  │   └── services/                                                          │
│  │       └── ComplexityAnalyzer.ts # 複雑度分析ドメインサービス             │
│  │                                                                          │
│  ├── application/                                                           │
│  │   ├── SubagentDispatcher.ts    # サブエージェント割り当て                │
│  │   ├── ContextManager.ts        # コンテキスト共有管理                    │
│  │   ├── ParallelExecutor.ts      # 並列実行エンジン                        │
│  │   └── ResultAggregator.ts      # 結果統合                                │
│  │                                                                          │
│  ├── infrastructure/                                                        │
│  │   ├── SubagentAdapter.ts       # runSubagent呼び出しアダプタ             │
│  │   └── YATAContextStore.ts      # YATA経由コンテキスト永続化              │
│  │                                                                          │
│  └── interface/                                                             │
│      ├── cli/                                                               │
│      │   └── agent-commands.ts    # CLIコマンド                             │
│      └── mcp/                                                               │
│          └── agent-tools.ts       # MCPツール定義                           │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

#### DES-SDD-001: ComplexityAnalyzer

**トレーサビリティ**: REQ-SDD-001

```typescript
// packages/agent-orchestrator/src/domain/services/ComplexityAnalyzer.ts

export interface ComplexityScore {
  readonly value: number;        // 1-10
  readonly factors: ComplexityFactor[];
  readonly threshold: number;    // デフォルト: 7
}

export interface ComplexityFactor {
  name: string;
  weight: number;
  score: number;
  description: string;
}

export interface IComplexityAnalyzer {
  analyze(task: Task): ComplexityScore;
  shouldDecompose(score: ComplexityScore): boolean;
}

export const createComplexityAnalyzer = (): IComplexityAnalyzer => {
  const factors: ComplexityFactor[] = [
    { name: 'scope', weight: 0.3, score: 0, description: '影響範囲' },
    { name: 'dependencies', weight: 0.25, score: 0, description: '依存関係数' },
    { name: 'fileCount', weight: 0.2, score: 0, description: '変更ファイル数' },
    { name: 'testCoverage', weight: 0.15, score: 0, description: 'テスト必要量' },
    { name: 'uncertainty', weight: 0.1, score: 0, description: '不確実性' },
  ];

  return {
    analyze: (task: Task): ComplexityScore => {
      // 実装: 各因子をスコアリングして加重平均
      const value = factors.reduce((sum, f) => sum + f.weight * f.score, 0);
      return { value, factors, threshold: 7 };
    },
    shouldDecompose: (score: ComplexityScore): boolean => {
      return score.value >= score.threshold;
    },
  };
};
```

#### DES-SDD-002: SubagentDispatcher

**トレーサビリティ**: REQ-SDD-002

```typescript
// packages/agent-orchestrator/src/application/SubagentDispatcher.ts

export interface SubagentSpec {
  id: string;
  role: AgentRole;
  prompt: string;
  inputContext: ExecutionContext;
  outputExpectation: string;
}

export interface AgentRole {
  name: 'requirements' | 'design' | 'implementation' | 'test' | 'review';
  capabilities: string[];
  constraints: string[];
}

export interface ISubagentDispatcher {
  decompose(task: Task, score: ComplexityScore): SubagentSpec[];
  dispatch(spec: SubagentSpec): Promise<SubagentResult>;
  aggregate(results: SubagentResult[]): AggregatedResult;
}
```

#### DES-SDD-003: ContextManager

**トレーサビリティ**: REQ-SDD-003

```typescript
// packages/agent-orchestrator/src/application/ContextManager.ts

export interface ExecutionContext {
  taskId: string;
  parentContext?: ExecutionContext;
  sharedKnowledge: Map<string, unknown>;
  artifacts: Artifact[];
  timestamp: Date;
}

export interface IContextManager {
  create(taskId: string, parent?: ExecutionContext): ExecutionContext;
  share(context: ExecutionContext, key: string, value: unknown): void;
  merge(contexts: ExecutionContext[]): ExecutionContext;
  persist(context: ExecutionContext): Promise<void>;
  restore(taskId: string): Promise<ExecutionContext | null>;
}
```

---

### 4.2 Workflow Engine コンポーネント

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      packages/workflow-engine/                              │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  src/                                                                       │
│  ├── domain/                                                                │
│  │   ├── entities/                                                          │
│  │   │   ├── Workflow.ts          # ワークフローエンティティ                │
│  │   │   ├── Phase.ts             # フェーズエンティティ                    │
│  │   │   └── QualityGate.ts       # 品質ゲートエンティティ                  │
│  │   ├── value-objects/                                                     │
│  │   │   ├── PhaseType.ts         # Phase 1-5 enum                          │
│  │   │   ├── TaskStatus.ts        # not-started/in-progress/completed/failed│
│  │   │   └── ApprovalStatus.ts    # pending/approved/rejected               │
│  │   └── events/                                                            │
│  │       ├── PhaseTransitioned.ts # フェーズ遷移イベント                    │
│  │       └── QualityGatePassed.ts # 品質ゲート通過イベント                  │
│  │                                                                          │
│  ├── application/                                                           │
│  │   ├── PhaseController.ts       # フェーズ遷移制御                        │
│  │   ├── StateTracker.ts          # 状態追跡                                │
│  │   ├── QualityGateRunner.ts     # 品質ゲート実行                          │
│  │   └── ApprovalManager.ts       # 承認管理                                │
│  │                                                                          │
│  ├── infrastructure/                                                        │
│  │   ├── WorkflowPersistence.ts   # ワークフロー永続化                      │
│  │   └── EventPublisher.ts        # イベント発行                            │
│  │                                                                          │
│  └── interface/                                                             │
│      ├── cli/                                                               │
│      │   └── workflow-commands.ts # CLIコマンド                             │
│      └── mcp/                                                               │
│          └── workflow-tools.ts    # MCPツール定義                           │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

#### DES-ORCH-001: PhaseController

**トレーサビリティ**: REQ-ORCH-001

```typescript
// packages/workflow-engine/src/application/PhaseController.ts

export type PhaseType = 
  | 'requirements'    // Phase 1
  | 'design'          // Phase 2
  | 'task-breakdown'  // Phase 3
  | 'implementation'  // Phase 4
  | 'completion';     // Phase 5

export interface PhaseTransition {
  from: PhaseType;
  to: PhaseType;
  conditions: TransitionCondition[];
}

export interface TransitionCondition {
  name: string;
  check: () => Promise<boolean>;
  errorMessage: string;
}

export interface IPhaseController {
  getCurrentPhase(): PhaseType;
  canTransition(to: PhaseType): Promise<TransitionResult>;
  transition(to: PhaseType, approval: Approval): Promise<void>;
  getValidTransitions(): PhaseType[];
}

// 有効な遷移のみを許可（Phase 2→4直接遷移は禁止）
const validTransitions: Map<PhaseType, PhaseType[]> = new Map([
  ['requirements', ['design']],
  ['design', ['task-breakdown']],        // Phase 2 → Phase 3 のみ
  ['task-breakdown', ['implementation']], // Phase 3 → Phase 4
  ['implementation', ['completion']],
  ['completion', []],
]);
```

#### DES-ORCH-002: StateTracker

**トレーサビリティ**: REQ-ORCH-002

```typescript
// packages/workflow-engine/src/application/StateTracker.ts

export type TaskStatus = 'not-started' | 'in-progress' | 'completed' | 'failed';

export interface TaskState {
  id: string;
  status: TaskStatus;
  progress: number;  // 0-100
  startedAt?: Date;
  completedAt?: Date;
  error?: string;
}

export interface IStateTracker {
  getState(taskId: string): TaskState | null;
  updateState(taskId: string, status: TaskStatus): void;
  getProgress(): WorkflowProgress;
  subscribe(listener: StateChangeListener): Unsubscribe;
}

export interface WorkflowProgress {
  totalTasks: number;
  completed: number;
  inProgress: number;
  failed: number;
  percentage: number;
}
```

#### DES-ORCH-003: QualityGateRunner

**トレーサビリティ**: REQ-ORCH-003

```typescript
// packages/workflow-engine/src/application/QualityGateRunner.ts

export interface QualityGate {
  id: string;
  phase: PhaseType;
  checks: QualityCheck[];
}

export interface QualityCheck {
  name: string;
  description: string;
  check: () => Promise<CheckResult>;
  required: boolean;  // 必須チェックか
}

export interface CheckResult {
  passed: boolean;
  message: string;
  details?: unknown;
}

export interface QualityGateResult {
  gate: QualityGate;
  results: Map<string, CheckResult>;
  passed: boolean;
  requiresApproval: boolean;
}

export interface IQualityGateRunner {
  run(phase: PhaseType): Promise<QualityGateResult>;
  getGatesForPhase(phase: PhaseType): QualityGate[];
}

// デフォルト品質ゲート
const defaultGates: Map<PhaseType, QualityGate> = new Map([
  ['requirements', {
    id: 'QG-REQ',
    phase: 'requirements',
    checks: [
      { name: 'ears-format', description: 'EARS形式準拠', check: checkEarsFormat, required: true },
      { name: 'traceability', description: 'ID付与完了', check: checkTraceability, required: true },
      { name: 'priority', description: '優先度設定完了', check: checkPriority, required: true },
    ],
  }],
  ['design', {
    id: 'QG-DES',
    phase: 'design',
    checks: [
      { name: 'c4-model', description: 'C4モデル完備', check: checkC4Model, required: true },
      { name: 'req-trace', description: '要件トレース完了', check: checkReqTrace, required: true },
      { name: 'solid', description: 'SOLID準拠', check: checkSolid, required: false },
    ],
  }],
  ['task-breakdown', {
    id: 'QG-TSK',
    phase: 'task-breakdown',
    checks: [
      { name: 'des-trace', description: '設計トレース完了', check: checkDesTrace, required: true },
      { name: 'size', description: 'タスクサイズ適切', check: checkTaskSize, required: true },
      { name: 'dependencies', description: '依存関係明確', check: checkDependencies, required: true },
    ],
  }],
]);
```

---

### 4.3 Skill Manager コンポーネント

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                       packages/skill-manager/                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  src/                                                                       │
│  ├── domain/                                                                │
│  │   ├── entities/                                                          │
│  │   │   └── Skill.ts             # スキルエンティティ                      │
│  │   └── value-objects/                                                     │
│  │       ├── SkillMetadata.ts     # メタデータ                              │
│  │       └── SkillStructure.ts    # 構造定義                                │
│  │                                                                          │
│  ├── application/                                                           │
│  │   ├── SkillRegistry.ts         # スキル登録管理                          │
│  │   ├── SkillLoader.ts           # スキル読み込み                          │
│  │   └── SkillValidator.ts        # スキル検証                              │
│  │                                                                          │
│  ├── infrastructure/                                                        │
│  │   └── FileSystemSkillStore.ts  # ファイルシステムストア                  │
│  │                                                                          │
│  └── interface/                                                             │
│      ├── cli/                                                               │
│      │   └── skill-commands.ts    # CLIコマンド                             │
│      └── mcp/                                                               │
│          └── skill-tools.ts       # MCPツール定義                           │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

#### DES-SKILL-001/002: Skill構造

**トレーサビリティ**: REQ-SKILL-001, REQ-SKILL-002

```typescript
// packages/skill-manager/src/domain/entities/Skill.ts

export interface Skill {
  id: string;
  name: string;
  version: string;
  metadata: SkillMetadata;
  structure: SkillStructure;
}

export interface SkillMetadata {
  description: string;
  author: string;
  tags: string[];
  dependencies: string[];
}

export interface SkillStructure {
  skillMd: SkillMdFile;          // SKILL.md (500行以下)
  readme?: string;               // README.md
  references: ReferenceFile[];   // references/
  examples: ExampleFile[];       // examples/
  scripts: ScriptFile[];         // scripts/
}

export interface SkillMdFile {
  content: string;
  lineCount: number;
  sections: SkillSection[];
}

export interface SkillSection {
  name: string;
  lineRange: [number, number];
  references?: string[];  // references/へのリンク
}

// スキル構造検証
export const validateSkillStructure = (skill: Skill): ValidationResult => {
  const errors: string[] = [];
  
  // REQ-SKILL-001: SKILL.md 500行以下
  if (skill.structure.skillMd.lineCount > 500) {
    errors.push(`SKILL.md exceeds 500 lines (${skill.structure.skillMd.lineCount})`);
  }
  
  // REQ-SKILL-002: 必須ディレクトリ
  if (skill.structure.references.length === 0) {
    errors.push('references/ directory is empty');
  }
  
  return {
    valid: errors.length === 0,
    errors,
  };
};
```

---

### 4.4 MCP Tools拡張

**トレーサビリティ**: REQ-MCP-001, REQ-MCP-002, REQ-MCP-003

```typescript
// packages/mcp-server/src/tools/agent-tools.ts

import type { ToolDefinition } from '../types.js';

/**
 * ツールアノテーション（REQ-MCP-002準拠）
 */
export interface ToolAnnotations {
  readOnlyHint: boolean;
  destructiveHint: boolean;
  idempotentHint: boolean;
  openWorldHint: boolean;
}

/**
 * エージェントツール定義
 */
export const agentAnalyzeComplexity: ToolDefinition = {
  name: 'agent_analyze_complexity',  // REQ-MCP-001準拠
  description: 'Analyze task complexity and recommend decomposition strategy',
  annotations: {
    readOnlyHint: true,
    destructiveHint: false,
    idempotentHint: true,
    openWorldHint: false,
  },
  inputSchema: {
    type: 'object',
    properties: {
      taskDescription: { type: 'string', description: 'Task description' },
      context: { type: 'object', description: 'Execution context' },
    },
    required: ['taskDescription'],
  },
  handler: async (args) => {
    // 実装
  },
};

export const agentDispatchSubagent: ToolDefinition = {
  name: 'agent_dispatch_subagent',
  description: 'Dispatch a subagent for a specific task',
  annotations: {
    readOnlyHint: false,
    destructiveHint: false,
    idempotentHint: false,
    openWorldHint: true,  // runSubagent呼び出し
  },
  inputSchema: {
    type: 'object',
    properties: {
      role: { type: 'string', enum: ['requirements', 'design', 'implementation', 'test', 'review'] },
      prompt: { type: 'string' },
      context: { type: 'object' },
    },
    required: ['role', 'prompt'],
  },
  handler: async (args) => {
    // 実装
  },
};
```

```typescript
// packages/mcp-server/src/tools/workflow-tools.ts

export const workflowGetStatus: ToolDefinition = {
  name: 'workflow_get_status',
  description: 'Get current workflow status and phase',
  annotations: {
    readOnlyHint: true,
    destructiveHint: false,
    idempotentHint: true,
    openWorldHint: false,
  },
  inputSchema: {
    type: 'object',
    properties: {
      workflowId: { type: 'string' },
    },
    required: ['workflowId'],
  },
  handler: async (args) => {
    // 実装
  },
};

export const workflowTransitionPhase: ToolDefinition = {
  name: 'workflow_transition_phase',
  description: 'Transition to next workflow phase (requires approval)',
  annotations: {
    readOnlyHint: false,
    destructiveHint: false,
    idempotentHint: false,
    openWorldHint: false,
  },
  inputSchema: {
    type: 'object',
    properties: {
      workflowId: { type: 'string' },
      targetPhase: { type: 'string', enum: ['requirements', 'design', 'task-breakdown', 'implementation', 'completion'] },
      approvalToken: { type: 'string' },
    },
    required: ['workflowId', 'targetPhase', 'approvalToken'],
  },
  handler: async (args) => {
    // 実装
  },
};

export const workflowRunQualityGate: ToolDefinition = {
  name: 'workflow_run_quality_gate',
  description: 'Run quality gate checks for current phase',
  annotations: {
    readOnlyHint: true,
    destructiveHint: false,
    idempotentHint: true,
    openWorldHint: false,
  },
  inputSchema: {
    type: 'object',
    properties: {
      workflowId: { type: 'string' },
      phase: { type: 'string' },
    },
    required: ['workflowId'],
  },
  handler: async (args) => {
    // 実装
  },
};
```

```typescript
// packages/mcp-server/src/tools/skill-tools.ts

export const skillLoad: ToolDefinition = {
  name: 'skill_load',
  description: 'Load a skill definition from .github/skills/',
  annotations: {
    readOnlyHint: true,
    destructiveHint: false,
    idempotentHint: true,
    openWorldHint: false,
  },
  inputSchema: {
    type: 'object',
    properties: {
      skillName: { type: 'string' },
    },
    required: ['skillName'],
  },
  handler: async (args) => {
    // 実装
  },
};

export const skillValidate: ToolDefinition = {
  name: 'skill_validate',
  description: 'Validate skill structure and content',
  annotations: {
    readOnlyHint: true,
    destructiveHint: false,
    idempotentHint: true,
    openWorldHint: false,
  },
  inputSchema: {
    type: 'object',
    properties: {
      skillPath: { type: 'string' },
    },
    required: ['skillPath'],
  },
  handler: async (args) => {
    // 実装
  },
};
```

---

## 5. 新規MCPツール一覧

### 5.1 Agent Tools（`agent_*`）

| ツール名 | 説明 | アノテーション |
|---------|------|---------------|
| `agent_analyze_complexity` | タスク複雑度分析 | readOnly, idempotent |
| `agent_dispatch_subagent` | サブエージェント実行 | openWorld |
| `agent_merge_context` | コンテキスト統合 | - |
| `agent_list_roles` | 利用可能ロール一覧 | readOnly, idempotent |

### 5.2 Workflow Tools（`workflow_*`）

| ツール名 | 説明 | アノテーション |
|---------|------|---------------|
| `workflow_get_status` | ワークフロー状態取得 | readOnly, idempotent |
| `workflow_transition_phase` | フェーズ遷移 | - |
| `workflow_run_quality_gate` | 品質ゲート実行 | readOnly, idempotent |
| `workflow_request_approval` | 承認リクエスト | - |

### 5.3 Skill Tools（`skill_*`）

| ツール名 | 説明 | アノテーション |
|---------|------|---------------|
| `skill_load` | スキル読み込み | readOnly, idempotent |
| `skill_validate` | スキル検証 | readOnly, idempotent |
| `skill_list` | スキル一覧 | readOnly, idempotent |

### 5.4 既存ツール（`sdd_*`）- 維持

| ツール名 | 変更 |
|---------|------|
| `sdd_create_requirements` | 変更なし（後方互換） |
| `sdd_validate_requirements` | 変更なし |
| `sdd_create_design` | 変更なし |
| `sdd_validate_design` | 変更なし |
| `sdd_create_tasks` | 変更なし |
| `sdd_query_knowledge` | 変更なし |
| `sdd_update_knowledge` | 変更なし |
| `sdd_validate_constitution` | 変更なし |
| `sdd_validate_traceability` | 変更なし |

---

## 6. シーケンス図

### 6.1 Subagent Dispatch フロー

```
┌────────┐     ┌──────────────────┐     ┌─────────────────┐     ┌──────────────┐
│  User  │     │ AgentOrchestrator│     │SubagentDispatcher│     │  runSubagent │
└────┬───┘     └────────┬─────────┘     └────────┬────────┘     └──────┬───────┘
     │                   │                        │                      │
     │  Complex Task     │                        │                      │
     │──────────────────►│                        │                      │
     │                   │                        │                      │
     │                   │  analyze complexity    │                      │
     │                   │────────────────────────│                      │
     │                   │                        │                      │
     │                   │  score >= 7            │                      │
     │                   │  decompose             │                      │
     │                   │───────────────────────►│                      │
     │                   │                        │                      │
     │                   │                        │  SubagentSpec[]      │
     │                   │                        │                      │
     │                   │                        │  dispatch (parallel) │
     │                   │                        │─────────────────────►│
     │                   │                        │                      │
     │                   │                        │◄─────────────────────│
     │                   │                        │  results[]           │
     │                   │                        │                      │
     │                   │◄───────────────────────│                      │
     │                   │  AggregatedResult      │                      │
     │                   │                        │                      │
     │◄──────────────────│                        │                      │
     │  Final Result     │                        │                      │
     │                   │                        │                      │
```

### 6.2 Phase Transition フロー

```
┌────────┐     ┌────────────────┐     ┌─────────────────┐     ┌──────────────┐
│  User  │     │ PhaseController│     │QualityGateRunner│     │ApprovalManager│
└────┬───┘     └───────┬────────┘     └────────┬────────┘     └──────┬───────┘
     │                  │                       │                      │
     │  Request Phase 2 │                       │                      │
     │─────────────────►│                       │                      │
     │                  │                       │                      │
     │                  │  run quality gate     │                      │
     │                  │──────────────────────►│                      │
     │                  │                       │                      │
     │                  │◄──────────────────────│                      │
     │                  │  QualityGateResult    │                      │
     │                  │                       │                      │
     │◄─────────────────│                       │                      │
     │  Show Review     │                       │                      │
     │                  │                       │                      │
     │  "承認" / "OK"   │                       │                      │
     │─────────────────►│                       │                      │
     │                  │                       │                      │
     │                  │  request approval     │                      │
     │                  │─────────────────────────────────────────────►│
     │                  │                       │                      │
     │                  │◄─────────────────────────────────────────────│
     │                  │  ApprovalToken        │                      │
     │                  │                       │                      │
     │                  │  transition()         │                      │
     │                  │──────────────────────────────────────────────│
     │                  │                       │                      │
     │◄─────────────────│                       │                      │
     │  Phase 2 Started │                       │                      │
     │                  │                       │                      │
```

---

## 7. パッケージ依存関係

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          Package Dependencies                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│                          ┌─────────────────┐                                │
│                          │   mcp-server    │                                │
│                          └────────┬────────┘                                │
│                                   │                                         │
│            ┌──────────────────────┼──────────────────────┐                  │
│            │                      │                      │                  │
│            ▼                      ▼                      ▼                  │
│  ┌─────────────────┐   ┌─────────────────┐   ┌─────────────────┐           │
│  │agent-orchestrator│   │ workflow-engine │   │  skill-manager  │◄─NEW     │
│  └────────┬────────┘   └────────┬────────┘   └────────┬────────┘           │
│           │                     │                     │                     │
│           └──────────────────┬──┴─────────────────────┘                     │
│                              │                                              │
│                              ▼                                              │
│                    ┌─────────────────┐                                      │
│                    │      core       │                                      │
│                    └────────┬────────┘                                      │
│                             │                                               │
│                             ▼                                               │
│                    ┌─────────────────┐                                      │
│                    │   yata-client   │                                      │
│                    └─────────────────┘                                      │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 依存関係表

| パッケージ | 依存先 | 種別 |
|-----------|--------|------|
| `mcp-server` | `agent-orchestrator`, `workflow-engine`, `skill-manager`, `core` | 直接 |
| `agent-orchestrator` | `core`, `yata-client` | 直接 |
| `workflow-engine` | `core`, `yata-client` | 直接 |
| `skill-manager` | `core` | 直接 |

---

## 8. 非機能要件対応

### DES-NFR-001: パフォーマンス

**トレーサビリティ**: REQ-NFR-001

| 指標 | 目標 | 実装方針 |
|------|------|---------|
| 複雑度分析 | < 200ms | キャッシュ活用 |
| サブエージェント起動 | < 500ms | 非同期起動 |
| フェーズ遷移 | < 1s | 品質ゲート並列実行 |

### DES-NFR-002: 後方互換性

**トレーサビリティ**: REQ-NFR-002

| 対象 | 方針 |
|------|------|
| 既存`sdd_*`ツール | 変更なし、維持 |
| CLIコマンド | 既存コマンド維持、新規追加 |
| 設定ファイル | 既存形式維持、新設定は追加 |

---

## 9. 次ステップ

この設計書が承認されたら、Phase 3（タスク分解）に進み、以下のタスクを生成します：

1. **TSK-AGENT-***: Agent Orchestratorパッケージ実装タスク
2. **TSK-WORKFLOW-***: Workflow Engineパッケージ実装タスク
3. **TSK-SKILL-***: Skill Managerパッケージ実装タスク
4. **TSK-MCP-***: MCPツール追加タスク
5. **TSK-TEST-***: テスト実装タスク

---

**Document ID**: DES-ENHANCEMENT-v2.4.0  
**Created**: 2026-01-11  
**Author**: AI Agent (GitHub Copilot)  
**Status**: Draft - Awaiting Review
