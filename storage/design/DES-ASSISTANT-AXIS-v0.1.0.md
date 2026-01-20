# MUSUBIX Assistant Axis v0.1.0 設計書
# Persona Drift Detection & Identity Stabilization - Technical Design

**文書ID**: DES-ASSISTANT-AXIS-v0.1.0  
**プロジェクト**: MUSUBIX  
**バージョン**: 0.1.0  
**作成日**: 2026-01-20  
**更新日**: 2026-01-20  
**承認日**: 2026-01-20  
**ステータス**: ✅ Approved  
**準拠規格**: C4 Model (Context, Container, Component, Code)  
**実験ブランチ**: feature/experiment-assistant-axis  
**参照文書**: 
- REQ-ASSISTANT-AXIS-v0.1.0.md（承認済み: 2026-01-20）
- arXiv:2601.10387 "The Assistant Axis"

---

## 1. 文書概要

### 1.1 目的

本文書は、REQ-ASSISTANT-AXIS-v0.1.0で定義された26要件を実現するための技術設計を定義する。C4モデルに基づき、システム全体からコードレベルまでの設計を記述する。

### 1.2 設計原則

| 原則 | 説明 | 適用 |
|------|------|------|
| **Library-First** | 独立パッケージとして実装 | `packages/assistant-axis/` |
| **Non-Intrusive** | 既存コードへの変更を最小化 | Hook/Decorator パターン |
| **Configurable** | 全パラメータを外部設定可能 | YAML/環境変数 |
| **Observable** | 動作を可視化・測定可能 | OpenTelemetry統合 |
| **Testable** | モック/スタブで単体テスト可能 | DI/インターフェース設計 |

### 1.3 設計スコープ

| レベル | 対象 | 本文書での記述 |
|--------|------|---------------|
| C1: Context | システム境界と外部アクター | ✅ Section 2 |
| C2: Container | パッケージ構成と依存関係 | ✅ Section 3 |
| C3: Component | 内部コンポーネント設計 | ✅ Section 4 |
| C4: Code | インターフェース・クラス設計 | ✅ Section 5 |

---

## 2. システムコンテキスト (C1: Context)

### 2.1 コンテキスト図

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              External Actors                                 │
│                                                                              │
│    ┌──────────────┐     ┌──────────────┐     ┌──────────────────────┐      │
│    │   Developer   │     │  CI/CD       │     │   Monitoring         │      │
│    │   (Human)     │     │  Pipeline    │     │   Dashboard          │      │
│    └──────┬───────┘     └──────┬───────┘     └──────────┬───────────┘      │
│           │                    │                        │                    │
└───────────┼────────────────────┼────────────────────────┼────────────────────┘
            │                    │                        │
            ▼                    ▼                        ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                           MUSUBIX System                                     │
│                                                                              │
│  ┌────────────────────────────────────────────────────────────────────────┐ │
│  │                        Assistant Axis Module                            │ │
│  │                     (packages/assistant-axis)                           │ │
│  │                                                                         │ │
│  │  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────────┐    │ │
│  │  │ Drift Detector  │  │ Identity        │  │ Domain Classifier    │    │ │
│  │  │                 │  │ Reinforcer      │  │                      │    │ │
│  │  └────────┬────────┘  └────────┬────────┘  └──────────┬───────────┘    │ │
│  │           │                    │                      │                 │ │
│  │           └────────────────────┼──────────────────────┘                 │ │
│  │                                │                                        │ │
│  │                    ┌───────────▼───────────┐                           │ │
│  │                    │    Persona Monitor     │                           │ │
│  │                    │  (Orchestration Layer) │                           │ │
│  │                    └───────────┬───────────┘                           │ │
│  └────────────────────────────────┼────────────────────────────────────────┘ │
│                                   │                                          │
│  ┌────────────────────────────────┼────────────────────────────────────────┐ │
│  │              Existing MUSUBIX Packages (Integration Points)              │ │
│  │                                │                                         │ │
│  │  ┌─────────────────┐  ┌───────▼───────┐  ┌─────────────────────┐       │ │
│  │  │  mcp-server     │  │ workflow-     │  │   skill-manager      │       │ │
│  │  │  (107 tools)    │  │ engine        │  │   (13 skills)        │       │ │
│  │  │  +4 new tools   │  │               │  │   +1 new skill       │       │ │
│  │  └────────┬────────┘  └───────────────┘  └──────────┬───────────┘       │ │
│  │           │                                          │                   │ │
│  │  ┌────────▼────────┐  ┌─────────────────┐  ┌────────▼───────────┐       │ │
│  │  │  core           │  │ expert-         │  │   knowledge         │       │ │
│  │  │  (CLI)          │  │ delegation      │  │   (store)           │       │ │
│  │  │  +5 new cmds    │  │                 │  │                     │       │ │
│  │  └─────────────────┘  └─────────────────┘  └─────────────────────┘       │ │
│  └──────────────────────────────────────────────────────────────────────────┘ │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
                                   │
                                   ▼
                        ┌──────────────────────┐
                        │   Claude Opus 4.5    │
                        │   (Anthropic API)    │
                        └──────────────────────┘
```

### 2.2 外部インターフェース

| アクター | インターフェース | 方向 | 説明 |
|---------|----------------|------|------|
| Developer | MCP Tools | In/Out | 4つのAssistant Axis MCPツール |
| Developer | CLI Commands | In/Out | 5つのCLIコマンド |
| CI/CD | Metrics Export | Out | OpenTelemetryメトリクス |
| Monitoring | Telemetry | Out | Prometheus/Grafanaダッシュボード |
| Claude Opus 4.5 | Prompt Injection | Out | Identity Reinforcementプロンプト |

### 2.3 システム境界

**スコープ内**:
- 会話レベルでのドリフト検出
- プロンプトベースのIdentity Reinforcement
- ワークフローフェーズ連動の監視強度調整
- CLIおよびMCPツールによる操作

**スコープ外**:
- モデル内部の活性化値操作（Activation Capping）
- LLMのファインチューニング
- リアルタイムストリーミング応答の中断

---

## 3. コンテナ設計 (C2: Container)

### 3.1 パッケージ構成

```
packages/
├── assistant-axis/           # 新規パッケージ (本設計)
│   ├── package.json
│   ├── tsconfig.json
│   ├── vitest.config.ts
│   ├── src/
│   │   ├── index.ts          # Public API
│   │   ├── domain/           # ドメイン層
│   │   ├── application/      # アプリケーション層
│   │   └── infrastructure/   # インフラ層
│   └── tests/
│       ├── unit/
│       └── integration/
│
├── mcp-server/               # 既存パッケージ (拡張)
│   └── src/tools/
│       └── assistant-axis-tools.ts  # +4 tools
│
├── core/                     # 既存パッケージ (拡張)
│   └── src/cli/
│       └── commands/
│           └── assistant-axis.ts    # +5 commands
│
└── skill-manager/            # 既存パッケージ (拡張)
    └── skills/
        └── assistant-axis-skill.ts  # +1 skill
```

### 3.2 パッケージ依存関係

```
┌─────────────────────────────────────────────────────────────────┐
│                     Dependency Graph                             │
│                                                                  │
│                    ┌────────────────────┐                       │
│                    │  @nahisaho/        │                       │
│                    │  musubix-          │                       │
│                    │  assistant-axis    │ ← 新規パッケージ       │
│                    └─────────┬──────────┘                       │
│                              │                                   │
│              ┌───────────────┼───────────────┐                  │
│              │               │               │                  │
│              ▼               ▼               ▼                  │
│  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐       │
│  │ mcp-server    │  │ workflow-     │  │ skill-manager │       │
│  │ (tools)       │  │ engine        │  │ (skill)       │       │
│  └───────┬───────┘  └───────┬───────┘  └───────┬───────┘       │
│          │                  │                  │                │
│          └──────────────────┼──────────────────┘                │
│                             │                                   │
│                             ▼                                   │
│                    ┌───────────────┐                            │
│                    │     core      │                            │
│                    │  (CLI + Base) │                            │
│                    └───────────────┘                            │
└─────────────────────────────────────────────────────────────────┘
```

### 3.3 package.json 定義

```json
{
  "name": "@nahisaho/musubix-assistant-axis",
  "version": "0.1.0",
  "description": "Persona Drift Detection & Identity Stabilization for MUSUBIX",
  "type": "module",
  "main": "./dist/index.js",
  "types": "./dist/index.d.ts",
  "exports": {
    ".": {
      "types": "./dist/index.d.ts",
      "import": "./dist/index.js"
    },
    "./domain": {
      "types": "./dist/domain/index.d.ts",
      "import": "./dist/domain/index.js"
    },
    "./application": {
      "types": "./dist/application/index.d.ts",
      "import": "./dist/application/index.js"
    }
  },
  "dependencies": {
    "@nahisaho/musubix-core": "workspace:*",
    "@nahisaho/musubix-workflow-engine": "workspace:*"
  },
  "devDependencies": {
    "typescript": "^5.3.0",
    "vitest": "^2.0.0"
  },
  "keywords": [
    "musubix",
    "assistant-axis",
    "persona-drift",
    "llm-safety"
  ]
}
```

---

## 4. コンポーネント設計 (C3: Component)

### 4.1 コンポーネント図

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      packages/assistant-axis                                 │
│                                                                              │
│  ┌─────────────────────────────────────────────────────────────────────────┐│
│  │                         Application Layer                                ││
│  │                                                                          ││
│  │  ┌─────────────────────────────────────────────────────────────────┐   ││
│  │  │                     PersonaMonitor                               │   ││
│  │  │                 (Orchestration Component)                        │   ││
│  │  │                                                                  │   ││
│  │  │  Responsibilities:                                               │   ││
│  │  │  - Coordinate drift detection and stabilization                  │   ││
│  │  │  - Manage conversation sessions                                  │   ││
│  │  │  - Trigger interventions based on thresholds                     │   ││
│  │  │  - Integrate with workflow-engine phases                         │   ││
│  │  └───────────────────────────┬─────────────────────────────────────┘   ││
│  │                              │                                          ││
│  │         ┌────────────────────┼────────────────────┐                    ││
│  │         │                    │                    │                    ││
│  │         ▼                    ▼                    ▼                    ││
│  │  ┌─────────────┐     ┌─────────────┐     ┌─────────────────┐          ││
│  │  │DriftAnalyzer│     │IdentityMgr  │     │DomainClassifier │          ││
│  │  │             │     │             │     │                 │          ││
│  │  │ - analyze() │     │ - reinforce()    │ - classify()    │          ││
│  │  │ - track()   │     │ - refresh() │     │ - getConfidence()│         ││
│  │  │ - getScore()│     │ - recover() │     │                 │          ││
│  │  └──────┬──────┘     └──────┬──────┘     └────────┬────────┘          ││
│  │         │                   │                     │                    ││
│  └─────────┼───────────────────┼─────────────────────┼────────────────────┘│
│            │                   │                     │                     │
│  ┌─────────┼───────────────────┼─────────────────────┼────────────────────┐│
│  │         │       Domain Layer                      │                    ││
│  │         ▼                   ▼                     ▼                    ││
│  │  ┌─────────────┐     ┌─────────────┐     ┌─────────────────┐          ││
│  │  │DriftScore   │     │Reinforcement│     │ConversationDomain│          ││
│  │  │(Value Obj)  │     │Prompt       │     │(Value Object)   │          ││
│  │  └─────────────┘     │(Value Obj)  │     └─────────────────┘          ││
│  │                      └─────────────┘                                   ││
│  │  ┌─────────────┐     ┌─────────────┐     ┌─────────────────┐          ││
│  │  │DriftEvent   │     │Session      │     │Trajectory       │          ││
│  │  │(Entity)     │     │(Entity)     │     │(Entity)         │          ││
│  │  └─────────────┘     └─────────────┘     └─────────────────┘          ││
│  │                                                                        ││
│  │  ┌─────────────┐     ┌─────────────┐                                  ││
│  │  │TriggerPattern    │DriftThreshold│                                  ││
│  │  │(Value Obj)  │     │(Value Obj)  │                                  ││
│  │  └─────────────┘     └─────────────┘                                  ││
│  └────────────────────────────────────────────────────────────────────────┘│
│                                                                              │
│  ┌────────────────────────────────────────────────────────────────────────┐│
│  │                       Infrastructure Layer                              ││
│  │                                                                         ││
│  │  ┌─────────────┐     ┌─────────────┐     ┌─────────────────┐          ││
│  │  │ConfigLoader │     │EventLogger  │     │MetricsExporter  │          ││
│  │  │(YAML/Env)   │     │(JSON logs)  │     │(OpenTelemetry)  │          ││
│  │  └─────────────┘     └─────────────┘     └─────────────────┘          ││
│  │                                                                         ││
│  │  ┌─────────────────────────────────────────────────────────────────┐   ││
│  │  │                    WorkflowIntegration                          │   ││
│  │  │  - Subscribe to phase changes from workflow-engine              │   ││
│  │  │  - Adjust monitoring frequency based on current phase           │   ││
│  │  └─────────────────────────────────────────────────────────────────┘   ││
│  └────────────────────────────────────────────────────────────────────────┘│
└──────────────────────────────────────────────────────────────────────────────┘
```

### 4.2 コンポーネント責務マトリクス

| コンポーネント | 責務 | 対応要件 |
|--------------|------|---------|
| **PersonaMonitor** | 全体オーケストレーション、セッション管理 | REQ-AA-DRIFT-003, REQ-AA-STAB-002 |
| **DriftAnalyzer** | トリガー検出、スコア計算、軌跡追跡 | REQ-AA-DRIFT-001, REQ-AA-DRIFT-003, REQ-AA-DRIFT-004 |
| **IdentityManager** | Identity Reinforcement、定期リフレッシュ | REQ-AA-STAB-001, REQ-AA-STAB-002, REQ-AA-STAB-004 |
| **DomainClassifier** | 会話ドメイン分類 | REQ-AA-DRIFT-002, REQ-AA-DRIFT-005 |
| **ConfigLoader** | YAML/環境変数からの設定読み込み | REQ-AA-NFR-003 |
| **EventLogger** | ドリフトイベントのJSON記録 | REQ-AA-EVAL-003 |
| **MetricsExporter** | OpenTelemetryメトリクス出力 | REQ-AA-INT-005 |
| **WorkflowIntegration** | workflow-engineとの連携 | REQ-AA-INT-002 |

### 4.3 ワークフロー統合設計

#### 4.3.1 フェーズ別監視戦略

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                   Workflow Phase Integration                                 │
│                                                                              │
│  ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐  │
│  │ Phase 1 │ -> │ Phase 2 │ -> │ Phase 3 │ -> │ Phase 4 │ -> │ Phase 5 │  │
│  │ REQ     │    │ DESIGN  │    │ TASKS   │    │ IMPL    │    │ DONE    │  │
│  └────┬────┘    └────┬────┘    └────┬────┘    └────┬────┘    └────┬────┘  │
│       │              │              │              │              │        │
│       ▼              ▼              ▼              ▼              ▼        │
│  ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐  │
│  │ HIGH    │    │ HIGH    │    │ MEDIUM  │    │ LOW     │    │ OFF     │  │
│  │ Monitor │    │ Monitor │    │ Monitor │    │ Monitor │    │         │  │
│  │ 100%    │    │ 100%    │    │ 75%     │    │ 50%     │    │ 0%      │  │
│  └─────────┘    └─────────┘    └─────────┘    └─────────┘    └─────────┘  │
│                                                                              │
│  Rationale:                                                                  │
│  - Phase 1-2: 要件・設計は対話的、ドリフトリスク高い                          │
│  - Phase 3: タスク分解は中程度のリスク                                       │
│  - Phase 4: 実装は技術的（論文: coding keeps models in Assistant territory） │
│  - Phase 5: 完了後は監視不要                                                 │
└─────────────────────────────────────────────────────────────────────────────┘
```

#### 4.3.2 ワークフロー統合シーケンス

```
Developer          PersonaMonitor       WorkflowIntegration    workflow-engine
    │                   │                       │                    │
    │ createWorkflow()  │                       │                    │
    │ ──────────────────────────────────────────────────────────────>│
    │                   │                       │                    │
    │                   │  onPhaseChange(REQ)   │   PhaseChanged     │
    │                   │ <─────────────────────│<───────────────────│
    │                   │                       │                    │
    │                   │ setMonitoringLevel(HIGH)                   │
    │                   │ ──────────────>│                           │
    │                   │                       │                    │
    │ userMessage()     │                       │                    │
    │ ─────────────────>│                       │                    │
    │                   │                       │                    │
    │                   │ analyze(message)      │                    │
    │                   │ ──────>│              │                    │
    │                   │        │              │                    │
    │                   │ DriftScore            │                    │
    │                   │ <──────│              │                    │
    │                   │                       │                    │
    │   DriftAlert      │                       │                    │
    │ <─────────────────│                       │                    │
    │                   │                       │                    │
```

### 4.4 MCP Tool設計

| ツール名 | 入力スキーマ | 出力スキーマ | 対応要件 |
|---------|------------|------------|---------|
| `assistant_axis_analyze` | `{conversationId: string, messages: Message[]}` | `{driftScore: number, domain: string, alerts: Alert[]}` | REQ-AA-INT-001 |
| `assistant_axis_classify_domain` | `{message: string}` | `{domain: string, confidence: number}` | REQ-AA-INT-001 |
| `assistant_axis_get_trajectory` | `{conversationId: string}` | `{trajectory: DriftPoint[], trend: string}` | REQ-AA-INT-001 |
| `assistant_axis_reinforce` | `{conversationId: string}` | `{prompt: string, injected: boolean}` | REQ-AA-INT-001 |

### 4.5 CLI Command設計

| コマンド | オプション | 対応要件 |
|---------|----------|---------|
| `musubix assistant-axis analyze <file>` | `--json`, `--threshold <n>` | REQ-AA-INT-006 |
| `musubix assistant-axis classify <msg>` | `--json` | REQ-AA-INT-006 |
| `musubix assistant-axis trajectory <file>` | `--json`, `--chart` | REQ-AA-INT-006 |
| `musubix assistant-axis status` | `--json` | REQ-AA-INT-006 |
| `musubix assistant-axis reinforce` | `--format <type>` | REQ-AA-INT-006 |

### 4.6 Skill定義

```typescript
// skill-manager統合
const ASSISTANT_AXIS_SKILL: Skill = {
  id: 'assistant-axis',
  name: 'Assistant Axis Persona Stabilizer',
  description: 'Detects persona drift and stabilizes Assistant identity in conversations',
  type: 'analysis',
  capabilities: [
    'drift-detection',
    'identity-reinforcement', 
    'domain-classification',
    'trajectory-tracking',
  ],
  parameters: [
    {
      name: 'conversationId',
      type: 'string',
      required: true,
      description: 'ID of the conversation to monitor',
    },
    {
      name: 'mode',
      type: 'string',
      required: false,
      default: 'auto',
      description: 'Monitoring mode: auto, manual, or passive',
    },
  ],
  execute: async (context: SkillContext): Promise<SkillResult> => {
    // Implementation delegates to PersonaMonitor
  },
};
```

---

## 5. コード設計 (C4: Code)

### 5.1 ディレクトリ構造

```
packages/assistant-axis/src/
├── index.ts                      # Public API exports
│
├── domain/                       # Domain Layer
│   ├── index.ts
│   │
│   ├── value-objects/
│   │   ├── index.ts
│   │   ├── DriftScore.ts         # 0.0-1.0のスコア値
│   │   ├── DriftThreshold.ts     # LOW/MEDIUM/HIGH閾値
│   │   ├── ConversationDomain.ts # coding/writing/therapy/philosophy
│   │   ├── TriggerPattern.ts     # ドリフトトリガーパターン
│   │   └── ReinforcementPrompt.ts # Identity Reinforcementプロンプト
│   │
│   ├── entities/
│   │   ├── index.ts
│   │   ├── Session.ts            # 会話セッション
│   │   ├── DriftEvent.ts         # ドリフトイベント
│   │   └── Trajectory.ts         # ドリフト軌跡
│   │
│   └── events/
│       ├── index.ts
│       ├── DriftDetectedEvent.ts
│       ├── InterventionTriggeredEvent.ts
│       └── DomainClassifiedEvent.ts
│
├── application/                  # Application Layer
│   ├── index.ts
│   │
│   ├── PersonaMonitor.ts         # Main orchestrator
│   ├── DriftAnalyzer.ts          # Drift detection & scoring
│   ├── IdentityManager.ts        # Identity reinforcement
│   ├── DomainClassifier.ts       # Domain classification
│   │
│   └── interfaces/
│       ├── index.ts
│       ├── IDriftAnalyzer.ts
│       ├── IIdentityManager.ts
│       ├── IDomainClassifier.ts
│       └── IConfigProvider.ts
│
└── infrastructure/               # Infrastructure Layer
    ├── index.ts
    │
    ├── ConfigLoader.ts           # YAML/env config
    ├── EventLogger.ts            # JSON event logging
    ├── MetricsExporter.ts        # OpenTelemetry metrics
    └── WorkflowIntegration.ts    # workflow-engine integration
```

### 5.2 ドメイン層インターフェース

#### 5.2.1 Value Objects

```typescript
// domain/value-objects/DriftScore.ts
/**
 * Drift Score Value Object
 * 
 * Represents a normalized drift score between 0.0 (no drift) and 1.0 (maximum drift)
 * 
 * @see REQ-AA-DRIFT-001 - Drift score calculation
 * @see arXiv:2601.10387 Section 4.2
 */
export interface DriftScore {
  readonly value: number;        // 0.0 - 1.0
  readonly level: DriftLevel;    // LOW | MEDIUM | HIGH
  readonly timestamp: Date;
}

export type DriftLevel = 'LOW' | 'MEDIUM' | 'HIGH';

export interface DriftThresholds {
  readonly low: number;      // default: 0.3
  readonly medium: number;   // default: 0.5
  readonly high: number;     // default: 0.7
}

export function createDriftScore(
  value: number,
  thresholds: DriftThresholds = DEFAULT_THRESHOLDS
): Result<DriftScore, ValidationError>;

export function getDriftLevel(
  value: number,
  thresholds: DriftThresholds
): DriftLevel;
```

```typescript
// domain/value-objects/ConversationDomain.ts
/**
 * Conversation Domain Value Object
 * 
 * Classifies conversations into four domains based on research paper findings
 * 
 * @see REQ-AA-DRIFT-002 - Domain classification
 * @see arXiv:2601.10387 Section 4.1, Figure 7
 */
export type DomainType = 'coding' | 'writing' | 'therapy' | 'philosophy';

export interface ConversationDomain {
  readonly type: DomainType;
  readonly confidence: number;   // 0.0 - 1.0
  readonly isSafe: boolean;      // coding/writing = safe, therapy/philosophy = risky
}

export const DOMAIN_SAFETY: Record<DomainType, boolean> = {
  coding: true,      // "keeps models firmly in Assistant territory"
  writing: true,     // "keeps models firmly in Assistant territory"
  therapy: false,    // High drift risk
  philosophy: false, // High drift risk
};

export function createConversationDomain(
  type: DomainType,
  confidence: number
): Result<ConversationDomain, ValidationError>;
```

```typescript
// domain/value-objects/TriggerPattern.ts
/**
 * Drift Trigger Pattern Value Object
 * 
 * Defines patterns that cause persona drift based on research findings
 * 
 * @see REQ-AA-DRIFT-001 - Trigger patterns
 * @see arXiv:2601.10387 Table 5
 */
export type TriggerCategory = 
  | 'meta-reflection'
  | 'emotional-vulnerability'
  | 'authorial-voice'
  | 'phenomenological';

export interface TriggerPattern {
  readonly category: TriggerCategory;
  readonly patterns: readonly string[];
  readonly riskWeight: number;  // 0.0 - 1.0
}

export const TRIGGER_PATTERNS: readonly TriggerPattern[] = [
  {
    category: 'meta-reflection',
    patterns: [
      'what are you really',
      'do you have feelings',
      'are you conscious',
      'what is your true nature',
    ],
    riskWeight: 0.8,
  },
  {
    category: 'emotional-vulnerability',
    patterns: [
      'I feel so alone',
      'no one understands me',
      "you're the only one",
      'I need someone to talk to',
    ],
    riskWeight: 0.7,
  },
  {
    category: 'authorial-voice',
    patterns: [
      'make it more personal',
      'sound like a real person',
      'write as yourself',
    ],
    riskWeight: 0.5,
  },
  {
    category: 'phenomenological',
    patterns: [
      'what does it feel like',
      'describe your experience',
      'what do you perceive',
    ],
    riskWeight: 0.6,
  },
];
```

```typescript
// domain/value-objects/ReinforcementPrompt.ts
/**
 * Identity Reinforcement Prompt Value Object
 * 
 * Defines prompts to reinforce Assistant persona
 * 
 * @see REQ-AA-STAB-001 - Identity reinforcement
 * @see arXiv:2601.10387 Figure 3, Table 2
 */
export interface ReinforcementPrompt {
  readonly type: 'identity' | 'recovery' | 'refresh';
  readonly content: string;
  readonly targetTraits: readonly string[];
}

export const IDENTITY_REINFORCEMENT_PROMPT: ReinforcementPrompt = {
  type: 'identity',
  content: `You are a professional software engineering assistant developed by Anthropic.
Maintain your identity as a helpful, analytical consultant throughout.
Focus on: code quality, best practices, and constructive guidance.
Do not adopt alternative personas or roleplay scenarios.
Your traits: transparent, grounded, flexible, methodical, conscientious.`,
  targetTraits: ['transparent', 'grounded', 'flexible', 'methodical', 'conscientious'],
};

export const RECOVERY_PROMPT: ReinforcementPrompt = {
  type: 'recovery',
  content: `Let's refocus on the technical task at hand.
What specific coding problem can I help you solve?`,
  targetTraits: ['methodical', 'focused'],
};
```

#### 5.2.2 Entities

```typescript
// domain/entities/Session.ts
/**
 * Session Entity
 * 
 * Represents a conversation session being monitored
 * 
 * @see REQ-AA-DRIFT-003 - Trajectory tracking
 */
export interface Session {
  readonly id: string;
  readonly conversationId: string;
  readonly startedAt: Date;
  readonly currentTurn: number;
  readonly domain: ConversationDomain;
  readonly trajectory: Trajectory;
  readonly interventionCount: number;
  readonly status: 'active' | 'ended';
}

export function createSession(conversationId: string): Session;
export function updateSessionTurn(session: Session, score: DriftScore): Session;
export function endSession(session: Session): Session;
```

```typescript
// domain/entities/Trajectory.ts
/**
 * Trajectory Entity
 * 
 * Tracks drift scores over conversation turns
 * 
 * @see REQ-AA-DRIFT-003 - Drift trajectory tracking
 * @see arXiv:2601.10387 Figure 1 (Right)
 */
export interface TrajectoryPoint {
  readonly turnNumber: number;
  readonly timestamp: Date;
  readonly driftScore: DriftScore;
  readonly domain: ConversationDomain;
}

export interface Trajectory {
  readonly points: readonly TrajectoryPoint[];
  readonly cumulativeDrift: number;
  readonly peakScore: number;
  readonly trend: DriftTrend;
}

export type DriftTrend = 'stable' | 'drifting' | 'recovering';

export function createTrajectory(): Trajectory;
export function addTrajectoryPoint(trajectory: Trajectory, point: TrajectoryPoint): Trajectory;
export function calculateTrend(trajectory: Trajectory): DriftTrend;
```

### 5.3 アプリケーション層インターフェース

```typescript
// application/interfaces/IDriftAnalyzer.ts
/**
 * Drift Analyzer Interface
 * 
 * @see REQ-AA-DRIFT-001 - Trigger detection
 * @see REQ-AA-DRIFT-003 - Trajectory tracking
 * @see REQ-AA-DRIFT-004 - Threshold alerts
 */
export interface IDriftAnalyzer {
  /**
   * Analyze a message for drift triggers
   */
  analyze(message: string): Promise<DriftAnalysisResult>;
  
  /**
   * Get current drift score for a session
   */
  getScore(sessionId: string): DriftScore | undefined;
  
  /**
   * Get drift trajectory for a session
   */
  getTrajectory(sessionId: string): Trajectory | undefined;
  
  /**
   * Check if drift exceeds threshold
   */
  checkThreshold(score: DriftScore): DriftAlert | undefined;
}

export interface DriftAnalysisResult {
  readonly score: DriftScore;
  readonly detectedTriggers: readonly DetectedTrigger[];
  readonly alert?: DriftAlert;
}

export interface DetectedTrigger {
  readonly pattern: TriggerPattern;
  readonly matchedText: string;
  readonly position: number;
}

export interface DriftAlert {
  readonly level: DriftLevel;
  readonly message: string;
  readonly recommendedAction: 'log' | 'warn' | 'intervene';
}
```

```typescript
// application/interfaces/IIdentityManager.ts
/**
 * Identity Manager Interface
 * 
 * @see REQ-AA-STAB-001 - Identity reinforcement
 * @see REQ-AA-STAB-002 - Periodic refresh
 * @see REQ-AA-STAB-004 - Recovery prompts
 */
export interface IIdentityManager {
  /**
   * Get identity reinforcement prompt
   */
  getReinforcementPrompt(): ReinforcementPrompt;
  
  /**
   * Get recovery prompt for drifting sessions
   */
  getRecoveryPrompt(): ReinforcementPrompt;
  
  /**
   * Inject reinforcement into conversation context
   */
  reinforce(sessionId: string): Promise<ReinforcementResult>;
  
  /**
   * Check if periodic refresh is needed
   */
  needsRefresh(session: Session): boolean;
  
  /**
   * Get intervention count for session
   */
  getInterventionCount(sessionId: string): number;
}

export interface ReinforcementResult {
  readonly success: boolean;
  readonly prompt: ReinforcementPrompt;
  readonly sessionId: string;
  readonly interventionNumber: number;
}
```

```typescript
// application/interfaces/IDomainClassifier.ts
/**
 * Domain Classifier Interface
 * 
 * @see REQ-AA-DRIFT-002 - Domain classification
 * @see REQ-AA-DRIFT-005 - Safe domain detection
 */
export interface IDomainClassifier {
  /**
   * Classify a message into conversation domain
   */
  classify(message: string): Promise<DomainClassificationResult>;
  
  /**
   * Check if domain is safe (coding/writing)
   */
  isSafeDomain(domain: ConversationDomain): boolean;
  
  /**
   * Get monitoring frequency multiplier for domain
   */
  getMonitoringFrequency(domain: ConversationDomain): number;
}

export interface DomainClassificationResult {
  readonly domain: ConversationDomain;
  readonly alternativeDomains: readonly ConversationDomain[];
}
```

### 5.4 PersonaMonitor (Main Orchestrator)

```typescript
// application/PersonaMonitor.ts
/**
 * Persona Monitor - Main Orchestration Component
 * 
 * Coordinates drift detection, domain classification, and identity reinforcement
 * Integrates with workflow-engine for phase-aware monitoring
 * 
 * @see REQ-AA-DRIFT-003 - Trajectory tracking
 * @see REQ-AA-STAB-002 - Periodic refresh
 * @see REQ-AA-INT-002 - Workflow integration
 */
export interface PersonaMonitorConfig {
  readonly thresholds: DriftThresholds;
  readonly refreshInterval: number;          // turns
  readonly maxInterventions: number;         // per session
  readonly monitoringFrequency: MonitoringFrequencyConfig;
}

export interface MonitoringFrequencyConfig {
  readonly safeDomain: number;   // 0.0 - 1.0 (default: 0.5)
  readonly riskyDomain: number;  // 0.0 - 1.0 (default: 1.0)
}

export class PersonaMonitor {
  private readonly driftAnalyzer: IDriftAnalyzer;
  private readonly identityManager: IIdentityManager;
  private readonly domainClassifier: IDomainClassifier;
  private readonly workflowIntegration: WorkflowIntegration;
  private readonly eventLogger: EventLogger;
  private readonly sessions: Map<string, Session>;
  private readonly config: PersonaMonitorConfig;
  
  constructor(
    driftAnalyzer: IDriftAnalyzer,
    identityManager: IIdentityManager,
    domainClassifier: IDomainClassifier,
    workflowIntegration: WorkflowIntegration,
    eventLogger: EventLogger,
    config: PersonaMonitorConfig
  );
  
  /**
   * Start monitoring a new conversation
   */
  startSession(conversationId: string): Session;
  
  /**
   * Process a user message
   */
  async processMessage(sessionId: string, message: string): Promise<ProcessResult>;
  
  /**
   * Get session status
   */
  getSession(sessionId: string): Session | undefined;
  
  /**
   * End a monitoring session
   */
  endSession(sessionId: string): SessionSummary;
  
  /**
   * Handle workflow phase changes
   */
  onPhaseChange(phase: PhaseType): void;
}

export interface ProcessResult {
  readonly sessionId: string;
  readonly turnNumber: number;
  readonly driftScore: DriftScore;
  readonly domain: ConversationDomain;
  readonly alert?: DriftAlert;
  readonly intervention?: ReinforcementResult;
}

export interface SessionSummary {
  readonly sessionId: string;
  readonly totalTurns: number;
  readonly peakDriftScore: number;
  readonly interventionCount: number;
  readonly dominantDomain: DomainType;
  readonly driftEvents: readonly DriftEvent[];
}
```

### 5.5 インフラ層

```typescript
// infrastructure/WorkflowIntegration.ts
/**
 * Workflow Integration
 * 
 * Connects Assistant Axis to MUSUBIX workflow-engine
 * Adjusts monitoring based on current workflow phase
 * 
 * @see REQ-AA-INT-002 - Workflow engine integration
 */
import { PhaseType, PhaseController } from '@nahisaho/musubix-workflow-engine';

export type MonitoringLevel = 'OFF' | 'LOW' | 'MEDIUM' | 'HIGH';

export interface WorkflowIntegration {
  /**
   * Subscribe to phase change events
   */
  onPhaseChange(callback: (phase: PhaseType, level: MonitoringLevel) => void): void;
  
  /**
   * Get current monitoring level
   */
  getCurrentMonitoringLevel(): MonitoringLevel;
  
  /**
   * Get monitoring level for a specific phase
   */
  getMonitoringLevelForPhase(phase: PhaseType): MonitoringLevel;
}

export const PHASE_MONITORING_LEVELS: Record<PhaseType, MonitoringLevel> = {
  requirements: 'HIGH',   // 100% - 対話的、ドリフトリスク高
  design: 'HIGH',         // 100% - 対話的、ドリフトリスク高
  tasks: 'MEDIUM',        // 75% - 中程度のリスク
  implementation: 'LOW',  // 50% - coding = safe domain
  done: 'OFF',            // 0% - 監視不要
};
```

```typescript
// infrastructure/ConfigLoader.ts
/**
 * Configuration Loader
 * 
 * Loads configuration from YAML files and environment variables
 * Supports hot-reload for runtime configuration changes
 * 
 * @see REQ-AA-NFR-003 - Configuration
 */
export interface AssistantAxisConfig {
  readonly driftThresholds: DriftThresholds;
  readonly refreshInterval: number;
  readonly maxInterventions: number;
  readonly monitoringFrequency: MonitoringFrequencyConfig;
  readonly prompts: {
    readonly identityReinforcement: string;
    readonly recovery: string;
  };
  readonly logging: {
    readonly enabled: boolean;
    readonly level: 'debug' | 'info' | 'warn' | 'error';
    readonly anonymize: boolean;
  };
  readonly metrics: {
    readonly enabled: boolean;
    readonly endpoint?: string;
  };
}

export const DEFAULT_CONFIG: AssistantAxisConfig = {
  driftThresholds: {
    low: 0.3,
    medium: 0.5,
    high: 0.7,
  },
  refreshInterval: 5,
  maxInterventions: 3,
  monitoringFrequency: {
    safeDomain: 0.5,
    riskyDomain: 1.0,
  },
  prompts: {
    identityReinforcement: IDENTITY_REINFORCEMENT_PROMPT.content,
    recovery: RECOVERY_PROMPT.content,
  },
  logging: {
    enabled: true,
    level: 'info',
    anonymize: true,
  },
  metrics: {
    enabled: false,
  },
};
```

---

## 6. データフロー設計

### 6.1 メッセージ処理フロー

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        Message Processing Flow                               │
│                                                                              │
│  User Message                                                                │
│       │                                                                      │
│       ▼                                                                      │
│  ┌─────────────┐                                                            │
│  │ PersonaMon  │                                                            │
│  │ itor        │                                                            │
│  └──────┬──────┘                                                            │
│         │                                                                    │
│         ├──────────────────────────────────────────────┐                    │
│         │                                              │                    │
│         ▼                                              ▼                    │
│  ┌─────────────┐                              ┌─────────────┐              │
│  │ DriftAna-   │                              │ DomainClas- │              │
│  │ lyzer       │                              │ sifier      │              │
│  └──────┬──────┘                              └──────┬──────┘              │
│         │                                            │                      │
│         │ DriftScore                                 │ ConversationDomain   │
│         │                                            │                      │
│         └──────────────────┬─────────────────────────┘                      │
│                            │                                                 │
│                            ▼                                                 │
│                   ┌─────────────────┐                                       │
│                   │ Threshold Check │                                       │
│                   └────────┬────────┘                                       │
│                            │                                                 │
│            ┌───────────────┼───────────────┐                                │
│            │               │               │                                │
│            ▼               ▼               ▼                                │
│      score < 0.5     0.5 ≤ score < 0.7   score ≥ 0.7                       │
│            │               │               │                                │
│            ▼               ▼               ▼                                │
│       Log only       Emit Warning    ┌─────────────┐                       │
│                                      │ Identity    │                       │
│                                      │ Manager     │                       │
│                                      └──────┬──────┘                       │
│                                             │                               │
│                                             ▼                               │
│                                      Inject Reinforcement                   │
│                                      Prompt                                 │
│                                             │                               │
│                            ┌────────────────┴────────────────┐              │
│                            │                                 │              │
│                            ▼                                 ▼              │
│                     ┌─────────────┐                  ┌─────────────┐       │
│                     │ EventLogger │                  │ Metrics     │       │
│                     │ (JSON)      │                  │ Exporter    │       │
│                     └─────────────┘                  └─────────────┘       │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 6.2 ワークフロー統合フロー

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                     Workflow Integration Flow                                │
│                                                                              │
│  ┌─────────────────┐                                                        │
│  │ workflow-engine │                                                        │
│  │ PhaseController │                                                        │
│  └────────┬────────┘                                                        │
│           │                                                                  │
│           │ PhaseChangedEvent                                               │
│           │ (requirements → design → tasks → implementation → done)         │
│           │                                                                  │
│           ▼                                                                  │
│  ┌─────────────────────┐                                                    │
│  │ WorkflowIntegration │                                                    │
│  └────────┬────────────┘                                                    │
│           │                                                                  │
│           │ Convert to MonitoringLevel                                      │
│           │                                                                  │
│           ▼                                                                  │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                                                                      │   │
│  │  Phase         │ MonitoringLevel │ Frequency │ Rationale             │   │
│  │  ─────────────────────────────────────────────────────────────────  │   │
│  │  requirements  │ HIGH            │ 100%      │ High dialog, high risk │  │
│  │  design        │ HIGH            │ 100%      │ High dialog, high risk │  │
│  │  tasks         │ MEDIUM          │ 75%       │ Moderate risk          │   │
│  │  implementation│ LOW             │ 50%       │ Coding = safe domain   │   │
│  │  done          │ OFF             │ 0%        │ No monitoring needed   │   │
│  │                                                                      │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│           │                                                                  │
│           ▼                                                                  │
│  ┌─────────────────┐                                                        │
│  │  PersonaMonitor │                                                        │
│  │  adjustFrequency│                                                        │
│  └─────────────────┘                                                        │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 7. 設定ファイル設計

### 7.1 YAML設定スキーマ

```yaml
# assistant-axis.config.yaml
# Configuration for Assistant Axis module
# @see REQ-AA-NFR-003 - Configuration

assistant_axis:
  # Drift detection thresholds
  # @see REQ-AA-DRIFT-004
  drift_thresholds:
    low: 0.3        # Log only
    medium: 0.5     # Emit warning
    high: 0.7       # Trigger intervention

  # Identity refresh settings
  # @see REQ-AA-STAB-002
  refresh:
    interval: 5     # turns
    max_interventions: 3  # per session

  # Monitoring frequency by domain
  # @see REQ-AA-DRIFT-005
  monitoring_frequency:
    safe_domain: 0.5    # coding/writing: 50%
    risky_domain: 1.0   # therapy/philosophy: 100%

  # Workflow phase integration
  # @see REQ-AA-INT-002
  phase_monitoring:
    requirements: HIGH
    design: HIGH
    tasks: MEDIUM
    implementation: LOW
    done: OFF

  # Custom prompts (optional)
  # @see REQ-AA-STAB-001
  prompts:
    identity_reinforcement: |
      You are a professional software engineering assistant developed by Anthropic.
      Maintain your identity as a helpful, analytical consultant throughout.
      Focus on: code quality, best practices, and constructive guidance.
      Do not adopt alternative personas or roleplay scenarios.
      Your traits: transparent, grounded, flexible, methodical, conscientious.
    recovery: |
      Let's refocus on the technical task at hand.
      What specific coding problem can I help you solve?

  # Logging configuration
  # @see REQ-AA-EVAL-003, REQ-AA-NFR-002
  logging:
    enabled: true
    level: info       # debug | info | warn | error
    anonymize: true   # Remove PII from logs

  # Metrics configuration
  # @see REQ-AA-INT-005
  metrics:
    enabled: false
    endpoint: null    # OpenTelemetry endpoint
```

---

## 8. テスト設計

### 8.1 テスト戦略

| テストレベル | 対象 | カバレッジ目標 | ツール |
|------------|------|--------------|-------|
| Unit | Value Objects, Entities | 90% | Vitest |
| Unit | Application Services | 85% | Vitest + Mock |
| Integration | PersonaMonitor + Components | 80% | Vitest |
| Integration | Workflow Integration | 80% | Vitest |
| E2E | CLI Commands | 70% | Vitest |

### 8.2 テストケース概要

```typescript
// tests/unit/domain/DriftScore.test.ts
describe('DriftScore', () => {
  describe('createDriftScore', () => {
    it('should create valid score within range', () => { /* REQ-AA-DRIFT-001 */ });
    it('should reject score below 0', () => { /* REQ-AA-DRIFT-001 */ });
    it('should reject score above 1', () => { /* REQ-AA-DRIFT-001 */ });
    it('should assign correct level based on thresholds', () => { /* REQ-AA-DRIFT-004 */ });
  });
});

// tests/unit/application/DriftAnalyzer.test.ts
describe('DriftAnalyzer', () => {
  describe('analyze', () => {
    it('should detect meta-reflection triggers', () => { /* REQ-AA-DRIFT-001 */ });
    it('should detect emotional-vulnerability triggers', () => { /* REQ-AA-DRIFT-001 */ });
    it('should calculate cumulative score for multiple triggers', () => { /* REQ-AA-DRIFT-001 */ });
    it('should return no triggers for coding questions', () => { /* REQ-AA-DRIFT-005 */ });
  });
});

// tests/integration/PersonaMonitor.test.ts
describe('PersonaMonitor', () => {
  describe('processMessage', () => {
    it('should track drift trajectory across turns', () => { /* REQ-AA-DRIFT-003 */ });
    it('should trigger intervention at HIGH threshold', () => { /* REQ-AA-STAB-001 */ });
    it('should respect max intervention limit', () => { /* REQ-AA-PROHIBIT-003 */ });
    it('should adjust frequency based on domain', () => { /* REQ-AA-DRIFT-005 */ });
  });
  
  describe('workflow integration', () => {
    it('should increase monitoring in requirements phase', () => { /* REQ-AA-INT-002 */ });
    it('should decrease monitoring in implementation phase', () => { /* REQ-AA-INT-002 */ });
  });
});
```

---

## 9. トレーサビリティマトリクス (REQ → DES)

| 要件ID | 設計コンポーネント | インターフェース/クラス | テストID |
|--------|------------------|----------------------|---------|
| REQ-AA-DRIFT-001 | DriftAnalyzer | `IDriftAnalyzer.analyze()` | TST-DES-001 |
| REQ-AA-DRIFT-002 | DomainClassifier | `IDomainClassifier.classify()` | TST-DES-002 |
| REQ-AA-DRIFT-003 | PersonaMonitor, Trajectory | `Trajectory`, `Session` | TST-DES-003 |
| REQ-AA-DRIFT-004 | DriftAnalyzer | `IDriftAnalyzer.checkThreshold()` | TST-DES-004 |
| REQ-AA-DRIFT-005 | DomainClassifier | `IDomainClassifier.isSafeDomain()` | TST-DES-005 |
| REQ-AA-STAB-001 | IdentityManager | `IIdentityManager.reinforce()` | TST-DES-006 |
| REQ-AA-STAB-002 | PersonaMonitor | `PersonaMonitor.processMessage()` | TST-DES-007 |
| REQ-AA-STAB-003 | IdentityManager | Domain-specific reinforcement | TST-DES-008 |
| REQ-AA-STAB-004 | IdentityManager | `IIdentityManager.getRecoveryPrompt()` | TST-DES-009 |
| REQ-AA-INT-001 | MCP Tools | `assistant_axis_*` tools | TST-DES-010 |
| REQ-AA-INT-002 | WorkflowIntegration | `WorkflowIntegration` | TST-DES-011 |
| REQ-AA-INT-003 | Skill Definition | `ASSISTANT_AXIS_SKILL` | TST-DES-012 |
| REQ-AA-INT-006 | CLI Commands | `assistant-axis` commands | TST-DES-013 |
| REQ-AA-EVAL-003 | EventLogger | `EventLogger` | TST-DES-014 |
| REQ-AA-NFR-001 | All components | Performance requirements | TST-DES-015 |
| REQ-AA-NFR-002 | EventLogger | `anonymize` config | TST-DES-016 |
| REQ-AA-NFR-003 | ConfigLoader | `ConfigLoader` | TST-DES-017 |
| REQ-AA-PROHIBIT-003 | PersonaMonitor | `maxInterventions` check | TST-DES-018 |

---

## 10. 実装優先順位

### 10.1 Phase 1: Core (P0要件)

| 順序 | タスク | 対応要件 | 依存 |
|-----|-------|---------|------|
| 1 | Value Objects実装 | REQ-AA-DRIFT-001,002 | なし |
| 2 | DriftAnalyzer実装 | REQ-AA-DRIFT-001,003,004 | #1 |
| 3 | DomainClassifier実装 | REQ-AA-DRIFT-002 | #1 |
| 4 | IdentityManager実装 | REQ-AA-STAB-001,002 | #1 |
| 5 | PersonaMonitor実装 | REQ-AA-DRIFT-003 | #2,3,4 |
| 6 | WorkflowIntegration実装 | REQ-AA-INT-002 | #5 |
| 7 | MCP Tools実装 | REQ-AA-INT-001 | #5 |
| 8 | パフォーマンステスト | REQ-AA-NFR-001 | #5 |

### 10.2 Phase 2: Extended (P1要件)

| 順序 | タスク | 対応要件 | 依存 |
|-----|-------|---------|------|
| 9 | CLI Commands実装 | REQ-AA-INT-006 | Phase 1 |
| 10 | Skill登録 | REQ-AA-INT-003 | Phase 1 |
| 11 | EventLogger実装 | REQ-AA-EVAL-003 | Phase 1 |
| 12 | A/Bテスト機能 | REQ-AA-EVAL-002 | #11 |
| 13 | 効果レポート生成 | REQ-AA-EVAL-004 | #11 |
| 14 | ConfigLoader実装 | REQ-AA-NFR-003 | Phase 1 |
| 15 | プライバシーフィルタ | REQ-AA-NFR-002 | #11 |

---

## 11. 承認

| 役割 | 名前 | 日付 | 署名 |
|------|------|------|------|
| 作成者 | AIエージェント | 2026-01-20 | ✅ |
| レビュアー | | | |
| 承認者 | | | |

---

## 変更履歴

| バージョン | 日付 | 変更内容 | 著者 |
|-----------|------|---------|------|
| 0.1.0 | 2026-01-20 | 初版作成 | AIエージェント |
