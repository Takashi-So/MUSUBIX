# MUSUBIX改良 設計書
## FastRender分析知見に基づく機能強化

| 項目 | 内容 |
|------|------|
| **文書ID** | DES-MUSUBIX-FR-001 |
| **バージョン** | 1.2.0 |
| **作成日** | 2026-01-23 |
| **更新日** | 2026-01-23 |
| **ステータス** | Draft |
| **関連要件** | REQ-MUSUBIX-FR-001 (v1.2.0) |
| **設計パターン** | Repository, Service, Strategy, Observer, Factory |

---

## 1. 設計概要

### 1.1 設計原則

本設計は以下の原則に従う：

| 原則 | 適用 |
|:--|:--|
| **SOLID** | 単一責任、開放閉鎖、リスコフ置換、インターフェース分離、依存性逆転 |
| **憲法II条** | すべてのライブラリはCLI公開必須 |
| **憲法V条** | 要件↔設計↔コード↔テストの100%追跡 |
| **憲法VII条** | 設計パターン適用の文書化 |

### 1.2 トレーサビリティマトリクス

| 要件ID | 設計ID | コンポーネント | 優先度 |
|:--|:--|:--|:--:|
| REQ-FR-001〜003 | DES-POLICY-001 | BalanceRuleEngine | P2 |
| REQ-FR-010〜012 | DES-ORCH-001 | WorkstreamManager | P4 |
| REQ-FR-020〜023 | DES-POLICY-002 | NonNegotiablesEngine | P0 |
| REQ-FR-030〜032 | DES-CORE-001 | MetricsCollector | P3 |
| REQ-FR-040〜041 | DES-WORKFLOW-001 | TriageEngine | P2 |
| REQ-FR-050〜052 | DES-PATTERN-001 | PatternLearningDB | P3 |
| REQ-FR-060〜063 | DES-ORCH-002 | ResourceLimiter | P0 |
| REQ-FR-070〜071 | DES-CODEGRAPH-001 | TestPlacementValidator | P4 |
| REQ-FR-080〜082 | DES-WORKFLOW-002 | EvidenceLevelValidator | P1 |
| REQ-FR-090〜092 | DES-ORCH-003 | SingleStepEnforcer | P1 |

---

## 2. C4モデル

### 2.1 Context図

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                            System Context                                    │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│    ┌──────────────┐                           ┌──────────────────┐          │
│    │              │                           │                  │          │
│    │  Developer   │────────────────────────▶  │  AI Agent        │          │
│    │  (User)      │                           │  (Cursor/Claude) │          │
│    │              │                           │                  │          │
│    └──────────────┘                           └────────┬─────────┘          │
│           │                                            │                    │
│           │                                            │                    │
│           ▼                                            ▼                    │
│    ┌───────────────────────────────────────────────────────────────┐        │
│    │                                                               │        │
│    │                     MUSUBIX System                            │        │
│    │                                                               │        │
│    │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐   │        │
│    │  │ MCP Server  │  │ CLI Tools   │  │ VS Code Extension   │   │        │
│    │  └─────────────┘  └─────────────┘  └─────────────────────┘   │        │
│    │                                                               │        │
│    └───────────────────────────────────────────────────────────────┘        │
│                              │                                              │
│                              ▼                                              │
│                    ┌──────────────────┐                                     │
│                    │                  │                                     │
│                    │  Local Storage   │                                     │
│                    │  (Git-friendly)  │                                     │
│                    │                  │                                     │
│                    └──────────────────┘                                     │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 2.2 Container図

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           MUSUBIX Containers                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │                         MCP Server Layer                             │    │
│  │  ┌───────────────┐  ┌───────────────┐  ┌───────────────────────┐    │    │
│  │  │  policy-tools │  │ workflow-tools│  │ orchestrator-tools   │    │    │
│  │  │  (14 tools)   │  │  (10 tools)   │  │     (12 tools)       │    │    │
│  │  └───────┬───────┘  └───────┬───────┘  └───────────┬───────────┘    │    │
│  └──────────┼──────────────────┼──────────────────────┼────────────────┘    │
│             │                  │                      │                     │
│             ▼                  ▼                      ▼                     │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │                        Core Libraries                                │    │
│  │                                                                      │    │
│  │  ┌─────────────────────┐  ┌─────────────────────┐                   │    │
│  │  │  @musubix/policy    │  │ workflow-engine     │                   │    │
│  │  │                     │  │                     │                   │    │
│  │  │  • BalanceRule      │  │ • TriageEngine      │                   │    │
│  │  │  • NonNegotiables   │  │ • EvidenceValidator │                   │    │
│  │  └─────────────────────┘  └─────────────────────┘                   │    │
│  │                                                                      │    │
│  │  ┌─────────────────────┐  ┌─────────────────────┐                   │    │
│  │  │ agent-orchestrator  │  │   pattern-mcp       │                   │    │
│  │  │                     │  │                     │                   │    │
│  │  │ • ResourceLimiter   │  │ • PatternLearningDB │                   │    │
│  │  │ • WorkstreamManager │  │ • AntiPatternAlert  │                   │    │
│  │  │ • SingleStepEnforcer│  └─────────────────────┘                   │    │
│  │  └─────────────────────┘                                            │    │
│  │                                                                      │    │
│  │  ┌─────────────────────┐  ┌─────────────────────┐                   │    │
│  │  │    codegraph        │  │      core           │                   │    │
│  │  │                     │  │                     │                   │    │
│  │  │ • TestPlacement     │  │ • MetricsCollector  │                   │    │
│  │  │   Validator         │  │ • MetricsDisplay    │                   │    │
│  │  └─────────────────────┘  └─────────────────────┘                   │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                              │                                              │
│                              ▼                                              │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │                        Storage Layer                                 │    │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌───────────┐  │    │
│  │  │ .knowledge/ │  │  .metrics/  │  │  .patterns/ │  │ .evidence/│  │    │
│  │  │ graph.json  │  │  data.json  │  │  library.json│ │  *.json   │  │    │
│  │  └─────────────┘  └─────────────┘  └─────────────┘  └───────────┘  │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 3. ワークフロー統合設計（v1.1.0 NEW!）

### 3.1 MUSUBIX 5フェーズワークフローへの統合

新規コンポーネントは既存の5フェーズワークフローに統合される。

```
┌────────────────────────────────────────────────────────────────────────────────┐
│                    MUSUBIX Enhanced Workflow Integration                        │
├────────────────────────────────────────────────────────────────────────────────┤
│                                                                                │
│  ╔═══════════════════════════════════════════════════════════════════════════╗ │
│  ║ [GLOBAL LAYER] 全フェーズで常時稼働                                        ║ │
│  ║                                                                            ║ │
│  ║  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐           ║ │
│  ║  │ ResourceLimiter │  │ MetricsCollector│  │ PatternLearning │           ║ │
│  ║  │ (DES-ORCH-002)  │  │ (DES-CORE-001)  │  │ (DES-PATTERN-001)│          ║ │
│  ║  │                 │  │                 │  │                 │           ║ │
│  ║  │ • タイムアウト  │  │ • 実行時間記録  │  │ • 失敗パターン  │           ║ │
│  ║  │ • メモリ制限    │  │ • エラー記録    │  │   自動登録      │           ║ │
│  ║  │ • 暴走検出      │  │ • カバレッジ    │  │ • 成功パターン  │           ║ │
│  ║  └─────────────────┘  └─────────────────┘  │   自動登録      │           ║ │
│  ║                                            └─────────────────┘           ║ │
│  ╚═══════════════════════════════════════════════════════════════════════════╝ │
│                                                                                │
│  ┌─────────┐     ┌─────────┐     ┌─────────┐     ┌─────────┐     ┌─────────┐ │
│  │ Phase 1 │ ──▶ │ Phase 2 │ ──▶ │ Phase 3 │ ──▶ │ Phase 4 │ ──▶ │ Phase 5 │ │
│  │ 要件定義│     │  設計   │     │タスク分解│     │  実装   │     │  完了   │ │
│  └────┬────┘     └────┬────┘     └────┬────┘     └────┬────┘     └────┬────┘ │
│       │               │               │               │               │       │
│  ┌────┴────┐     ┌────┴────┐     ┌────┴────┐     ┌────┴────┐     ┌────┴────┐ │
│  │ENTRY    │     │ENTRY    │     │ENTRY    │     │ENTRY    │     │ENTRY    │ │
│  │GATE     │     │GATE     │     │GATE     │     │GATE     │     │GATE     │ │
│  │         │     │         │     │         │     │         │     │         │ │
│  │ Triage  │     │ (none)  │     │ Triage  │     │ 前提条件│     │ (none)  │ │
│  │ Engine  │     │         │     │ Engine  │     │ チェック│     │         │ │
│  └────┬────┘     └────┬────┘     └────┬────┘     └────┬────┘     └────┬────┘ │
│       │               │               │               │               │       │
│       ▼               ▼               ▼               ▼               ▼       │
│  ┌─────────┐     ┌─────────┐     ┌─────────┐     ┌─────────┐     ┌─────────┐ │
│  │DURING   │     │DURING   │     │DURING   │     │DURING   │     │DURING   │ │
│  │PHASE    │     │PHASE    │     │PHASE    │     │PHASE    │     │PHASE    │ │
│  │         │     │         │     │         │     │         │     │         │ │
│  │ (none)  │     │ (none)  │     │ (none)  │     │SingleStep│    │ (none)  │ │
│  │         │     │         │     │         │     │Enforcer │     │         │ │
│  │         │     │         │     │         │     │         │     │         │ │
│  │         │     │         │     │         │     │Workstream│    │         │ │
│  │         │     │         │     │         │     │Manager  │     │         │ │
│  └────┬────┘     └────┬────┘     └────┬────┘     └────┬────┘     └────┬────┘ │
│       │               │               │               │               │       │
│       ▼               ▼               ▼               ▼               ▼       │
│  ┌─────────┐     ┌─────────┐     ┌─────────┐     ┌─────────┐     ┌─────────┐ │
│  │EXIT     │     │EXIT     │     │EXIT     │     │EXIT     │     │EXIT     │ │
│  │GATE     │     │GATE     │     │GATE     │     │GATE     │     │GATE     │ │
│  │(Quality)│     │(Quality)│     │(Quality)│     │(Quality)│     │(Quality)│ │
│  │         │     │         │     │         │     │         │     │         │ │
│  │ EARS    │     │ Non-Neg │     │ タスク  │     │ Non-Neg │     │ Balance │ │
│  │ 検証    │     │ Engine  │     │ 検証    │     │ Engine  │     │ Rule    │ │
│  │         │     │ (設計)  │     │         │     │ (コード)│     │         │ │
│  │         │     │         │     │         │     │         │     │ Evidence│ │
│  │         │     │         │     │         │     │ Test    │     │Validator│ │
│  │         │     │         │     │         │     │Placement│     │         │ │
│  │         │     │         │     │         │     │Validator│     │         │ │
│  └─────────┘     └─────────┘     └─────────┘     └─────────┘     └─────────┘ │
│                                                                                │
└────────────────────────────────────────────────────────────────────────────────┘
```

### 3.2 統合ポイント詳細

| コンポーネント | 統合レイヤー | 発動タイミング | 統合方法 |
|:--|:--|:--|:--|
| **ResourceLimiter** | GLOBAL | 全操作 | `PhaseController` ラッパー |
| **MetricsCollector** | GLOBAL | 全操作 | `PhaseController` イベントリスナー |
| **PatternLearningDB** | GLOBAL | 失敗/成功時 | `QualityGateRunner` イベントリスナー |
| **TriageEngine** | ENTRY_GATE | Phase 1, 3開始時 | `QualityGate` として登録 |
| **NonNegotiablesEngine** | EXIT_GATE | Phase 2, 4完了時 | `QualityGate` として登録 |
| **SingleStepEnforcer** | DURING_PHASE | Phase 4実行中 | `PhaseController` 拡張 |
| **WorkstreamManager** | DURING_PHASE | Phase 4並列実行時 | `ParallelExecutor` 拡張 |
| **TestPlacementValidator** | EXIT_GATE | Phase 4完了時 | `QualityGate` として登録 |
| **EvidenceLevelValidator** | EXIT_GATE | Phase 5完了時 | `QualityGate` として登録 |
| **BalanceRuleEngine** | EXIT_GATE | Phase 5完了時 | `QualityGate` として登録 |

### 3.3 QualityGate統合

既存の `QualityGate` 型を拡張し、`QualityGateRunner` に新規ゲートを登録する。

#### 3.3.1 既存QualityGate型の拡張

```typescript
// packages/workflow-engine/src/domain/entities/ExtendedQualityGate.ts

import type {
  QualityGate,
  QualityCheckResult,
  PhaseType,
  PhaseArtifact,
  Task,
} from '../index.js';
import type { ITriageEngine } from '../../application/TriageEngine.js';
import type { INonNegotiablesEngine } from '@musubix/policy';
import type { IEvidenceLevelValidator } from '../../application/EvidenceLevelValidator.js';
import type { IBalanceRuleEngine } from '@musubix/policy';
import type { ITestPlacementValidator } from '@nahisaho/musubix-codegraph';

/**
 * ゲート実行タイミング
 * @trace DES-MUSUBIX-FR-001 Section 3.3.1
 */
export type GateTiming = 'entry' | 'exit';

/**
 * ゲート実行コンテキスト
 * FastRender知見に基づく拡張ゲートで使用
 */
export interface GateExecutionContext {
  /** ワークフローID */
  readonly workflowId: string;
  /** 現在のフェーズ */
  readonly phase: PhaseType;
  /** フェーズ成果物 */
  readonly artifacts: readonly PhaseArtifact[];
  /** 変更されたファイル（Phase 4用） */
  readonly changedFiles?: readonly string[];
  /** タスク一覧（Phase 5用） */
  readonly tasks?: readonly Task[];
  /** サービス依存性 */
  readonly services: GateServices;
}

/**
 * ゲートで使用するサービス群
 */
export interface GateServices {
  readonly triageEngine?: ITriageEngine;
  readonly nonNegotiablesEngine?: INonNegotiablesEngine;
  readonly evidenceLevelValidator?: IEvidenceLevelValidator;
  readonly balanceRuleEngine?: IBalanceRuleEngine;
  readonly testPlacementValidator?: ITestPlacementValidator;
}

/**
 * 拡張QualityGate（FastRender機能用）
 * 既存のQualityGate型を拡張し、timingとcontextを追加
 */
export interface ExtendedQualityGate {
  /** ゲートID */
  readonly id: string;
  /** ゲート名 */
  readonly name: string;
  /** 対象フェーズ */
  readonly phase: PhaseType;
  /** 説明 */
  readonly description: string;
  /** 必須フラグ */
  readonly mandatory: boolean;
  /** 実行タイミング（entry: フェーズ開始時, exit: フェーズ完了時） */
  readonly timing: GateTiming;
  /** コンテキスト付きチェック関数 */
  readonly check: (context: GateExecutionContext) => Promise<QualityCheckResult>;
}

/**
 * 拡張ゲートを標準QualityGateに変換
 * 既存のQualityGateRunnerとの互換性を維持
 * 
 * @param extended - 拡張ゲート
 * @param contextProvider - コンテキスト提供関数
 * @returns 標準QualityGate
 */
export function toStandardGate(
  extended: ExtendedQualityGate,
  contextProvider: () => GateExecutionContext
): QualityGate {
  return Object.freeze({
    id: extended.id,
    name: extended.name,
    phase: extended.phase,
    description: extended.description,
    mandatory: extended.mandatory,
    check: async (): Promise<QualityCheckResult> => {
      return extended.check(contextProvider());
    },
  });
}

/**
 * 拡張ゲートを作成
 */
export function createExtendedGate(params: {
  id: string;
  name: string;
  phase: PhaseType;
  description: string;
  mandatory?: boolean;
  timing: GateTiming;
  check: (context: GateExecutionContext) => Promise<QualityCheckResult>;
}): ExtendedQualityGate {
  return Object.freeze({
    id: params.id,
    name: params.name,
    phase: params.phase,
    description: params.description,
    mandatory: params.mandatory ?? true,
    timing: params.timing,
    check: params.check,
  });
}
```

#### 3.3.2 新規QualityGate定義

```typescript
// packages/workflow-engine/src/application/quality-gates/fastrender-gates.ts

import {
  type ExtendedQualityGate,
  type GateExecutionContext,
  createExtendedGate,
} from '../../domain/entities/ExtendedQualityGate.js';

/**
 * FastRender知見に基づく新規QualityGate定義
 * @trace DES-MUSUBIX-FR-001 Section 3.3.2
 */
export const FASTRENDER_QUALITY_GATES: readonly ExtendedQualityGate[] = [
  // Phase 1 Entry Gate
  createExtendedGate({
    id: 'gate-triage-requirements',
    name: 'Requirements Triage',
    phase: 'requirements',
    description: '未解決のP0/P1タスクがある場合、新規要件の開始をブロック',
    mandatory: true,
    timing: 'entry',
    check: async (context: GateExecutionContext) => {
      const { triageEngine } = context.services;
      if (!triageEngine) {
        return { passed: true, message: 'Triage engine not configured', severity: 'info' };
      }
      return triageEngine.checkPriorityBlocking();
    },
  }),
  
  // Phase 2 Exit Gate
  createExtendedGate({
    id: 'gate-non-negotiables-design',
    name: 'Non-negotiables Design Check',
    phase: 'design',
    description: '設計成果物がNon-negotiablesルールに違反していないか検証',
    mandatory: true,
    timing: 'exit',
    check: async (context: GateExecutionContext) => {
      const { nonNegotiablesEngine } = context.services;
      if (!nonNegotiablesEngine) {
        return { passed: true, message: 'Non-negotiables engine not configured', severity: 'info' };
      }
      const result = await nonNegotiablesEngine.validateDesignArtifacts(context.artifacts);
      return {
        passed: result.passed,
        message: result.passed ? 'Design artifacts validated' : `${result.violations.length} violations found`,
        details: result.violations.map(v => v.message).join('; '),
        severity: result.passed ? 'info' : 'error',
      };
    },
  }),
  
  // Phase 3 Entry Gate
  createExtendedGate({
    id: 'gate-triage-tasks',
    name: 'Task Triage',
    phase: 'task-breakdown',
    description: '未解決のP0/P1タスクがある場合、新規タスク分解をブロック',
    mandatory: true,
    timing: 'entry',
    check: async (context: GateExecutionContext) => {
      const { triageEngine } = context.services;
      if (!triageEngine) {
        return { passed: true, message: 'Triage engine not configured', severity: 'info' };
      }
      return triageEngine.checkPriorityBlocking();
    },
  }),
  
  // Phase 4 Exit Gates
  createExtendedGate({
    id: 'gate-non-negotiables-code',
    name: 'Non-negotiables Code Check',
    phase: 'implementation',
    description: 'コードがNon-negotiablesルールに違反していないか検証',
    mandatory: true,
    timing: 'exit',
    check: async (context: GateExecutionContext) => {
      const { nonNegotiablesEngine } = context.services;
      if (!nonNegotiablesEngine) {
        return { passed: true, message: 'Non-negotiables engine not configured', severity: 'info' };
      }
      const result = await nonNegotiablesEngine.validateCodeArtifacts(context.artifacts);
      return {
        passed: result.passed,
        message: result.passed ? 'Code artifacts validated' : `${result.violations.length} violations found`,
        details: result.violations.map(v => `${v.location?.file}:${v.location?.line} - ${v.message}`).join('\n'),
        severity: result.passed ? 'info' : 'error',
      };
    },
  }),
  
  createExtendedGate({
    id: 'gate-test-placement',
    name: 'Test Placement Validation',
    phase: 'implementation',
    description: 'テストファイルが正しいディレクトリに配置されているか検証',
    mandatory: false, // 警告のみ
    timing: 'exit',
    check: async (context: GateExecutionContext) => {
      const { testPlacementValidator } = context.services;
      if (!testPlacementValidator || !context.changedFiles) {
        return { passed: true, message: 'Test placement validator not configured', severity: 'info' };
      }
      return testPlacementValidator.validate(context.changedFiles);
    },
  }),
  
  // Phase 5 Exit Gates
  createExtendedGate({
    id: 'gate-evidence-level',
    name: 'Evidence Level Verification',
    phase: 'completion',
    description: 'タスク完了時に必要な証拠レベルを満たしているか検証',
    mandatory: true,
    timing: 'exit',
    check: async (context: GateExecutionContext) => {
      const { evidenceLevelValidator } = context.services;
      if (!evidenceLevelValidator || !context.tasks) {
        return { passed: true, message: 'Evidence validator not configured', severity: 'info' };
      }
      const result = await evidenceLevelValidator.verifyAllTasks(context.tasks);
      return {
        passed: result.passed,
        message: result.message,
        severity: result.passed ? 'info' : 'error',
      };
    },
  }),
  
  createExtendedGate({
    id: 'gate-balance-rule',
    name: '90/10 Balance Check',
    phase: 'completion',
    description: 'カウント対象変更が90%以上を維持しているか検証',
    mandatory: false, // 警告のみ
    timing: 'exit',
    check: async (context: GateExecutionContext) => {
      const { balanceRuleEngine } = context.services;
      if (!balanceRuleEngine) {
        return { passed: true, message: 'Balance rule engine not configured', severity: 'info' };
      }
      const stats = await balanceRuleEngine.getStats();
      return {
        passed: !stats.exceedsThreshold,
        message: stats.exceedsThreshold
          ? `Balance warning: ${(stats.ratio * 100).toFixed(1)}% non-counted changes (threshold: ${stats.threshold}%)`
          : `Balance OK: ${(stats.ratio * 100).toFixed(1)}% non-counted changes`,
        severity: stats.exceedsThreshold ? 'warning' : 'info',
      };
    },
  }),
];
```

#### 3.3.3 QualityGateRunner拡張

```typescript
// packages/workflow-engine/src/application/ExtendedQualityGateRunner.ts

import { QualityGateRunner, type GateRunResult } from './QualityGateRunner.js';
import {
  type ExtendedQualityGate,
  type GateExecutionContext,
  type GateTiming,
  toStandardGate,
} from '../domain/entities/ExtendedQualityGate.js';
import { FASTRENDER_QUALITY_GATES } from './quality-gates/fastrender-gates.js';

/**
 * 拡張QualityGateRunner
 * 既存のQualityGateRunnerを拡張し、entry/exit timingをサポート
 */
export class ExtendedQualityGateRunner extends QualityGateRunner {
  private extendedGates: Map<string, ExtendedQualityGate> = new Map();
  private contextProvider?: () => GateExecutionContext;

  constructor(config?: QualityGateRunnerConfig) {
    super(config);
  }

  /**
   * コンテキストプロバイダを設定
   */
  setContextProvider(provider: () => GateExecutionContext): void {
    this.contextProvider = provider;
  }

  /**
   * 拡張ゲートを登録
   */
  registerExtendedGate(gate: ExtendedQualityGate): void {
    this.extendedGates.set(gate.id, gate);
    
    // 標準ゲートとしても登録（既存のrunGatesと互換性維持）
    if (this.contextProvider) {
      const standardGate = toStandardGate(gate, this.contextProvider);
      this.registerGate(standardGate);
    }
  }

  /**
   * FastRender標準ゲートをすべて登録
   */
  registerFastRenderGates(): void {
    for (const gate of FASTRENDER_QUALITY_GATES) {
      this.registerExtendedGate(gate);
    }
  }

  /**
   * 特定タイミングのゲートのみ実行
   */
  async runGatesByTiming(
    phase: PhaseType,
    timing: GateTiming,
    context: GateExecutionContext
  ): Promise<GateRunResult> {
    const gates = Array.from(this.extendedGates.values())
      .filter(g => g.phase === phase && g.timing === timing);
    
    // 一時的にコンテキストプロバイダを設定
    const originalProvider = this.contextProvider;
    this.contextProvider = () => context;
    
    try {
      // フィルタされたゲートのみ実行
      const results = await Promise.all(
        gates.map(async gate => {
          const result = await gate.check(context);
          return {
            gateId: gate.id,
            gateName: gate.name,
            results: [result],
            passed: result.passed,
            executedAt: new Date(),
            duration: 0,
          };
        })
      );
      
      const allPassed = results.every(r => r.passed);
      const mandatoryPassed = results
        .filter((r, i) => gates[i].mandatory)
        .every(r => r.passed);
      
      return {
        phase,
        results,
        allPassed,
        mandatoryPassed,
        summary: `${timing} gates: ${results.filter(r => r.passed).length}/${results.length} passed`,
        duration: 0,
      };
    } finally {
      this.contextProvider = originalProvider;
    }
  }
}
```

### 3.4 PhaseController拡張

```typescript
// packages/workflow-engine/src/application/PhaseController.ts (拡張)

import type { IResourceLimiter } from '@nahisaho/musubix-agent-orchestrator';
import type { IMetricsCollector } from '@nahisaho/musubix-core';
import type { ISingleStepEnforcer } from './SingleStepEnforcer.js';

/**
 * 拡張PhaseController設定
 * @trace DES-MUSUBIX-FR-001 Section 3.4
 */
export interface EnhancedPhaseControllerConfig extends PhaseControllerConfig {
  /** リソース制限を有効化 */
  enableResourceLimiter?: boolean;
  /** メトリクス収集を有効化 */
  enableMetricsCollection?: boolean;
  /** シングルステップ強制を有効化（Phase 4のみ） */
  enableSingleStepEnforcer?: boolean;
}

/**
 * 拡張PhaseController
 * 
 * 既存のPhaseControllerを拡張し、FastRender知見に基づく
 * 新機能をワークフローに統合
 */
export class EnhancedPhaseController extends PhaseController {
  private resourceLimiter?: IResourceLimiter;
  private metricsCollector?: IMetricsCollector;
  private singleStepEnforcer?: ISingleStepEnforcer;
  
  constructor(
    config: EnhancedPhaseControllerConfig,
    services: {
      resourceLimiter?: IResourceLimiter;
      metricsCollector?: IMetricsCollector;
      singleStepEnforcer?: ISingleStepEnforcer;
    }
  ) {
    super(config);
    
    if (config.enableResourceLimiter && services.resourceLimiter) {
      this.resourceLimiter = services.resourceLimiter;
    }
    if (config.enableMetricsCollection && services.metricsCollector) {
      this.metricsCollector = services.metricsCollector;
    }
    if (config.enableSingleStepEnforcer && services.singleStepEnforcer) {
      this.singleStepEnforcer = services.singleStepEnforcer;
    }
  }
  
  /**
   * フェーズ遷移（リソース制限付き）
   */
  async advancePhaseWithLimits(
    workflowId: string,
    approver: string
  ): Promise<PhaseControllerResult<Phase>> {
    // メトリクス記録開始
    const startTime = Date.now();
    this.metricsCollector?.onPhaseStart(workflowId);
    
    try {
      // リソース制限付きで実行
      if (this.resourceLimiter) {
        const result = await this.resourceLimiter.executeWithTimeout(
          () => this.advancePhase(workflowId, approver),
          'normalBuild'
        );
        
        if (!result.success) {
          this.metricsCollector?.onError(workflowId, result.error);
          return {
            success: false,
            error: result.error?.message,
            message: 'Phase transition timed out or exceeded resource limits',
          };
        }
        
        return result.data!;
      }
      
      return await this.advancePhase(workflowId, approver);
    } finally {
      // メトリクス記録終了
      this.metricsCollector?.onPhaseEnd(workflowId, Date.now() - startTime);
    }
  }
  
  /**
   * Phase 4開始時にSingleStepEnforcerを有効化
   */
  protected onEnterImplementationPhase(workflowId: string): void {
    if (this.singleStepEnforcer) {
      this.singleStepEnforcer.enable(workflowId);
    }
  }
  
  /**
   * Phase 4終了時にSingleStepEnforcerを無効化
   */
  protected onExitImplementationPhase(workflowId: string): void {
    if (this.singleStepEnforcer) {
      this.singleStepEnforcer.disable(workflowId);
    }
  }
}
```

### 3.5 グローバルレイヤー統合

```typescript
// packages/agent-orchestrator/src/application/GlobalLayerManager.ts

/**
 * グローバルレイヤー管理
 * 
 * 全フェーズで常時稼働するコンポーネントを管理
 * @trace DES-MUSUBIX-FR-001 Section 3.1
 */
export class GlobalLayerManager {
  private resourceLimiter: ResourceLimiter;
  private metricsCollector: MetricsCollector;
  private patternLearningDB: PatternLearningDB;
  
  constructor(config: GlobalLayerConfig) {
    this.resourceLimiter = new ResourceLimiter(config.resourceLimits);
    this.metricsCollector = new MetricsCollector(config.metricsConfig);
    this.patternLearningDB = new PatternLearningDB(config.patternConfig);
    
    // イベント連携
    this.setupEventHandlers();
  }
  
  private setupEventHandlers(): void {
    // 失敗時にパターン自動登録
    this.metricsCollector.on('taskFailed', (event) => {
      this.patternLearningDB.registerFailure({
        context: event.context,
        errorType: event.errorType,
        timestamp: event.timestamp,
      });
    });
    
    // 成功時にパターン自動登録
    this.metricsCollector.on('taskSucceeded', (event) => {
      this.patternLearningDB.registerSuccess({
        context: event.context,
        approach: event.approach,
        timestamp: event.timestamp,
      });
    });
  }
  
  /**
   * 操作をラップしてリソース制限・メトリクス収集を適用
   */
  async wrapOperation<T>(
    operation: () => Promise<T>,
    operationType: OperationType,
    context: OperationContext
  ): Promise<OperationResult<T>> {
    const taskId = this.metricsCollector.startTask(context);
    
    try {
      const result = await this.resourceLimiter.executeWithTimeout(
        operation,
        operationType
      );
      
      if (result.success) {
        this.metricsCollector.endTask(taskId, 'success');
      } else {
        this.metricsCollector.endTask(taskId, 'timeout');
      }
      
      return result;
    } catch (error) {
      this.metricsCollector.endTask(taskId, 'error', error);
      throw error;
    }
  }
}
```

---

## 4. コンポーネント設計

### 4.1 DES-ORCH-002: ResourceLimiter（P0）

**トレース**: REQ-FR-060〜063
**ワークフロー統合**: GLOBAL Layer

**設計パターン**: Strategy + Observer

```
┌─────────────────────────────────────────────────────────────────┐
│                      ResourceLimiter                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌────────────────────┐      ┌────────────────────────┐        │
│  │  ResourceMonitor   │◀────▶│  ResourceLimitConfig   │        │
│  │  (Observer)        │      │  (Strategy)            │        │
│  │                    │      │                        │        │
│  │  • cpu: number     │      │  • timeout: Map        │        │
│  │  • memory: number  │      │  • memoryLimit: number │        │
│  │  • disk: number    │      │  • scopeRequired: bool │        │
│  └─────────┬──────────┘      └────────────────────────┘        │
│            │                                                    │
│            ▼                                                    │
│  ┌────────────────────┐      ┌────────────────────────┐        │
│  │  TimeoutEnforcer   │      │  RunawayDetector       │        │
│  │                    │      │                        │        │
│  │  • enforce()       │      │  • detect()            │        │
│  │  • abort()         │      │  • terminate()         │        │
│  │  • cleanup()       │      │  • alert()             │        │
│  └────────────────────┘      └────────────────────────┘        │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

#### ディレクトリ構造（既存構造に準拠）

```
packages/agent-orchestrator/src/
├── domain/
│   ├── value-objects/
│   │   ├── ResourceUsage.ts          # リソース使用量VO
│   │   ├── ResourceLimitConfig.ts    # 設定VO
│   │   └── OperationType.ts          # 操作タイプVO
│   └── services/
│       ├── ResourceMonitor.ts        # リソース監視ドメインサービス
│       └── RunawayDetector.ts        # 暴走検出ドメインサービス
├── application/
│   ├── ResourceLimitExecutor.ts      # アプリケーションサービス
│   └── GlobalLayerManager.ts         # グローバルレイヤー管理
└── infrastructure/
    └── ProcessMonitorAdapter.ts      # OS依存の監視実装
```

#### インターフェース定義

```typescript
// packages/agent-orchestrator/src/domain/value-objects/ResourceLimitConfig.ts

/**
 * 操作タイプ
 * @trace REQ-FR-060
 */
export type OperationType = 
  | 'normalBuild'
  | 'singleTest'
  | 'fullHarness'
  | 'codeGeneration';

/**
 * リソース制限設定
 * @trace REQ-FR-060
 */
export interface ResourceLimitConfig {
  /** 操作タイプ別タイムアウト（ミリ秒） */
  readonly timeouts: Readonly<Record<OperationType, number>>;
  /** メモリ上限（バイト） */
  readonly memoryLimit: number;
  /** スコープ指定必須フラグ */
  readonly scopeRequired: boolean;
}

/**
 * デフォルト設定
 */
export const DEFAULT_RESOURCE_LIMITS: ResourceLimitConfig = {
  timeouts: {
    normalBuild: 600_000,    // 10分
    singleTest: 120_000,     // 2分
    fullHarness: 900_000,    // 15分
    codeGeneration: 300_000, // 5分
  },
  memoryLimit: 2 * 1024 * 1024 * 1024, // 2GB
  scopeRequired: true,
};
```

```typescript
// packages/agent-orchestrator/src/domain/value-objects/ResourceUsage.ts

/**
 * リソース使用量
 * @trace REQ-FR-061
 */
export interface ResourceUsage {
  readonly cpuPercent: number;
  readonly memoryBytes: number;
  readonly diskWriteBytes: number;
  readonly timestamp: Date;
}

/**
 * 暴走検出結果
 * @trace REQ-FR-063
 */
export interface RunawayDetectionResult {
  readonly detected: boolean;
  readonly type: 'infinite-loop' | 'memory-explosion' | 'disk-flood' | 'none';
  readonly details?: string;
}
```

```typescript
// packages/agent-orchestrator/src/application/ResourceLimitExecutor.ts

/**
 * リソース制限実行結果
 * 既存のPhaseControllerResultパターンに準拠
 */
export interface ResourceLimitResult<T> {
  readonly success: boolean;
  readonly data?: T;
  readonly error?: ResourceLimitError;
  readonly message: string;
}

/**
 * リソース制限エラー
 * 既存のActionableErrorを継承
 */
export class ResourceLimitError extends ActionableError {
  constructor(
    public readonly type: 'timeout' | 'memory' | 'runaway' | 'scope',
    message: string,
    suggestions?: string[]
  ) {
    super(message, 'ERR-RESOURCE', suggestions);
  }
}

/**
 * リソース制限実行サービス
 */
export interface IResourceLimitExecutor {
  /** タイムアウト付きで操作を実行 */
  executeWithTimeout<T>(
    operation: () => Promise<T>,
    type: OperationType,
    options?: { signal?: AbortSignal }
  ): Promise<ResourceLimitResult<T>>;

  /** リソース使用量を取得 */
  getResourceUsage(): Promise<ResourceUsage>;

  /** 暴走を検出 */
  detectRunaway(): Promise<RunawayDetectionResult>;

  /** プロセスを強制終了 */
  terminate(pid: number): Promise<void>;
}
```

---

### 4.2 DES-POLICY-002: NonNegotiablesEngine（P0）

**トレース**: REQ-FR-020〜023
**ワークフロー統合**: EXIT_GATE (Phase 2, 4)

**設計パターン**: Strategy + Chain of Responsibility

```
┌─────────────────────────────────────────────────────────────────┐
│                    NonNegotiablesEngine                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌────────────────────┐      ┌────────────────────────┐        │
│  │  RuleLoader        │─────▶│  non-negotiables.yml   │        │
│  │                    │      │  (設定ファイル)         │        │
│  └─────────┬──────────┘      └────────────────────────┘        │
│            │                                                    │
│            ▼                                                    │
│  ┌─────────────────────────────────────────────────────┐       │
│  │                  RuleChain                           │       │
│  │  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌────────┐ │       │
│  │  │ HackRule │→│ SpecRule │→│ PanicRule│→│ ...    │ │       │
│  │  └──────────┘ └──────────┘ └──────────┘ └────────┘ │       │
│  └─────────────────────────────────────────────────────┘       │
│            │                                                    │
│            ▼                                                    │
│  ┌────────────────────┐      ┌────────────────────────┐        │
│  │  ViolationReporter │      │  FixSuggester          │        │
│  │                    │      │                        │        │
│  │  • report()        │      │  • suggest()           │        │
│  │  • format()        │      │  • autoFix()           │        │
│  └────────────────────┘      └────────────────────────┘        │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

#### ディレクトリ構造（既存policyパッケージ構造に準拠）

```
packages/policy/src/
├── non-negotiables/
│   ├── types.ts                    # 型定義
│   ├── NonNegotiablesEngine.ts     # メインエンジン
│   ├── RuleLoader.ts               # ルール読み込み
│   ├── rules/
│   │   ├── HackDetectionRule.ts    # ハック検出
│   │   ├── SpecViolationRule.ts    # 仕様違反検出
│   │   ├── ExceptionDetectionRule.ts # 未処理例外検出
│   │   └── index.ts
│   └── index.ts
└── index.ts                        # バレルエクスポート
```

#### インターフェース定義（既存Policy型に準拠）

```typescript
// packages/policy/src/non-negotiables/types.ts

import type { Policy, PolicyResult, ValidationContext, Severity } from '../index.js';

/**
 * Non-negotiablesルール（既存Policy型を拡張）
 * @trace REQ-FR-020
 */
export interface NonNegotiableRule extends Policy {
  /** ルールカテゴリ */
  ruleCategory: 'hack' | 'spec-violation' | 'unhandled-exception' | 'custom';
  /** 対象言語 */
  languages: ('typescript' | 'javascript' | 'rust' | 'python')[];
  /** パターン（正規表現またはAST検査関数） */
  pattern: RegExp | ((code: string, filePath: string) => boolean);
  /** 除外パス */
  excludePaths?: string[];
}

/**
 * ハック検出パターン
 * @trace REQ-FR-021
 */
export interface HackPattern {
  readonly type: 'hostname-check' | 'magic-number' | 'selector-hack' | 'url-specific';
  readonly pattern: RegExp;
  readonly description: string;
}

/**
 * 言語別例外検出ルール
 * @trace REQ-FR-023
 */
export interface ExceptionDetectionConfig {
  readonly language: 'typescript' | 'javascript' | 'rust' | 'python';
  readonly patterns: {
    readonly unhandledThrow: RegExp;
    readonly unhandledPromise: RegExp;
    readonly unsafeTypeCast: RegExp;
    readonly panic?: RegExp;        // Rust only
    readonly bareRaise?: RegExp;    // Python only
  };
  readonly excludePaths: string[];
}

/**
 * Non-negotiablesエンジン
 * 既存IPolicyEngineを拡張
 */
export interface INonNegotiablesEngine {
  /** ルールを読み込む */
  loadRules(configPath: string): Promise<void>;

  /** コードを検証 */
  validateCode(context: ValidationContext): Promise<PolicyResult>;

  /** 設計成果物を検証（Phase 2用） */
  validateDesignArtifacts(artifacts: DesignArtifact[]): Promise<PolicyResult>;

  /** コード成果物を検証（Phase 4用） */
  validateCodeArtifacts(artifacts: CodeArtifact[]): Promise<PolicyResult>;

  /** ディレクトリを検証 */
  validateDirectory(dir: string): Promise<PolicyResult>;

  /** 修正を提案 */
  suggestFix(violation: Violation): string | undefined;
}
```

---

### 4.3 DES-ORCH-003: SingleStepEnforcer（P1）

**トレース**: REQ-FR-090〜092
**ワークフロー統合**: DURING_PHASE (Phase 4のみ)

**設計パターン**: State + Observer

```
┌─────────────────────────────────────────────────────────────────┐
│                     SingleStepEnforcer                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌────────────────────────────────────────────────────┐         │
│  │                  DevLoopStateMachine                │         │
│  │                                                     │         │
│  │   ┌──────┐   ┌──────┐   ┌──────┐   ┌──────┐       │         │
│  │   │  1   │──▶│  2   │──▶│  3   │──▶│  4   │       │         │
│  │   │実行  │   │比較  │   │差異  │   │デバッグ│      │         │
│  │   └──────┘   └──────┘   └──────┘   └──────┘       │         │
│  │       ▲                               │            │         │
│  │       │      ┌──────┐   ┌──────┐     │            │         │
│  │       └──────│  6   │◀──│  5   │◀────┘            │         │
│  │              │検証  │   │修正  │                  │         │
│  │              └──────┘   └──────┘                  │         │
│  └────────────────────────────────────────────────────┘         │
│                           │                                      │
│                           ▼                                      │
│  ┌────────────────────┐      ┌────────────────────────┐        │
│  │  FileChangeWatcher │      │  TestRunner            │        │
│  │                    │      │                        │        │
│  │  • watch()         │      │  • runRelated()        │        │
│  │  • onChange()      │      │  • blockOnFailure()    │        │
│  └────────────────────┘      └────────────────────────┘        │
│                                                                  │
│  ┌────────────────────────────────────────────────────┐         │
│  │                  LoopVisualizer                     │         │
│  │                                                     │         │
│  │  現在の状態: ステップ3「差異を特定する」            │         │
│  │  ┌─────────────────────────────────────────┐       │         │
│  │  │ ✓ 1. 実行する                           │       │         │
│  │  │ ✓ 2. 期待結果と比較する                 │       │         │
│  │  │ → 3. 差異を特定する                     │       │         │
│  │  │   4. デバッグ情報を追加する             │       │         │
│  │  │   5. 修正を実装する                     │       │         │
│  │  │   6. 即座に検証する                     │       │         │
│  │  └─────────────────────────────────────────┘       │         │
│  └────────────────────────────────────────────────────┘         │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

#### インターフェース定義

```typescript
// packages/agent-orchestrator/src/domain/value-objects/DevLoopState.ts

/**
 * 開発ループの状態
 * @trace REQ-FR-092
 */
export type DevLoopStep =
  | 'execute'           // 1. 実行する
  | 'compare'           // 2. 期待結果と比較する
  | 'identify-diff'     // 3. 差異を特定する
  | 'add-debug-info'    // 4. デバッグ情報を追加する
  | 'implement-fix'     // 5. 修正を実装する
  | 'verify';           // 6. 即座に検証する

/**
 * 開発ループ状態
 */
export interface DevLoopState {
  readonly currentStep: DevLoopStep;
  readonly completedSteps: readonly DevLoopStep[];
  readonly changedFiles: readonly string[];
  readonly testResults: readonly TestResult[];
  readonly startedAt: Date;
  readonly workflowId: string;
}

/**
 * バッチ変更検出結果
 * @trace REQ-FR-090
 */
export interface BatchChangeDetection {
  readonly detected: boolean;
  readonly files: readonly string[];
  readonly message: string;
}
```

```typescript
// packages/agent-orchestrator/src/application/SingleStepEnforcer.ts

/**
 * シングルステップ強制サービス
 * @trace REQ-FR-090〜092
 */
export interface ISingleStepEnforcer {
  /** ワークフローに対して有効化 */
  enable(workflowId: string): void;

  /** ワークフローに対して無効化 */
  disable(workflowId: string): void;

  /** 有効化されているか */
  isEnabled(workflowId: string): boolean;

  /** 現在の状態を取得 */
  getState(workflowId: string): DevLoopState | undefined;

  /** ステップを進める */
  advanceStep(workflowId: string): PhaseControllerResult<DevLoopState>;

  /** ファイル変更を記録 */
  recordFileChange(workflowId: string, file: string): PhaseControllerResult<void>;

  /** バッチ変更を検出 */
  detectBatchChange(workflowId: string): BatchChangeDetection;

  /** テストを強制実行 */
  enforceTest(workflowId: string, file: string): Promise<PhaseControllerResult<TestResult>>;

  /** 状態を可視化 */
  visualize(workflowId: string): string;

  /** 状態をリセット */
  reset(workflowId: string): void;
}
```

---

### 4.4 DES-WORKFLOW-002: EvidenceLevelValidator（P1）

**トレース**: REQ-FR-080〜082
**ワークフロー統合**: EXIT_GATE (Phase 5)

**設計パターン**: Strategy + Repository

#### インターフェース定義（既存型に準拠）

```typescript
// packages/workflow-engine/src/domain/value-objects/EvidenceLevel.ts

/**
 * 証拠レベル
 * @trace REQ-FR-080
 */
export type EvidenceLevel = 'best' | 'acceptable' | 'minimum' | 'not-allowed';

/**
 * 証拠レベルメタデータ
 */
export const EVIDENCE_LEVELS: ReadonlyMap<EvidenceLevel, EvidenceLevelMetadata> = new Map([
  ['best', {
    level: 'best',
    label: '🥇 最良',
    description: '自動テスト + 回帰テスト',
    requiredFor: ['bugfix', 'feature'],
  }],
  ['acceptable', {
    level: 'acceptable',
    label: '🥈 許容',
    description: 'ベースラインとの差分比較',
    requiredFor: ['performance'],
  }],
  ['minimum', {
    level: 'minimum',
    label: '🥉 最低限',
    description: '手動確認の記録',
    requiredFor: ['ui'],
  }],
  ['not-allowed', {
    level: 'not-allowed',
    label: '❌ 不可',
    description: 'AIの報告のみ（許可しない）',
    requiredFor: [],
  }],
]);
```

```typescript
// packages/workflow-engine/src/application/EvidenceLevelValidator.ts

/**
 * 証拠データ
 * @trace REQ-FR-081
 */
export interface Evidence {
  readonly id: string;
  readonly taskId: string;
  readonly type: 'test-result' | 'coverage' | 'performance' | 'screenshot' | 'manual';
  readonly before?: unknown;
  readonly after?: unknown;
  readonly delta?: unknown;
  readonly collectedAt: Date;
  readonly metadata?: Record<string, unknown>;
}

/**
 * 証拠検証結果
 */
export interface EvidenceValidationResult {
  readonly valid: boolean;
  readonly level: EvidenceLevel;
  readonly requiredLevel: EvidenceLevel;
  readonly missingEvidence: readonly string[];
  readonly message: string;
}

/**
 * 証拠レベル検証サービス
 * @trace REQ-FR-080〜082
 */
export interface IEvidenceLevelValidator {
  /** タスクに必要な証拠レベルを取得 */
  getRequiredLevel(taskType: TaskType): EvidenceLevel;

  /** 証拠を収集 */
  collectEvidence(taskId: string): Promise<Evidence[]>;

  /** 証拠レベルを検証 */
  validate(taskId: string, evidence: Evidence[]): EvidenceValidationResult;

  /** 全タスクの証拠を検証（QualityGate用） */
  verifyAllTasks(tasks: Task[]): Promise<QualityGateResult>;

  /** 「改善しました」報告を検証 */
  verifyReport(report: string, evidence: Evidence[]): PolicyResult;

  /** 証拠を保存 */
  saveEvidence(evidence: Evidence): Promise<void>;
}
```

---

### 4.5 その他のコンポーネント（P2-P4）

#### DES-POLICY-001: BalanceRuleEngine（P2）
- **ワークフロー統合**: EXIT_GATE (Phase 5)
- **既存パターン準拠**: `IPolicyEngine` を実装

#### DES-WORKFLOW-001: TriageEngine（P2）
- **ワークフロー統合**: ENTRY_GATE (Phase 1, 3)
- **既存パターン準拠**: `QualityGate` として登録

#### DES-CORE-001: MetricsCollector（P3）
- **ワークフロー統合**: GLOBAL Layer
- **既存パターン準拠**: `TypedEventEmitter` を使用

#### DES-PATTERN-001: PatternLearningDB（P3）
- **ワークフロー統合**: GLOBAL Layer
- **既存パターン準拠**: 既存 `PatternLibrary` を拡張

#### DES-CODEGRAPH-001: TestPlacementValidator（P4）
- **ワークフロー統合**: EXIT_GATE (Phase 4)
- **既存パターン準拠**: `QualityGate` として登録

#### DES-ORCH-001: WorkstreamManager（P4）
- **ワークフロー統合**: DURING_PHASE (Phase 4)
- **既存パターン準拠**: 既存 `ParallelExecutor` を拡張

---

## 5. ストレージ設計

### 5.1 ディレクトリ構造

```
project-root/
├── .knowledge/
│   └── graph.json              # Knowledge Store (既存)
├── .metrics/
│   ├── data.json               # メトリクスデータ (NEW)
│   └── baseline.json           # ベースライン値 (NEW)
├── .patterns/
│   └── library.json            # パターンライブラリ (NEW)
├── .evidence/
│   ├── TSK-001/
│   │   ├── before-test.json    # テスト結果(前)
│   │   ├── after-test.json     # テスト結果(後)
│   │   └── coverage-delta.json # カバレッジ差分
│   └── index.json              # 証拠インデックス (NEW)
├── steering/
│   └── project.yml             # 既存設定（拡張）
├── non-negotiables.yml         # Non-negotiablesルール (NEW)
└── workstreams.yml             # ワークストリーム定義 (NEW)
```

### 5.2 設定ファイル

```yaml
# steering/project.yml (拡張)

version: "3.0"

# 既存設定
project:
  name: "my-project"
  language: typescript

# NEW: FastRender知見に基づく設定
fastrender:
  # バランスルール設定
  balance:
    threshold: 10      # カウント対象外の許容割合（%）
    window: 7          # 計測期間（日）
    alertOnConsecutive: 3  # 連続カウント対象外でアラート

  # リソース制限設定
  resources:
    timeouts:
      normalBuild: 600000    # 10分
      singleTest: 120000     # 2分
      fullHarness: 900000    # 15分
      codeGeneration: 300000 # 5分
    memoryLimit: 2147483648  # 2GB
    scopeRequired: true

  # 証拠レベル設定
  evidence:
    retentionDays: 90
    autoCollect: true
    requiredLevels:
      bugfix: best
      feature: best
      performance: acceptable
      ui: minimum

  # シングルステップ設定
  singleStep:
    enabled: true
    enforceTestAfterChange: true
    maxFilesPerChange: 1
```

---

## 6. CLI設計（憲法II条準拠）

### 6.1 新規コマンド

```bash
# リソース制限確認
npx musubix resource status           # 現在のリソース使用状況
npx musubix resource config           # リソース制限設定表示

# Non-negotiables検証
npx musubix policy check-nonneg       # Non-negotiables検証
npx musubix policy check-nonneg --fix # 自動修正付き
npx musubix policy list-nonneg        # ルール一覧

# バランスルール
npx musubix balance status            # 90/10バランス確認
npx musubix balance report            # 週次レポート生成

# メトリクス
npx musubix metrics show              # メトリクスダッシュボード表示
npx musubix metrics export --json     # JSON形式エクスポート
npx musubix metrics baseline          # ベースライン設定

# 証拠管理
npx musubix evidence collect <taskId> # 証拠収集
npx musubix evidence verify <taskId>  # 証拠検証
npx musubix evidence list             # 証拠一覧

# シングルステップ
npx musubix loop status               # 開発ループ状態表示
npx musubix loop reset                # 状態リセット

# トリアージ
npx musubix triage <taskDescription>  # 優先度自動判定
npx musubix triage status             # 未解決P0/P1一覧

# パターン
npx musubix pattern query <context>   # パターン検索
npx musubix pattern list --failures   # 失敗パターン一覧
npx musubix pattern list --success    # 成功パターン一覧

# テスト配置
npx musubix test placement check      # 配置ルール検証
npx musubix test placement fix        # 自動修正

# ワークストリーム
npx musubix workstream list           # ワークストリーム一覧
npx musubix workstream check <file>   # 所属確認
```

---

## 7. MCPツール設計

### 7.1 新規MCPツール（36ツール追加）

命名規則を既存パターンに統一：

| カテゴリ | ツール名 | 要件トレース |
|:--|:--|:--|
| **Agent** | `agent_execute_with_timeout` | REQ-FR-060 |
| | `agent_get_resource_usage` | REQ-FR-061 |
| | `agent_detect_runaway` | REQ-FR-063 |
| | `agent_terminate_process` | REQ-FR-063 |
| | `agent_record_file_change` | REQ-FR-090 |
| | `agent_enforce_single_step` | REQ-FR-091 |
| | `agent_get_loop_state` | REQ-FR-092 |
| | `agent_visualize_loop` | REQ-FR-092 |
| | `agent_define_workstream` | REQ-FR-010 |
| | `agent_check_boundary` | REQ-FR-011 |
| | `agent_detect_conflict` | REQ-FR-012 |
| **Policy** | `policy_check_non_negotiables` | REQ-FR-020 |
| | `policy_detect_hack` | REQ-FR-021 |
| | `policy_detect_spec_violation` | REQ-FR-022 |
| | `policy_detect_unhandled_exception` | REQ-FR-023 |
| | `policy_check_balance` | REQ-FR-002 |
| | `policy_detect_drift` | REQ-FR-003 |
| | `policy_classify_commit` | REQ-FR-001 |
| | `policy_get_balance_stats` | REQ-FR-002 |
| | `policy_generate_balance_report` | REQ-FR-002 |
| **Workflow** | `workflow_triage` | REQ-FR-040 |
| | `workflow_enforce_priority` | REQ-FR-041 |
| | `workflow_get_required_evidence` | REQ-FR-080 |
| | `workflow_collect_evidence` | REQ-FR-081 |
| | `workflow_verify_report` | REQ-FR-082 |
| **Pattern** | `pattern_register_failure` | REQ-FR-050 |
| | `pattern_register_success` | REQ-FR-051 |
| | `pattern_query_by_context` | REQ-FR-051 |
| | `pattern_detect_antipattern` | REQ-FR-052 |
| **Metrics** | `metrics_start_task` | REQ-FR-030 |
| | `metrics_end_task` | REQ-FR-030 |
| | `metrics_record_test` | REQ-FR-030 |
| | `metrics_get_stats` | REQ-FR-031 |
| | `metrics_detect_regression` | REQ-FR-032 |
| **Codegraph** | `codegraph_check_test_placement` | REQ-FR-070 |
| | `codegraph_enforce_regression_test` | REQ-FR-071 |

---

## 8. 非機能要件対応

### 8.1 パフォーマンス要件対応

| 要件ID | 設計対応 |
|:--|:--|
| REQ-NFR-001 | MetricsCollector: イベントベースの軽量収集、バッチ書き込み |
| REQ-NFR-002 | NonNegotiablesEngine: 正規表現キャッシュ、並列検証 |

### 8.2 信頼性要件対応

| 要件ID | 設計対応 |
|:--|:--|
| REQ-NFR-010 | EvidenceStorage: JSON形式でGit管理、TTL設定 |
| REQ-NFR-011 | MetricsCollector: ローカルファイルストレージ、書き込み失敗時リトライ |

### 8.3 セキュリティ要件対応

| 要件ID | 設計対応 |
|:--|:--|
| REQ-NFR-020 | 全データはローカルストレージのみ、エクスポート時のフィルタリング |
| REQ-NFR-021 | ResourceLimiter: 許可コマンドホワイトリスト、確認プロンプト |

### 8.4 互換性要件対応

| 要件ID | 設計対応 |
|:--|:--|
| REQ-NFR-030 | Node.js 20+ 必須、package.json engines設定 |
| REQ-NFR-031 | ProcessMonitorAdapter: OS検出による実装切り替え |

### 8.5 保守性要件対応

| 要件ID | 設計対応 |
|:--|:--|
| REQ-NFR-040 | 全コンポーネント80%以上のテストカバレッジ目標 |
| REQ-NFR-041 | TSDoc形式のドキュメント、@traceタグによるトレーサビリティ |

---

## 9. セルフレビュー

### 9.1 設計チェックリスト

| 観点 | 状態 | 詳細 |
|:--|:--:|:--|
| **トレーサビリティ** | ✅ | 全要件(40件)が設計コンポーネントにマッピング済み |
| **ワークフロー統合** | ✅ | 全コンポーネントの統合ポイントを明記（Section 3） |
| **SOLID原則** | ✅ | インターフェース分離、依存性逆転を適用 |
| **憲法II条** | ✅ | 全機能にCLIコマンドを提供 |
| **憲法VII条** | ✅ | 設計パターン(Strategy, Observer, Repository等)を明記 |
| **既存コードとの整合性** | ✅ | 既存の型・インターフェース・命名規則に準拠 |
| **非機能要件対応** | ✅ | REQ-NFR-001〜041への対応を明記（Section 8） |
| **QualityGate型整合性** | ✅ | ExtendedQualityGate, GateExecutionContext, toStandardGate を追加（Section 3.3） |

### 9.2 v1.0.0からの変更点

1. **Section 3追加**: ワークフロー統合設計（GLOBAL/ENTRY_GATE/DURING_PHASE/EXIT_GATE）
2. **QualityGate統合**: 既存QualityGateRunner への新規ゲート登録設計
3. **PhaseController拡張**: EnhancedPhaseController の設計追加
4. **命名規則統一**: MCPツール名を既存パターンに統一（`resource_*` → `agent_*`等）
5. **ディレクトリ構造修正**: 既存パッケージ構造に準拠
6. **型定義修正**: 既存の`PolicyResult`/`PhaseControllerResult`パターンに準拠
7. **Section 8追加**: 非機能要件対応表

### 9.3 v1.1.0からの変更点（v1.2.0）

1. **Section 3.3.1追加**: `ExtendedQualityGate`型、`GateExecutionContext`型、`GateTiming`型の定義
2. **Section 3.3.2追加**: 各ゲートに`description`、`mandatory`フィールドを追加
3. **Section 3.3.3追加**: `ExtendedQualityGateRunner`クラス、`toStandardGate`変換関数の設計
4. **既存型との互換性**: 拡張ゲートを標準`QualityGate`に変換する仕組みを追加

---

## 10. 承認

| 役割 | 名前 | 日付 | 署名 |
|:--|:--|:--|:--|
| プロダクトオーナー | | | |
| テックリード | | | |
| アーキテクト | | | |

---

## 変更履歴

| バージョン | 日付 | 変更者 | 変更内容 |
|:--|:--|:--|:--|
| 1.0.0 | 2026-01-23 | AI | 初版作成（C4モデル、10コンポーネント設計） |
| 1.1.0 | 2026-01-23 | AI | ワークフロー統合設計追加、既存コード整合性修正、非機能要件対応追加 |
| 1.2.0 | 2026-01-23 | AI | QualityGate型拡張（ExtendedQualityGate, GateExecutionContext, toStandardGate）追加 |
