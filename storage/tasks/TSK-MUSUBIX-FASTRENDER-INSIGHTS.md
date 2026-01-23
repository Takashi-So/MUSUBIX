# MUSUBIX改良 タスク分解書
## FastRender分析知見に基づく機能強化

| 項目 | 内容 |
|------|------|
| **文書ID** | TSK-MUSUBIX-FR-001 |
| **バージョン** | 1.0.0 |
| **作成日** | 2026-01-23 |
| **更新日** | 2026-01-23 |
| **ステータス** | Draft |
| **関連要件** | REQ-MUSUBIX-FR-001 (v1.2.0) |
| **関連設計** | DES-MUSUBIX-FR-001 (v1.2.0) |

---

## 1. タスク概要

### 1.1 実装スコープ

| 優先度 | コンポーネント数 | 総タスク数 | 見積もり工数 |
|:--:|:--:|:--:|:--:|
| P0 | 2 | 12 | 16h |
| P1 | 2 | 10 | 12h |
| P2 | 2 | 10 | 10h |
| P3 | 2 | 10 | 10h |
| P4 | 2 | 10 | 8h |
| **合計** | **10** | **52** | **56h** |

### 1.2 実装順序

```
Phase A (P0): ResourceLimiter → NonNegotiablesEngine
    ↓
Phase B (P1): SingleStepEnforcer → EvidenceLevelValidator
    ↓
Phase C (P2): TriageEngine → BalanceRuleEngine
    ↓
Phase D (P3): MetricsCollector → PatternLearningDB
    ↓
Phase E (P4): WorkstreamManager → TestPlacementValidator
    ↓
Phase F: 統合テスト・ドキュメント
```

---

## 2. P0タスク（必須・最優先）

### 2.1 ResourceLimiter（DES-ORCH-002）

| タスクID | タスク名 | 説明 | 依存 | 工数 |
|:--|:--|:--|:--|:--:|
| TSK-FR-001 | 型定義作成 | `ResourceLimits`, `ResourceUsage`, `ResourceLimiterConfig` 型を定義 | - | 1h |
| TSK-FR-002 | インターフェース定義 | `IResourceLimiter` インターフェースを定義 | TSK-FR-001 | 0.5h |
| TSK-FR-003 | ResourceLimiter実装 | コア実装（checkLimits, recordUsage, getUsageReport） | TSK-FR-002 | 2h |
| TSK-FR-004 | PhaseController統合 | `EnhancedPhaseController` でResourceLimiterをラップ | TSK-FR-003 | 1.5h |
| TSK-FR-005 | ユニットテスト | ResourceLimiter単体テスト（80%カバレッジ） | TSK-FR-003 | 1.5h |
| TSK-FR-006 | 統合テスト | PhaseController統合テスト | TSK-FR-004 | 1h |

**実装ファイル**:
```
packages/agent-orchestrator/src/
├── domain/
│   ├── entities/ResourceLimiter.ts      # TSK-FR-001〜003
│   └── value-objects/ResourceLimits.ts  # TSK-FR-001
├── application/
│   └── EnhancedPhaseController.ts       # TSK-FR-004
└── __tests__/
    ├── ResourceLimiter.test.ts          # TSK-FR-005
    └── EnhancedPhaseController.test.ts  # TSK-FR-006
```

### 2.2 NonNegotiablesEngine（DES-POLICY-002）

| タスクID | タスク名 | 説明 | 依存 | 工数 |
|:--|:--|:--|:--|:--:|
| TSK-FR-007 | 型定義作成 | `NonNegotiableRule`, `ViolationReport`, `NonNegotiablesConfig` 型を定義 | - | 1h |
| TSK-FR-008 | インターフェース定義 | `INonNegotiablesEngine` インターフェースを定義 | TSK-FR-007 | 0.5h |
| TSK-FR-009 | NonNegotiablesEngine実装 | コア実装（validateDesignArtifacts, validateImplementation） | TSK-FR-008 | 2h |
| TSK-FR-010 | QualityGate統合 | `toStandardGate()` で既存QualityGateRunnerに登録 | TSK-FR-009 | 1h |
| TSK-FR-011 | ユニットテスト | NonNegotiablesEngine単体テスト（80%カバレッジ） | TSK-FR-009 | 1.5h |
| TSK-FR-012 | 統合テスト | QualityGate統合テスト | TSK-FR-010 | 1h |

**実装ファイル**:
```
packages/policy/src/
├── domain/
│   ├── entities/NonNegotiablesEngine.ts      # TSK-FR-007〜009
│   └── value-objects/NonNegotiableRule.ts    # TSK-FR-007
├── application/
│   └── non-negotiables-gate.ts               # TSK-FR-010
└── __tests__/
    ├── NonNegotiablesEngine.test.ts          # TSK-FR-011
    └── non-negotiables-gate.test.ts          # TSK-FR-012
```

---

## 3. P1タスク（重要）

### 3.1 SingleStepEnforcer（DES-ORCH-003）

| タスクID | タスク名 | 説明 | 依存 | 工数 |
|:--|:--|:--|:--|:--:|
| TSK-FR-013 | 型定義作成 | `StepDefinition`, `StepExecutionResult`, `SingleStepConfig` 型を定義 | - | 1h |
| TSK-FR-014 | インターフェース定義 | `ISingleStepEnforcer` インターフェースを定義 | TSK-FR-013 | 0.5h |
| TSK-FR-015 | SingleStepEnforcer実装 | コア実装（enforceStep, validateStepCompletion） | TSK-FR-014 | 2h |
| TSK-FR-016 | PhaseController統合 | DURING_PHASE層でPhase 4実行中に適用 | TSK-FR-015, TSK-FR-004 | 1h |
| TSK-FR-017 | ユニットテスト | SingleStepEnforcer単体テスト（80%カバレッジ） | TSK-FR-015 | 1.5h |

**実装ファイル**:
```
packages/agent-orchestrator/src/
├── domain/
│   ├── entities/SingleStepEnforcer.ts       # TSK-FR-013〜015
│   └── value-objects/StepDefinition.ts      # TSK-FR-013
├── application/
│   └── EnhancedPhaseController.ts           # TSK-FR-016（拡張）
└── __tests__/
    └── SingleStepEnforcer.test.ts           # TSK-FR-017
```

### 3.2 EvidenceLevelValidator（DES-WORKFLOW-002）

| タスクID | タスク名 | 説明 | 依存 | 工数 |
|:--|:--|:--|:--|:--:|
| TSK-FR-018 | 型定義作成 | `EvidenceLevel`, `EvidenceRequirement`, `EvidenceValidationResult` 型を定義 | - | 1h |
| TSK-FR-019 | インターフェース定義 | `IEvidenceLevelValidator` インターフェースを定義 | TSK-FR-018 | 0.5h |
| TSK-FR-020 | EvidenceLevelValidator実装 | コア実装（validateEvidence, getRequiredEvidence） | TSK-FR-019 | 2h |
| TSK-FR-021 | QualityGate統合 | EXIT_GATE層でPhase 5完了時に検証 | TSK-FR-020 | 1h |
| TSK-FR-022 | ユニットテスト | EvidenceLevelValidator単体テスト（80%カバレッジ） | TSK-FR-020 | 1.5h |

**実装ファイル**:
```
packages/workflow-engine/src/
├── domain/
│   ├── entities/EvidenceLevelValidator.ts   # TSK-FR-018〜020
│   └── value-objects/EvidenceLevel.ts       # TSK-FR-018
├── application/
│   └── quality-gates/evidence-gate.ts       # TSK-FR-021
└── __tests__/
    └── EvidenceLevelValidator.test.ts       # TSK-FR-022
```

---

## 4. P2タスク（標準）

### 4.1 TriageEngine（DES-WORKFLOW-001）

| タスクID | タスク名 | 説明 | 依存 | 工数 |
|:--|:--|:--|:--|:--:|
| TSK-FR-023 | 型定義作成 | `TriageResult`, `PriorityLevel`, `TriageConfig` 型を定義 | - | 1h |
| TSK-FR-024 | インターフェース定義 | `ITriageEngine` インターフェースを定義 | TSK-FR-023 | 0.5h |
| TSK-FR-025 | TriageEngine実装 | コア実装（checkPriorityBlocking, triageTask） | TSK-FR-024 | 1.5h |
| TSK-FR-026 | QualityGate統合 | ENTRY_GATE層でPhase 1, 3開始時に検証 | TSK-FR-025 | 1h |
| TSK-FR-027 | ユニットテスト | TriageEngine単体テスト（80%カバレッジ） | TSK-FR-025 | 1h |

**実装ファイル**:
```
packages/workflow-engine/src/
├── domain/
│   ├── entities/TriageEngine.ts             # TSK-FR-023〜025
│   └── value-objects/PriorityLevel.ts       # TSK-FR-023
├── application/
│   └── quality-gates/triage-gate.ts         # TSK-FR-026
└── __tests__/
    └── TriageEngine.test.ts                 # TSK-FR-027
```

### 4.2 BalanceRuleEngine（DES-POLICY-001）

| タスクID | タスク名 | 説明 | 依存 | 工数 |
|:--|:--|:--|:--|:--:|
| TSK-FR-028 | 型定義作成 | `BalanceRule`, `BalanceMetrics`, `BalanceConfig` 型を定義 | - | 1h |
| TSK-FR-029 | インターフェース定義 | `IBalanceRuleEngine` インターフェースを定義 | TSK-FR-028 | 0.5h |
| TSK-FR-030 | BalanceRuleEngine実装 | コア実装（evaluateBalance, getBalanceReport） | TSK-FR-029 | 1.5h |
| TSK-FR-031 | QualityGate統合 | EXIT_GATE層でPhase 5完了時に検証 | TSK-FR-030 | 1h |
| TSK-FR-032 | ユニットテスト | BalanceRuleEngine単体テスト（80%カバレッジ） | TSK-FR-030 | 1h |

**実装ファイル**:
```
packages/policy/src/
├── domain/
│   ├── entities/BalanceRuleEngine.ts        # TSK-FR-028〜030
│   └── value-objects/BalanceRule.ts         # TSK-FR-028
├── application/
│   └── quality-gates/balance-gate.ts        # TSK-FR-031
└── __tests__/
    └── BalanceRuleEngine.test.ts            # TSK-FR-032
```

---

## 5. P3タスク（追加機能）

### 5.1 MetricsCollector（DES-CORE-001）

| タスクID | タスク名 | 説明 | 依存 | 工数 |
|:--|:--|:--|:--|:--:|
| TSK-FR-033 | 型定義作成 | `Metric`, `MetricType`, `MetricsReport` 型を定義 | - | 1h |
| TSK-FR-034 | インターフェース定義 | `IMetricsCollector` インターフェースを定義 | TSK-FR-033 | 0.5h |
| TSK-FR-035 | MetricsCollector実装 | コア実装（collect, aggregate, export） | TSK-FR-034 | 2h |
| TSK-FR-036 | PhaseController統合 | GLOBAL層でイベントリスナーとして登録 | TSK-FR-035, TSK-FR-004 | 1h |
| TSK-FR-037 | ユニットテスト | MetricsCollector単体テスト（80%カバレッジ） | TSK-FR-035 | 1.5h |

**実装ファイル**:
```
packages/core/src/
├── metrics/
│   ├── MetricsCollector.ts                  # TSK-FR-033〜035
│   ├── types.ts                             # TSK-FR-033
│   └── index.ts
└── __tests__/
    └── MetricsCollector.test.ts             # TSK-FR-037
```

### 5.2 PatternLearningDB（DES-PATTERN-001）

| タスクID | タスク名 | 説明 | 依存 | 工数 |
|:--|:--|:--|:--|:--:|
| TSK-FR-038 | 型定義作成 | `LearnedPattern`, `PatternCategory`, `LearningEvent` 型を定義 | - | 1h |
| TSK-FR-039 | インターフェース定義 | `IPatternLearningDB` インターフェースを定義 | TSK-FR-038 | 0.5h |
| TSK-FR-040 | PatternLearningDB実装 | コア実装（recordPattern, queryPatterns, getRecommendations） | TSK-FR-039 | 2h |
| TSK-FR-041 | QualityGateRunner統合 | GLOBAL層でイベントリスナーとして登録 | TSK-FR-040 | 1h |
| TSK-FR-042 | ユニットテスト | PatternLearningDB単体テスト（80%カバレッジ） | TSK-FR-040 | 1.5h |

**実装ファイル**:
```
packages/pattern-mcp/src/
├── domain/
│   ├── entities/PatternLearningDB.ts        # TSK-FR-038〜040
│   └── value-objects/LearnedPattern.ts      # TSK-FR-038
├── application/
│   └── pattern-learning-listener.ts         # TSK-FR-041
└── __tests__/
    └── PatternLearningDB.test.ts            # TSK-FR-042
```

---

## 6. P4タスク（将来対応）

### 6.1 WorkstreamManager（DES-ORCH-001）

| タスクID | タスク名 | 説明 | 依存 | 工数 |
|:--|:--|:--|:--|:--:|
| TSK-FR-043 | 型定義作成 | `Workstream`, `WorkstreamStatus`, `WorkstreamConfig` 型を定義 | - | 1h |
| TSK-FR-044 | インターフェース定義 | `IWorkstreamManager` インターフェースを定義 | TSK-FR-043 | 0.5h |
| TSK-FR-045 | WorkstreamManager実装 | コア実装（createWorkstream, assignTask, getStatus） | TSK-FR-044 | 1.5h |
| TSK-FR-046 | ParallelExecutor統合 | DURING_PHASE層で並列実行を管理 | TSK-FR-045 | 1h |
| TSK-FR-047 | ユニットテスト | WorkstreamManager単体テスト（80%カバレッジ） | TSK-FR-045 | 1h |

**実装ファイル**:
```
packages/agent-orchestrator/src/
├── domain/
│   ├── entities/WorkstreamManager.ts        # TSK-FR-043〜045
│   └── value-objects/Workstream.ts          # TSK-FR-043
├── application/
│   └── ParallelExecutor.ts                  # TSK-FR-046（拡張）
└── __tests__/
    └── WorkstreamManager.test.ts            # TSK-FR-047
```

### 6.2 TestPlacementValidator（DES-CODEGRAPH-001）

| タスクID | タスク名 | 説明 | 依存 | 工数 |
|:--|:--|:--|:--|:--:|
| TSK-FR-048 | 型定義作成 | `TestPlacement`, `PlacementRule`, `PlacementValidationResult` 型を定義 | - | 1h |
| TSK-FR-049 | インターフェース定義 | `ITestPlacementValidator` インターフェースを定義 | TSK-FR-048 | 0.5h |
| TSK-FR-050 | TestPlacementValidator実装 | コア実装（validatePlacement, suggestPlacement） | TSK-FR-049 | 1.5h |
| TSK-FR-051 | QualityGate統合 | EXIT_GATE層でPhase 4完了時に検証 | TSK-FR-050 | 1h |
| TSK-FR-052 | ユニットテスト | TestPlacementValidator単体テスト（80%カバレッジ） | TSK-FR-050 | 1h |

**実装ファイル**:
```
packages/codegraph/src/
├── domain/
│   ├── entities/TestPlacementValidator.ts   # TSK-FR-048〜050
│   └── value-objects/TestPlacement.ts       # TSK-FR-048
├── application/
│   └── quality-gates/test-placement-gate.ts # TSK-FR-051
└── __tests__/
    └── TestPlacementValidator.test.ts       # TSK-FR-052
```

---

## 7. 共通タスク

### 7.1 基盤タスク

| タスクID | タスク名 | 説明 | 依存 | 工数 |
|:--|:--|:--|:--|:--:|
| TSK-FR-053 | ExtendedQualityGate型 | Section 3.3.1の型定義を実装 | - | 1h |
| TSK-FR-054 | toStandardGate関数 | 拡張ゲート→標準ゲート変換関数 | TSK-FR-053 | 0.5h |
| TSK-FR-055 | ExtendedQualityGateRunner | 拡張ゲートランナークラス実装 | TSK-FR-054 | 1.5h |
| TSK-FR-056 | 基盤テスト | 共通基盤のユニットテスト | TSK-FR-055 | 1h |

**実装ファイル**:
```
packages/workflow-engine/src/
├── domain/
│   └── entities/ExtendedQualityGate.ts      # TSK-FR-053〜054
├── application/
│   └── ExtendedQualityGateRunner.ts         # TSK-FR-055
└── __tests__/
    └── ExtendedQualityGate.test.ts          # TSK-FR-056
```

### 7.2 統合・ドキュメントタスク

| タスクID | タスク名 | 説明 | 依存 | 工数 |
|:--|:--|:--|:--|:--:|
| TSK-FR-057 | E2E統合テスト | 全コンポーネントの統合テスト | 全P0〜P4タスク | 3h |
| TSK-FR-058 | MCPツール登録 | 新規MCPツールの登録 | 全P0〜P4タスク | 2h |
| TSK-FR-059 | APIドキュメント | TSDoc/JSDoc記述 | 全P0〜P4タスク | 2h |
| TSK-FR-060 | ユーザーガイド更新 | USER-GUIDE.mdの更新 | TSK-FR-059 | 1h |

---

## 8. 依存関係図

```
TSK-FR-053 (ExtendedQualityGate型)
    │
    ├──▶ TSK-FR-054 (toStandardGate)
    │        │
    │        └──▶ TSK-FR-055 (ExtendedQualityGateRunner)
    │                  │
    │                  └──▶ TSK-FR-056 (基盤テスト)
    │
    ├──▶ TSK-FR-010 (NonNegotiables QualityGate統合)
    ├──▶ TSK-FR-021 (Evidence QualityGate統合)
    ├──▶ TSK-FR-026 (Triage QualityGate統合)
    ├──▶ TSK-FR-031 (Balance QualityGate統合)
    └──▶ TSK-FR-051 (TestPlacement QualityGate統合)

TSK-FR-001〜006 (ResourceLimiter)
    │
    └──▶ TSK-FR-004 (EnhancedPhaseController)
              │
              ├──▶ TSK-FR-016 (SingleStepEnforcer統合)
              └──▶ TSK-FR-036 (MetricsCollector統合)
```

---

## 9. 実装スケジュール

| フェーズ | 期間 | タスク | マイルストーン |
|:--|:--|:--|:--|
| **Phase A** | Day 1-2 | TSK-FR-053〜056, TSK-FR-001〜012 | P0コンポーネント完了 |
| **Phase B** | Day 3-4 | TSK-FR-013〜022 | P1コンポーネント完了 |
| **Phase C** | Day 5 | TSK-FR-023〜032 | P2コンポーネント完了 |
| **Phase D** | Day 6 | TSK-FR-033〜042 | P3コンポーネント完了 |
| **Phase E** | Day 7 | TSK-FR-043〜052 | P4コンポーネント完了 |
| **Phase F** | Day 8 | TSK-FR-057〜060 | 統合・ドキュメント完了 |

---

## 10. 品質基準

| 項目 | 基準 |
|:--|:--|
| **ユニットテストカバレッジ** | 80%以上 |
| **統合テスト** | 全QualityGate統合パスをカバー |
| **型安全性** | strict mode, no any |
| **ドキュメント** | 全public APIにTSDoc |
| **憲法準拠** | Article III（テスト先行）、V（トレーサビリティ） |

---

## 11. セルフレビュー

| 観点 | 状態 | 詳細 |
|:--|:--:|:--|
| **設計対応** | ✅ | DES-MUSUBIX-FR-001 v1.2.0の全コンポーネントをタスク化 |
| **依存関係** | ✅ | TSK-FR-053（基盤）→ 各コンポーネントの依存を明確化 |
| **工数見積もり** | ✅ | 各タスク0.5〜3h、合計56h |
| **実装順序** | ✅ | P0→P1→P2→P3→P4の優先度順 |
| **テスト計画** | ✅ | 各コンポーネントにユニットテスト、最後にE2E |
| **ファイル配置** | ✅ | 既存パッケージ構造（domain/application/__tests__）に準拠 |

---

## 変更履歴

| バージョン | 日付 | 変更者 | 変更内容 |
|:--|:--|:--|:--|
| 1.0.0 | 2026-01-23 | AI | 初版作成（60タスク、56h見積もり） |
