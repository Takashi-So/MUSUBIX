# TSK-ENHANCEMENT-v2.4.0: Claude Code統合タスク分解

**Version**: 2.4.0  
**Created**: 2026-01-11  
**Status**: Draft  
**Traceability**: 
- REQ: REQ-ENHANCEMENT-v2.4.0-Claude-Code-Integration.md
- DES: DES-ENHANCEMENT-v2.4.0-Claude-Code-Integration.md

---

## 1. タスク概要

### 1.1 スコープ

| 項目 | 内容 |
|------|------|
| 新規パッケージ | 3（agent-orchestrator, workflow-engine, skill-manager） |
| 新規MCPツール | 11 |
| 推定総工数 | 40-50時間 |
| 依存関係 | core, yata-client, mcp-server |

### 1.2 トレーサビリティマトリクス

| 設計ID | タスクID | 概要 |
|--------|---------|------|
| DES-SDD-001 | TSK-AGENT-001 | ComplexityAnalyzer実装 |
| DES-SDD-002 | TSK-AGENT-002 | SubagentDispatcher実装 |
| DES-SDD-003 | TSK-AGENT-003 | ContextManager実装 |
| DES-PAD-001 | TSK-AGENT-004 | DependencyAnalyzer実装 |
| DES-PAD-002 | TSK-AGENT-005 | ParallelExecutor実装 |
| DES-PAD-003 | TSK-AGENT-006 | ResultAggregator実装 |
| DES-ORCH-001 | TSK-WORKFLOW-001 | PhaseController実装 |
| DES-ORCH-002 | TSK-WORKFLOW-002 | StateTracker実装 |
| DES-ORCH-003 | TSK-WORKFLOW-003 | QualityGateRunner実装 |
| DES-SKILL-001 | TSK-SKILL-001 | SkillValidator実装 |
| DES-SKILL-002 | TSK-SKILL-002 | SkillLoader/Registry実装 |
| DES-MCP-001 | TSK-MCP-001 | Agent Tools実装 |
| DES-MCP-002 | TSK-MCP-002 | Workflow Tools実装 |
| DES-MCP-003 | TSK-MCP-003 | Skill Tools実装 |
| DES-NFR-001 | TSK-TEST-001 | パフォーマンステスト |
| DES-NFR-002 | TSK-TEST-002 | 後方互換性テスト |

---

## 2. パッケージスキャフォールド

### TSK-SCAFFOLD-001: agent-orchestratorパッケージ作成

**優先度**: P0（必須）  
**工数**: 1時間  
**依存**: なし

**タスク内容**:
1. `packages/agent-orchestrator/` ディレクトリ作成
2. `package.json` 作成（`@nahisaho/musubix-agent-orchestrator`）
3. `tsconfig.json` 作成（tsconfig.base.json継承）
4. ディレクトリ構造作成:
   ```
   src/
   ├── domain/
   │   ├── entities/
   │   ├── value-objects/
   │   └── services/
   ├── application/
   ├── infrastructure/
   └── interface/
       ├── cli/
       └── mcp/
   ```
5. `vitest.config.ts` 作成
6. エントリーポイント `src/index.ts` 作成

**受入基準**:
- [ ] `npm run build` が成功
- [ ] `npm run test` が実行可能（テストなしでもOK）
- [ ] workspaceから認識される

---

### TSK-SCAFFOLD-002: workflow-engineパッケージ作成

**優先度**: P0（必須）  
**工数**: 1時間  
**依存**: なし

**タスク内容**:
1. `packages/workflow-engine/` ディレクトリ作成
2. `package.json` 作成（`@nahisaho/musubix-workflow-engine`）
3. `tsconfig.json` 作成
4. ディレクトリ構造作成（TSK-SCAFFOLD-001と同様）
5. `vitest.config.ts` 作成
6. エントリーポイント作成

**受入基準**:
- [ ] `npm run build` が成功
- [ ] workspaceから認識される

---

### TSK-SCAFFOLD-003: skill-managerパッケージ作成

**優先度**: P0（必須）  
**工数**: 1時間  
**依存**: なし

**タスク内容**:
1. `packages/skill-manager/` ディレクトリ作成
2. `package.json` 作成（`@nahisaho/musubix-skill-manager`）
3. `tsconfig.json` 作成
4. ディレクトリ構造作成
5. `vitest.config.ts` 作成
6. エントリーポイント作成

**受入基準**:
- [ ] `npm run build` が成功
- [ ] workspaceから認識される

---

## 3. Agent Orchestratorタスク

### TSK-AGENT-001: ComplexityAnalyzer実装

**優先度**: P0（必須）  
**工数**: 3時間  
**依存**: TSK-SCAFFOLD-001  
**トレーサビリティ**: DES-SDD-001 → REQ-SDD-001

**タスク内容**:

1. **Value Objects作成** (30分)
   - `src/domain/value-objects/ComplexityScore.ts`
   - `src/domain/value-objects/ComplexityFactor.ts`

2. **エンティティ作成** (30分)
   - `src/domain/entities/Task.ts`

3. **ドメインサービス実装** (1時間)
   - `src/domain/services/ComplexityAnalyzer.ts`
   - 5つの複雑度因子（scope, dependencies, fileCount, testCoverage, uncertainty）
   - 閾値判定（デフォルト: 7）

4. **テスト作成** (1時間)
   - `tests/domain/services/ComplexityAnalyzer.test.ts`
   - 低複雑度タスク（score < 7）→ 分解不要
   - 高複雑度タスク（score >= 7）→ 分解推奨

**受入基準**:
- [ ] ComplexityScore Value Objectが不変
- [ ] 複雑度スコアが1-10の範囲
- [ ] 閾値7以上で `shouldDecompose()` がtrue
- [ ] テストカバレッジ90%以上

---

### TSK-AGENT-002: SubagentDispatcher実装

**優先度**: P0（必須）  
**工数**: 4時間  
**依存**: TSK-AGENT-001  
**トレーサビリティ**: DES-SDD-002 → REQ-SDD-002

**タスク内容**:

1. **Value Objects作成** (30分)
   - `src/domain/value-objects/AgentRole.ts`
   - `src/domain/value-objects/SubagentSpec.ts`

2. **Applicationサービス実装** (2時間)
   - `src/application/SubagentDispatcher.ts`
   - タスク分解ロジック（役割別サブタスク生成）
   - プロンプト生成

3. **Infrastructureアダプタ実装** (1時間)
   - `src/infrastructure/SubagentAdapter.ts`
   - `runSubagent`ツール呼び出しラッパー

4. **テスト作成** (30分)
   - 分解テスト
   - 役割割り当てテスト

**受入基準**:
- [ ] 5つの役割（requirements, design, implementation, test, review）をサポート
- [ ] 各サブエージェントに適切なプロンプトが生成される
- [ ] 並列実行可能なタスクが識別される

---

### TSK-AGENT-003: ContextManager実装

**優先度**: P0（必須）  
**工数**: 3時間  
**依存**: TSK-SCAFFOLD-001  
**トレーサビリティ**: DES-SDD-003 → REQ-SDD-003

**タスク内容**:

1. **エンティティ作成** (30分)
   - `src/domain/entities/ExecutionContext.ts`
   - `src/domain/entities/Artifact.ts`

2. **Applicationサービス実装** (1.5時間)
   - `src/application/ContextManager.ts`
   - コンテキスト作成・共有・マージ

3. **Infrastructure実装** (30分)
   - `src/infrastructure/YATAContextStore.ts`
   - YATA経由の永続化（オプショナル）

4. **テスト作成** (30分)
   - コンテキスト共有テスト
   - マージテスト

**受入基準**:
- [ ] 親子コンテキストの継承が機能
- [ ] 複数コンテキストのマージが機能
- [ ] コンテキスト永続化が機能

---

### TSK-AGENT-004: DependencyAnalyzer実装

**優先度**: P1（重要）  
**工数**: 2時間  
**依存**: TSK-AGENT-002  
**トレーサビリティ**: DES-PAD-001 → REQ-PAD-001

**タスク内容**:

1. **ドメインサービス実装** (1時間)
   - `src/domain/services/DependencyAnalyzer.ts`
   - タスク間依存関係の検出
   - 依存グラフ構築

2. **テスト作成** (1時間)
   - 独立タスク検出テスト
   - 依存タスク検出テスト

**受入基準**:
- [ ] 独立タスクが正しく識別される
- [ ] 依存グラフがDAGとして構築される
- [ ] 循環依存が検出・報告される

---

### TSK-AGENT-005: ParallelExecutor実装

**優先度**: P1（重要）  
**工数**: 3時間  
**依存**: TSK-AGENT-004  
**トレーサビリティ**: DES-PAD-002 → REQ-PAD-002

**タスク内容**:

1. **Applicationサービス実装** (2時間)
   - `src/application/ParallelExecutor.ts`
   - Promise.all による並列実行
   - 同時実行数制限（デフォルト: 5）
   - タイムアウト処理

2. **テスト作成** (1時間)
   - 並列実行テスト
   - タイムアウトテスト
   - エラーハンドリングテスト

**受入基準**:
- [ ] 独立タスクが並列実行される
- [ ] 同時実行数が制限される
- [ ] 1タスク失敗時も他タスクは継続

---

### TSK-AGENT-006: ResultAggregator実装

**優先度**: P1（重要）  
**工数**: 2時間  
**依存**: TSK-AGENT-005  
**トレーサビリティ**: DES-PAD-003 → REQ-PAD-003

**タスク内容**:

1. **Applicationサービス実装** (1.5時間)
   - `src/application/ResultAggregator.ts`
   - 結果統合ロジック
   - コンフリクト検出

2. **テスト作成** (30分)
   - 結果統合テスト
   - コンフリクト検出テスト

**受入基準**:
- [ ] 複数結果が正しく統合される
- [ ] コンフリクトが検出・報告される

---

## 4. Workflow Engineタスク

### TSK-WORKFLOW-001: PhaseController実装

**優先度**: P0（必須）  
**工数**: 4時間  
**依存**: TSK-SCAFFOLD-002  
**トレーサビリティ**: DES-ORCH-001 → REQ-ORCH-001

**タスク内容**:

1. **Value Objects作成** (30分)
   - `src/domain/value-objects/PhaseType.ts`
   - `src/domain/value-objects/ApprovalStatus.ts`

2. **エンティティ作成** (30分)
   - `src/domain/entities/Phase.ts`
   - `src/domain/entities/Workflow.ts`

3. **Applicationサービス実装** (2時間)
   - `src/application/PhaseController.ts`
   - 有効遷移マップ（Phase 2→4直接遷移禁止）
   - 遷移条件チェック

4. **テスト作成** (1時間)
   - 有効遷移テスト
   - 無効遷移拒否テスト（Phase 2→4）

**受入基準**:
- [ ] Phase 1→2→3→4→5の順序遷移が機能
- [ ] Phase 2→Phase 4直接遷移が拒否される
- [ ] 承認なしの遷移が拒否される

---

### TSK-WORKFLOW-002: StateTracker実装

**優先度**: P0（必須）  
**工数**: 3時間  
**依存**: TSK-SCAFFOLD-002  
**トレーサビリティ**: DES-ORCH-002 → REQ-ORCH-002

**タスク内容**:

1. **Value Objects作成** (30分)
   - `src/domain/value-objects/TaskStatus.ts`

2. **エンティティ作成** (30分)
   - `src/domain/entities/TaskState.ts`

3. **Applicationサービス実装** (1.5時間)
   - `src/application/StateTracker.ts`
   - 状態追跡
   - 進捗計算
   - イベント購読

4. **テスト作成** (30分)
   - 状態遷移テスト
   - 進捗計算テスト

**受入基準**:
- [ ] 4状態（not-started, in-progress, completed, failed）が追跡される
- [ ] 進捗率が正しく計算される
- [ ] 状態変更がイベントとして発火される

---

### TSK-WORKFLOW-003: QualityGateRunner実装

**優先度**: P0（必須）  
**工数**: 4時間  
**依存**: TSK-WORKFLOW-001  
**トレーサビリティ**: DES-ORCH-003 → REQ-ORCH-003

**タスク内容**:

1. **エンティティ作成** (30分)
   - `src/domain/entities/QualityGate.ts`
   - `src/domain/entities/QualityCheck.ts`

2. **Applicationサービス実装** (2.5時間)
   - `src/application/QualityGateRunner.ts`
   - フェーズ別品質ゲート定義
   - チェック実行

3. **デフォルトチェック実装** (30分)
   - EARS形式チェック
   - トレーサビリティチェック
   - C4モデルチェック

4. **テスト作成** (30分)
   - 品質ゲート通過テスト
   - 品質ゲート失敗テスト

**受入基準**:
- [ ] 各フェーズに品質ゲートが定義される
- [ ] 必須チェック失敗で遷移ブロック
- [ ] チェック結果が詳細に報告される

---

## 5. Skill Managerタスク

### TSK-SKILL-001: SkillValidator実装

**優先度**: P1（重要）  
**工数**: 2時間  
**依存**: TSK-SCAFFOLD-003  
**トレーサビリティ**: DES-SKILL-001 → REQ-SKILL-001

**タスク内容**:

1. **ドメインロジック実装** (1時間)
   - `src/domain/services/SkillValidator.ts`
   - SKILL.md 500行制限チェック
   - ディレクトリ構造チェック

2. **テスト作成** (1時間)
   - 有効スキル検証テスト
   - 無効スキル検証テスト（500行超過）

**受入基準**:
- [ ] 500行超過が検出される
- [ ] 必須ディレクトリ欠如が検出される
- [ ] 検証結果が詳細に報告される

---

### TSK-SKILL-002: SkillLoader/Registry実装

**優先度**: P1（重要）  
**工数**: 3時間  
**依存**: TSK-SKILL-001  
**トレーサビリティ**: DES-SKILL-002 → REQ-SKILL-002

**タスク内容**:

1. **エンティティ作成** (30分)
   - `src/domain/entities/Skill.ts`
   - `src/domain/value-objects/SkillMetadata.ts`

2. **Applicationサービス実装** (1.5時間)
   - `src/application/SkillLoader.ts`
   - `src/application/SkillRegistry.ts`

3. **Infrastructure実装** (30分)
   - `src/infrastructure/FileSystemSkillStore.ts`

4. **テスト作成** (30分)
   - スキル読み込みテスト
   - レジストリ検索テスト

**受入基準**:
- [ ] `.github/skills/`からスキルが読み込める
- [ ] スキルがレジストリに登録される
- [ ] 名前・タグでスキルが検索できる

---

## 6. MCPツール実装タスク

### TSK-MCP-001: Agent Tools実装

**優先度**: P0（必須）  
**工数**: 3時間  
**依存**: TSK-AGENT-001〜006  
**トレーサビリティ**: DES-MCP-001 → REQ-MCP-001

**タスク内容**:

1. **ツール定義作成** (2時間)
   - `packages/mcp-server/src/tools/agent-tools.ts`
   - `agent_analyze_complexity`
   - `agent_dispatch_subagent`
   - `agent_merge_context`
   - `agent_list_roles`

2. **MCPサーバー統合** (30分)
   - `src/index.ts` への登録

3. **テスト作成** (30分)
   - ツール呼び出しテスト

**受入基準**:
- [ ] 4つのagent_*ツールが登録される
- [ ] 各ツールにアノテーションがある
- [ ] ツールが正しく動作する

---

### TSK-MCP-002: Workflow Tools実装

**優先度**: P0（必須）  
**工数**: 3時間  
**依存**: TSK-WORKFLOW-001〜003  
**トレーサビリティ**: DES-MCP-002 → REQ-MCP-002

**タスク内容**:

1. **ツール定義作成** (2時間)
   - `packages/mcp-server/src/tools/workflow-tools.ts`
   - `workflow_get_status`
   - `workflow_transition_phase`
   - `workflow_run_quality_gate`
   - `workflow_request_approval`

2. **MCPサーバー統合** (30分)
   - `src/index.ts` への登録

3. **テスト作成** (30分)
   - ツール呼び出しテスト

**受入基準**:
- [ ] 4つのworkflow_*ツールが登録される
- [ ] 各ツールにアノテーションがある
- [ ] ツールが正しく動作する

---

### TSK-MCP-003: Skill Tools実装

**優先度**: P1（重要）  
**工数**: 2時間  
**依存**: TSK-SKILL-001〜002  
**トレーサビリティ**: DES-MCP-003 → REQ-MCP-003

**タスク内容**:

1. **ツール定義作成** (1.5時間)
   - `packages/mcp-server/src/tools/skill-tools.ts`
   - `skill_load`
   - `skill_validate`
   - `skill_list`

2. **MCPサーバー統合** (15分)
   - `src/index.ts` への登録

3. **テスト作成** (15分)
   - ツール呼び出しテスト

**受入基準**:
- [ ] 3つのskill_*ツールが登録される
- [ ] 各ツールにアノテーションがある

---

## 7. テスト・品質タスク

### TSK-TEST-001: パフォーマンステスト

**優先度**: P1（重要）  
**工数**: 2時間  
**依存**: TSK-MCP-001〜003  
**トレーサビリティ**: DES-NFR-001 → REQ-NFR-001

**タスク内容**:

1. **ベンチマークテスト作成** (1.5時間)
   - `tests/benchmark/performance.bench.ts`
   - 複雑度分析 < 200ms
   - サブエージェント起動 < 500ms
   - フェーズ遷移 < 1s

2. **CI統合** (30分)
   - GitHub Actions への追加

**受入基準**:
- [ ] 各操作がSLA内で完了
- [ ] CIでパフォーマンス劣化が検出される

---

### TSK-TEST-002: 後方互換性テスト

**優先度**: P0（必須）  
**工数**: 2時間  
**依存**: TSK-MCP-001〜003  
**トレーサビリティ**: DES-NFR-002 → REQ-NFR-002

**タスク内容**:

1. **互換性テスト作成** (1.5時間)
   - `tests/integration/backward-compatibility.test.ts`
   - 既存`sdd_*`ツール動作確認
   - 既存CLIコマンド動作確認

2. **回帰テストスイート** (30分)
   - 既存テストが全合格することを確認

**受入基準**:
- [ ] 既存2100+テストが全合格
- [ ] 既存`sdd_*`ツールが変更なく動作
- [ ] 既存CLIコマンドが変更なく動作

---

## 8. 実行順序（依存関係DAG）

```
Phase 1: スキャフォールド（並列実行可能）
┌─────────────────┬─────────────────┬─────────────────┐
│ TSK-SCAFFOLD-001│ TSK-SCAFFOLD-002│ TSK-SCAFFOLD-003│
│ agent-orchestr. │ workflow-engine │ skill-manager   │
└────────┬────────┴────────┬────────┴────────┬────────┘
         │                 │                 │
Phase 2: Domain層実装（並列実行可能）
         │                 │                 │
         ▼                 ▼                 ▼
┌─────────────────┐ ┌─────────────────┐ ┌─────────────────┐
│ TSK-AGENT-001   │ │ TSK-WORKFLOW-001│ │ TSK-SKILL-001   │
│ TSK-AGENT-003   │ │ TSK-WORKFLOW-002│ │                 │
└────────┬────────┘ └────────┬────────┘ └────────┬────────┘
         │                 │                 │
Phase 3: Application層実装
         │                 │                 │
         ▼                 ▼                 ▼
┌─────────────────┐ ┌─────────────────┐ ┌─────────────────┐
│ TSK-AGENT-002   │ │ TSK-WORKFLOW-003│ │ TSK-SKILL-002   │
│ TSK-AGENT-004   │ │                 │ │                 │
│ TSK-AGENT-005   │ │                 │ │                 │
│ TSK-AGENT-006   │ │                 │ │                 │
└────────┬────────┘ └────────┬────────┘ └────────┬────────┘
         │                 │                 │
Phase 4: MCPツール統合
         │                 │                 │
         ▼                 ▼                 ▼
┌─────────────────┐ ┌─────────────────┐ ┌─────────────────┐
│ TSK-MCP-001     │ │ TSK-MCP-002     │ │ TSK-MCP-003     │
└────────┬────────┘ └────────┬────────┘ └────────┬────────┘
         │                 │                 │
         └─────────────────┼─────────────────┘
                           │
Phase 5: テスト・品質
                           ▼
                  ┌─────────────────┐
                  │ TSK-TEST-001    │
                  │ TSK-TEST-002    │
                  └─────────────────┘
```

---

## 9. タスクサマリー

### タスク数

| カテゴリ | P0（必須） | P1（重要） | 合計 |
|---------|-----------|-----------|------|
| SCAFFOLD | 3 | 0 | 3 |
| AGENT | 3 | 3 | 6 |
| WORKFLOW | 3 | 0 | 3 |
| SKILL | 0 | 2 | 2 |
| MCP | 2 | 1 | 3 |
| TEST | 1 | 1 | 2 |
| **合計** | **12** | **7** | **19** |

### 工数見積もり

| カテゴリ | 工数（時間） |
|---------|-------------|
| SCAFFOLD | 3 |
| AGENT | 17 |
| WORKFLOW | 11 |
| SKILL | 5 |
| MCP | 8 |
| TEST | 4 |
| **合計** | **48時間** |

### 推奨実行順序

1. **Day 1** (8h): TSK-SCAFFOLD-001〜003, TSK-AGENT-001, TSK-WORKFLOW-001
2. **Day 2** (8h): TSK-AGENT-002〜003, TSK-WORKFLOW-002〜003, TSK-SKILL-001
3. **Day 3** (8h): TSK-AGENT-004〜006, TSK-SKILL-002
4. **Day 4** (8h): TSK-MCP-001〜003
5. **Day 5** (8h): TSK-TEST-001〜002, バグ修正、ドキュメント

---

## 10. リスクと対策

| リスク | 影響 | 対策 |
|--------|------|------|
| runSubagent API変更 | 高 | 抽象化レイヤー（SubagentAdapter）で吸収 |
| 既存テスト破壊 | 高 | TSK-TEST-002を早期実行 |
| パフォーマンス未達 | 中 | キャッシュ導入、並列化最適化 |
| スキル構造の複雑化 | 低 | Progressive Disclosureパターン厳守 |

---

**Document ID**: TSK-ENHANCEMENT-v2.4.0  
**Created**: 2026-01-11  
**Author**: AI Agent (GitHub Copilot)  
**Status**: Draft - Awaiting Review
