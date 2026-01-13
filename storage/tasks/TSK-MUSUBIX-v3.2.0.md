# MUSUBIX v3.2.0 タスク分解書
# Expert Delegation System - 実装タスク

**文書ID**: TSK-MUSUBIX-v3.2.0  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.0  
**作成日**: 2026-01-13  
**完了日**: 2026-01-14  
**ステータス**: Completed  
**参照文書**: REQ-MUSUBIX-v3.2.0.md, DES-MUSUBIX-v3.2.0.md

---

## 1. 文書概要

### 1.1 目的

本文書は、DES-MUSUBIX-v3.2.0設計書に基づき、Expert Delegation System実装のためのタスク分解を定義する。

### 1.2 タスク構成

| フェーズ | タスク数 | 見積時間 |
|---------|---------|---------|
| Phase A: 基盤構築 | 3 | 2h |
| Phase B: Provider層 | 4 | 3h |
| Phase C: Expert層 | 9 | 5h |
| Phase D: Trigger層 | 4 | 3h |
| Phase E: Delegation層 | 5 | 4h |
| Phase F: MCP層 | 3 | 3h |
| Phase G: テスト | 5 | 4h |
| Phase H: ドキュメント | 2 | 1h |
| **合計** | **35** | **25h** |

---

## 2. Phase A: 基盤構築

### TSK-A-001: パッケージ初期化

**設計トレース**: DES-MUSUBIX-v3.2.0 Section 7 (ディレクトリ構成)  
**見積時間**: 30分  
**依存**: なし

**作業内容**:
- [ ] `packages/expert-delegation/` ディレクトリ作成
- [ ] `package.json` 作成（@nahisaho/musubix-expert-delegation）
- [ ] `tsconfig.json` 作成
- [ ] `vitest.config.ts` 作成（VS Code APIモックパス設定）

**受入基準**:
- [ ] `npm install` が成功する
- [ ] `npm run build` が成功する（空でも）

---

### TSK-A-002: 共通型定義

**設計トレース**: DES-EXP-001, DES-FMT-001, DES-PRV-001, DES-ERR-001  
**見積時間**: 45分  
**依存**: TSK-A-001

**作業内容**:
- [ ] `src/types/index.ts` 作成
- [ ] `ExpertType` 型定義
- [ ] `ExecutionMode` 型定義
- [ ] `Expert` インターフェース
- [ ] `TriggerPattern` インターフェース
- [ ] `ExpertCapability` インターフェース
- [ ] `DelegationTask` インターフェース
- [ ] `DelegationContext` インターフェース
- [ ] `DelegationResult` インターフェース
- [ ] `TraceLink` インターフェース
- [ ] `ConstitutionViolation` インターフェース

**受入基準**:
- [ ] 型チェックが通る
- [ ] 設計書の型定義と一致

---

### TSK-A-003: エラー型定義

**設計トレース**: DES-ERR-001  
**見積時間**: 30分  
**依存**: TSK-A-001

**作業内容**:
- [ ] `src/types/errors.ts` 作成
- [ ] `DelegationErrorCode` 型定義（11エラーコード）
- [ ] `DelegationError` クラス実装
- [ ] `EscalationResult` インターフェース
- [ ] `DelegationError.isRetryable()` 静的メソッド
- [ ] `DelegationError.fromCode()` 静的メソッド

**受入基準**:
- [ ] 全11エラーコードが定義されている
- [ ] リトライ可能判定が正しく動作

---

## 3. Phase B: Provider層

### TSK-B-001: Providerインターフェース定義

**設計トレース**: DES-PRV-001  
**見積時間**: 30分  
**依存**: TSK-A-002

**作業内容**:
- [ ] `src/providers/provider-interface.ts` 作成
- [ ] `LMProvider` インターフェース
- [ ] `RequestOptions` インターフェース
- [ ] `ProviderResponse` インターフェース
- [ ] `ModelInfo` インターフェース
- [ ] `ModelCriteria` インターフェース

**受入基準**:
- [ ] 設計書のインターフェースと一致

---

### TSK-B-002: VS Code LM Provider実装

**設計トレース**: DES-PRV-001, REQ-PRV-001  
**見積時間**: 1時間  
**依存**: TSK-B-001

**作業内容**:
- [ ] `src/providers/vscode-lm-provider.ts` 作成
- [ ] `VSCodeLMProvider` クラス実装
- [ ] `sendRequest()` メソッド（vscode.lm API呼び出し）
- [ ] `listModels()` メソッド
- [ ] `selectModel()` メソッド
- [ ] `isAvailable()` メソッド
- [ ] ストリームレスポンスの収集処理

**受入基準**:
- [ ] VS Code LM APIが正しく呼び出される
- [ ] エラー時に適切な`DelegationError`がスローされる

---

### TSK-B-003: ModelSelector実装

**設計トレース**: DES-PRV-002, REQ-PRV-002  
**見積時間**: 45分  
**依存**: TSK-B-002

**作業内容**:
- [ ] `src/providers/model-selector.ts` 作成
- [ ] `ModelSelector` クラス実装
- [ ] `selectByFamily()` メソッド
- [ ] `selectByVendor()` メソッド
- [ ] `fallback()` メソッド

**受入基準**:
- [ ] ファミリー/ベンダーでモデル選択可能
- [ ] フォールバック機能が動作

---

### TSK-B-004: UsageStatistics実装

**設計トレース**: DES-PRV-002  
**見積時間**: 30分  
**依存**: TSK-B-001

**作業内容**:
- [ ] `src/providers/usage-statistics.ts` 作成
- [ ] `UsageStatistics` クラス実装
- [ ] `recordSuccess()` メソッド
- [ ] `recordFailure()` メソッド
- [ ] `getStats()` メソッド

**受入基準**:
- [ ] 成功/失敗が記録される
- [ ] 統計が正しく集計される

---

## 4. Phase C: Expert層

### TSK-C-001: Expertインターフェース定義

**設計トレース**: DES-EXP-001  
**見積時間**: 20分  
**依存**: TSK-A-002

**作業内容**:
- [ ] `src/experts/expert-interface.ts` 作成
- [ ] `Expert` インターフェース（types/から再エクスポート）
- [ ] Expert生成ヘルパー関数

**受入基準**:
- [ ] 型定義が正しい

---

### TSK-C-002: ExpertManager実装

**設計トレース**: DES-EXP-001, REQ-EXP-001  
**見積時間**: 45分  
**依存**: TSK-C-001

**作業内容**:
- [ ] `src/experts/expert-manager.ts` 作成
- [ ] `ExpertManager` クラス実装
- [ ] `registerExpert()` メソッド
- [ ] `getExpert()` メソッド
- [ ] `listExperts()` メソッド
- [ ] `getExpertByTrigger()` メソッド
- [ ] 7エキスパートのデフォルト登録

**受入基準**:
- [ ] 7エキスパートが登録される
- [ ] タイプ/トリガーで検索可能

---

### TSK-C-003: Architect Expert実装

**設計トレース**: DES-EXP-001  
**見積時間**: 30分  
**依存**: TSK-C-001

**作業内容**:
- [ ] `src/experts/architect.ts` 作成
- [ ] `architectExpert` 定義
- [ ] システムプロンプト定義
- [ ] トリガーパターン定義（EN/JA）
- [ ] ケイパビリティ定義

**受入基準**:
- [ ] claude-delegator互換のシステムプロンプト

---

### TSK-C-004: Security Analyst Expert実装

**設計トレース**: DES-EXP-001  
**見積時間**: 30分  
**依存**: TSK-C-001

**作業内容**:
- [ ] `src/experts/security-analyst.ts` 作成
- [ ] `securityAnalystExpert` 定義
- [ ] セキュリティ特化プロンプト
- [ ] トリガーパターン（security, 脆弱性 等）

**受入基準**:
- [ ] セキュリティ分析に特化したプロンプト

---

### TSK-C-005: Code Reviewer Expert実装

**設計トレース**: DES-EXP-001  
**見積時間**: 30分  
**依存**: TSK-C-001

**作業内容**:
- [ ] `src/experts/code-reviewer.ts` 作成
- [ ] `codeReviewerExpert` 定義
- [ ] コードレビュー特化プロンプト

**受入基準**:
- [ ] コードレビューに特化したプロンプト

---

### TSK-C-006: Plan Reviewer Expert実装

**設計トレース**: DES-EXP-001  
**見積時間**: 30分  
**依存**: TSK-C-001

**作業内容**:
- [ ] `src/experts/plan-reviewer.ts` 作成
- [ ] `planReviewerExpert` 定義
- [ ] 計画/設計レビュー特化プロンプト
- [ ] 憲法条項チェック機能

**受入基準**:
- [ ] 計画レビューに特化したプロンプト

---

### TSK-C-007: EARS Analyst Expert実装（MUSUBIX独自）

**設計トレース**: DES-EXP-003, REQ-EXP-003  
**見積時間**: 45分  
**依存**: TSK-C-001

**作業内容**:
- [ ] `src/experts/ears-analyst.ts` 作成
- [ ] `earsAnalystExpert` 定義
- [ ] EARS 5パターン知識をプロンプトに埋め込み
- [ ] @nahisaho/musubix-core EARS検証との連携
- [ ] オントロジークラス: `sdd:EARSAnalyst`

**受入基準**:
- [ ] EARS形式への変換・検証が可能
- [ ] 既存のmusubix-coreと連携

---

### TSK-C-008: Formal Verifier Expert実装（MUSUBIX独自）

**設計トレース**: DES-EXP-004, REQ-EXP-004  
**見積時間**: 45分  
**依存**: TSK-C-001

**作業内容**:
- [ ] `src/experts/formal-verifier.ts` 作成
- [ ] `formalVerifierExpert` 定義
- [ ] Z3/Lean4検証知識をプロンプトに埋め込み
- [ ] @nahisaho/musubix-formal-verifyとの連携
- [ ] オントロジークラス: `sdd:FormalVerifier`

**受入基準**:
- [ ] 形式検証の指示が可能
- [ ] 既存のformal-verifyと連携

---

### TSK-C-009: Ontology Reasoner Expert実装（MUSUBIX独自）

**設計トレース**: DES-EXP-005, REQ-EXP-005  
**見積時間**: 45分  
**依存**: TSK-C-001

**作業内容**:
- [ ] `src/experts/ontology-reasoner.ts` 作成
- [ ] `ontologyReasonerExpert` 定義
- [ ] オントロジー推論知識をプロンプトに埋め込み
- [ ] @nahisaho/musubix-ontology-mcpとの連携
- [ ] オントロジークラス: `sdd:OntologyReasoner`

**受入基準**:
- [ ] オントロジー推論の指示が可能
- [ ] 既存のontology-mcpと連携

---

## 5. Phase D: Trigger層

### TSK-D-001: TriggerPatterns定義

**設計トレース**: DES-TRG-001, REQ-TRG-001  
**見積時間**: 30分  
**依存**: TSK-A-002

**作業内容**:
- [ ] `src/triggers/trigger-patterns.ts` 作成
- [ ] 7エキスパートのトリガーパターン定義
- [ ] 英語/日本語パターン
- [ ] 優先度設定

**受入基準**:
- [ ] 全7エキスパートのトリガーが定義
- [ ] 日英両方でマッチ可能

---

### TSK-D-002: SemanticRouter実装

**設計トレース**: DES-TRG-001, REQ-TRG-001  
**見積時間**: 1時間  
**依存**: TSK-D-001, TSK-C-002

**作業内容**:
- [ ] `src/triggers/semantic-router.ts` 作成
- [ ] `SemanticRouter` クラス実装
- [ ] `detectIntent()` メソッド
- [ ] `routeToExpert()` メソッド
- [ ] `registerTrigger()` メソッド
- [ ] パターンマッチング（正規表現/文字列）
- [ ] 優先度ベースの選択ロジック

**受入基準**:
- [ ] メッセージから適切なエキスパートを選択
- [ ] 曖昧な場合はTRIGGER_AMBIGUOUSエラー

---

### TSK-D-003: ProactiveDelegation実装

**設計トレース**: DES-TRG-002, REQ-TRG-002  
**見積時間**: 45分  
**依存**: TSK-D-002

**作業内容**:
- [ ] `src/triggers/proactive-delegation.ts` 作成
- [ ] `ProactiveDelegation` クラス実装
- [ ] `checkEscalation()` メソッド（失敗回数ベース）
- [ ] `detectSecurityPattern()` メソッド（コード内パターン検出）
- [ ] `detectNonEarsRequirement()` メソッド（非EARS要件検出）

**受入基準**:
- [ ] 3回失敗でエスカレーション提案
- [ ] セキュリティパターン自動検出

---

### TSK-D-004: Trigger層index.ts作成

**設計トレース**: -  
**見積時間**: 15分  
**依存**: TSK-D-001〜003

**作業内容**:
- [ ] `src/triggers/index.ts` 作成
- [ ] 公開APIのエクスポート

**受入基準**:
- [ ] 必要な型・クラスがエクスポートされる

---

## 6. Phase E: Delegation層

### TSK-E-001: PromptBuilder実装

**設計トレース**: DES-FMT-001, DES-FMT-002, REQ-FMT-001, REQ-FMT-002  
**見積時間**: 1時間  
**依存**: TSK-A-002

**作業内容**:
- [ ] `src/delegation/prompt-builder.ts` 作成
- [ ] `PromptBuilder` クラス実装
- [ ] `build7Section()` メソッド（claude-delegator形式）
- [ ] `buildEarsExtended()` メソッド（+EARS/Traceability/Constitution）
- [ ] `validate()` メソッド（プロンプト長チェック）
- [ ] テンプレート文字列定義

**受入基準**:
- [ ] 7セクション形式のプロンプト生成
- [ ] MUSUBIX拡張セクションが追加可能

---

### TSK-E-002: AdvisoryMode実装

**設計トレース**: DES-EXP-002, REQ-EXP-002  
**見積時間**: 30分  
**依存**: TSK-E-001

**作業内容**:
- [ ] `src/delegation/advisory-mode.ts` 作成
- [ ] `AdvisoryMode` クラス実装
- [ ] `analyze()` メソッド
- [ ] `recommend()` メソッド
- [ ] 読み取り専用制約の実装

**受入基準**:
- [ ] ファイル変更を行わない
- [ ] 分析・推奨のみ返却

---

### TSK-E-003: ImplementationMode実装

**設計トレース**: DES-EXP-002, REQ-EXP-002  
**見積時間**: 30分  
**依存**: TSK-E-001

**作業内容**:
- [ ] `src/delegation/implementation-mode.ts` 作成
- [ ] `ImplementationMode` クラス実装
- [ ] `implement()` メソッド
- [ ] `modify()` メソッド
- [ ] 変更ファイルリスト管理

**受入基準**:
- [ ] 実装コードを返却
- [ ] 変更対象ファイルリストを含む

---

### TSK-E-004: RetryHandler実装

**設計トレース**: DES-MCP-002, REQ-MCP-002  
**見積時間**: 45分  
**依存**: TSK-A-003, TSK-E-001

**作業内容**:
- [ ] `src/delegation/retry-handler.ts` 作成
- [ ] `RetryHandler` クラス実装
- [ ] `retry()` メソッド（エラーコンテキスト付き再試行）
- [ ] `escalate()` メソッド（3回失敗後のエスカレーション）
- [ ] `maxRetries` 設定（デフォルト3）
- [ ] 指数バックオフ

**受入基準**:
- [ ] リトライ可能エラーで自動再試行
- [ ] 3回失敗でエスカレーション提案

---

### TSK-E-005: DelegationEngine実装

**設計トレース**: DES-EXP-002, REQ-EXP-002  
**見積時間**: 1時間  
**依存**: TSK-E-001〜004, TSK-B-002, TSK-C-002, TSK-D-002

**作業内容**:
- [ ] `src/delegation/delegation-engine.ts` 作成
- [ ] `DelegationEngine` クラス実装
- [ ] `delegate()` メソッド（メイン委任処理）
- [ ] `setMode()` メソッド
- [ ] コンポーネント統合（Provider, Expert, Trigger, Prompt）
- [ ] エラーハンドリング統合

**受入基準**:
- [ ] タスク→エキスパート選択→プロンプト生成→LLM呼び出し→結果返却
- [ ] エラー時の適切なハンドリング

---

## 7. Phase F: MCP層

### TSK-F-001: MCPツール定義

**設計トレース**: DES-MCP-001, REQ-MCP-001  
**見積時間**: 1時間  
**依存**: TSK-A-002

**作業内容**:
- [ ] `src/mcp/tools.ts` 作成
- [ ] `expertDelegateSchema` 定義
- [ ] `triggerDetectSchema` 定義
- [ ] `delegationRetrySchema` 定義
- [ ] `expertArchitectSchema` 定義
- [ ] `expertSecuritySchema` 定義
- [ ] `expertReviewSchema` 定義
- [ ] `expertPlanSchema` 定義
- [ ] `expertEarsSchema` 定義
- [ ] `expertFormalSchema` 定義
- [ ] `expertOntologySchema` 定義
- [ ] `providerSelectSchema` 定義

**受入基準**:
- [ ] 11ツールのスキーマが定義
- [ ] MCP仕様に準拠

---

### TSK-F-002: MCPハンドラー実装

**設計トレース**: DES-MCP-001, REQ-MCP-001  
**見積時間**: 1.5時間  
**依存**: TSK-F-001, TSK-E-005

**作業内容**:
- [ ] `src/mcp/handlers.ts` 作成
- [ ] `handleExpertDelegate()` 関数
- [ ] `handleTriggerDetect()` 関数
- [ ] `handleDelegationRetry()` 関数
- [ ] `handleExpertArchitect()` 関数
- [ ] `handleExpertSecurity()` 関数
- [ ] `handleExpertReview()` 関数
- [ ] `handleExpertPlan()` 関数
- [ ] `handleExpertEars()` 関数
- [ ] `handleExpertFormal()` 関数
- [ ] `handleExpertOntology()` 関数
- [ ] `handleProviderSelect()` 関数

**受入基準**:
- [ ] 各ツールが正しく動作
- [ ] DelegationEngineと連携

---

### TSK-F-003: mcp-server統合

**設計トレース**: REQ-MCP-001  
**見積時間**: 30分  
**依存**: TSK-F-002

**作業内容**:
- [ ] `packages/mcp-server/` への統合
- [ ] expert-delegationツールの登録
- [ ] ツール一覧への追加（61→72ツール）

**受入基準**:
- [ ] MCPサーバーから11ツールが呼び出せる

---

## 8. Phase G: テスト

### TSK-G-001: VS Code APIモック作成

**設計トレース**: DES-TEST-001  
**見積時間**: 30分  
**依存**: TSK-A-001

**作業内容**:
- [ ] `tests/__mocks__/vscode.ts` 作成
- [ ] `LanguageModelChatMessage` モック
- [ ] `MockLanguageModelChat` クラス
- [ ] `lm` 名前空間モック
- [ ] `CancellationTokenSource` モック

**受入基準**:
- [ ] VS Code環境外でテスト実行可能

---

### TSK-G-002: テストヘルパー作成

**設計トレース**: DES-TEST-002  
**見積時間**: 30分  
**依存**: TSK-G-001, TSK-A-002

**作業内容**:
- [ ] `tests/helpers/test-utils.ts` 作成
- [ ] `createMockExpert()` 関数
- [ ] `createMockDelegationTask()` 関数
- [ ] `createMockDelegationResult()` 関数
- [ ] `setupMockLM()` 関数
- [ ] `resetMockLM()` 関数

**受入基準**:
- [ ] テスト作成が効率化される

---

### TSK-G-003: Provider層テスト

**設計トレース**: REQ-NFR-002  
**見積時間**: 1時間  
**依存**: TSK-B-002〜004, TSK-G-001〜002

**作業内容**:
- [ ] `tests/providers/vscode-lm-provider.test.ts` 作成
- [ ] `tests/providers/model-selector.test.ts` 作成
- [ ] sendRequest成功/失敗テスト
- [ ] モデル選択テスト
- [ ] フォールバックテスト

**受入基準**:
- [ ] Provider層カバレッジ80%以上

---

### TSK-G-004: Expert/Trigger/Delegation層テスト

**設計トレース**: REQ-NFR-002  
**見積時間**: 1.5時間  
**依存**: Phase C〜E完了, TSK-G-001〜002

**作業内容**:
- [ ] `tests/experts/expert-manager.test.ts` 作成
- [ ] `tests/triggers/semantic-router.test.ts` 作成
- [ ] `tests/delegation/delegation-engine.test.ts` 作成
- [ ] `tests/delegation/prompt-builder.test.ts` 作成
- [ ] `tests/delegation/retry-handler.test.ts` 作成

**受入基準**:
- [ ] 各層カバレッジ80%以上

---

### TSK-G-005: MCPツールテスト

**設計トレース**: REQ-NFR-002  
**見積時間**: 30分  
**依存**: TSK-F-002, TSK-G-001〜002

**作業内容**:
- [ ] `tests/mcp/tools.test.ts` 作成
- [ ] 各ツールハンドラーのテスト

**受入基準**:
- [ ] 11ツールのテストカバレッジ

---

## 9. Phase H: ドキュメント

### TSK-H-001: パッケージREADME作成

**設計トレース**: REQ-NFR-003  
**見積時間**: 30分  
**依存**: Phase A〜F完了

**作業内容**:
- [ ] `packages/expert-delegation/README.md` 作成
- [ ] 概要
- [ ] インストール方法
- [ ] 使用方法
- [ ] 7エキスパート説明
- [ ] MCPツール一覧
- [ ] 設定オプション

**受入基準**:
- [ ] 新規ユーザーが理解可能

---

### TSK-H-002: AGENTS.md更新

**設計トレース**: REQ-NFR-003  
**見積時間**: 30分  
**依存**: TSK-H-001

**作業内容**:
- [ ] AGENTS.md更新
- [ ] パッケージ一覧に`expert-delegation`追加
- [ ] MCPツール数更新（96→107）
- [ ] 新機能セクション追加

**受入基準**:
- [ ] AIエージェントが新機能を理解可能

---

## 10. 依存関係図

```
Phase A (基盤)
  TSK-A-001 ──┬── TSK-A-002 ──┬── Phase B (Provider)
              │               │
              └── TSK-A-003 ──┘
                      │
                      ▼
Phase B (Provider)
  TSK-B-001 ── TSK-B-002 ── TSK-B-003
              │
              └── TSK-B-004

Phase C (Expert)
  TSK-C-001 ── TSK-C-002 ── TSK-C-003〜009

Phase D (Trigger)
  TSK-D-001 ── TSK-D-002 ── TSK-D-003 ── TSK-D-004

Phase E (Delegation)
  TSK-E-001 ──┬── TSK-E-002
              ├── TSK-E-003
              └── TSK-E-004 ── TSK-E-005

Phase F (MCP)
  TSK-F-001 ── TSK-F-002 ── TSK-F-003

Phase G (テスト)
  TSK-G-001 ── TSK-G-002 ── TSK-G-003〜005

Phase H (ドキュメント)
  TSK-H-001 ── TSK-H-002
```

---

## 11. タスクサマリー

### 優先度別

| 優先度 | タスク数 | 備考 |
|--------|---------|------|
| **Critical Path** | 15 | A-001→A-002→B-001→B-002→C-002→D-002→E-005→F-002 |
| **Parallel** | 20 | Expert実装（C-003〜009）、テスト（G-003〜005） |

### 工数サマリー

| フェーズ | 見積 | 備考 |
|---------|------|------|
| Phase A | 2h | 基盤。最初に完了必須 |
| Phase B | 3h | Provider。VS Code LM API統合 |
| Phase C | 5h | Expert。7エキスパート実装 |
| Phase D | 3h | Trigger。ルーティングロジック |
| Phase E | 4h | Delegation。コア処理 |
| Phase F | 3h | MCP。ツール統合 |
| Phase G | 4h | テスト。カバレッジ80%目標 |
| Phase H | 1h | ドキュメント |
| **合計** | **25h** | 約3-4営業日 |

---

## 12. トレーサビリティマトリクス

| 要件ID | タスクID | 備考 |
|--------|---------|------|
| REQ-EXP-001 | TSK-C-001, TSK-C-002 | Expert定義・管理 |
| REQ-EXP-002 | TSK-E-002, TSK-E-003, TSK-E-005 | 実行モード |
| REQ-EXP-003 | TSK-C-007 | EARS Analyst |
| REQ-EXP-004 | TSK-C-008 | Formal Verifier |
| REQ-EXP-005 | TSK-C-009 | Ontology Reasoner |
| REQ-TRG-001 | TSK-D-001, TSK-D-002 | トリガー検出 |
| REQ-TRG-002 | TSK-D-003 | プロアクティブ委任 |
| REQ-PRV-001 | TSK-B-001, TSK-B-002 | VS Code LM Provider |
| REQ-PRV-002 | TSK-B-003, TSK-B-004 | モデル選択・統計 |
| REQ-FMT-001 | TSK-E-001 | 7セクション形式 |
| REQ-FMT-002 | TSK-E-001 | EARS拡張形式 |
| REQ-MCP-001 | TSK-F-001, TSK-F-002, TSK-F-003 | MCPツール |
| REQ-MCP-002 | TSK-E-004 | リトライ機能 |
| REQ-NFR-001 | 全タスク | ステートレス設計 |
| REQ-NFR-002 | TSK-G-001〜005 | テストカバレッジ |
| REQ-NFR-003 | TSK-H-001, TSK-H-002 | ドキュメント |

---

## 13. 変更履歴

| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|----------|--------|
| 1.0 | 2026-01-13 | 初版作成 | AI Agent |

---

**文書終端**
