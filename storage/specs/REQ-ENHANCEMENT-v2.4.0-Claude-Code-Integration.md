# MUSUBIX v2.4.0 機能強化 要件定義書
# Claude Code統合・マルチエージェント並列処理

**文書ID**: REQ-ENHANCEMENT-v2.4.0  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.0  
**作成日**: 2026-01-11  
**ステータス**: Draft  
**準拠規格**: EARS（Easy Approach to Requirements Syntax）  
**参考資料**: davila7/claude-code-templates

---

## 1. 文書概要

### 1.1 目的

本文書は、`davila7/claude-code-templates`リポジトリの調査結果に基づき、MUSUBIXのClaude Code連携強化・マルチエージェント並列処理機能の要件を、EARS形式で定義する。

### 1.2 スコープ

本強化の対象範囲：
- **Subagent-Driven Development**（サブエージェント駆動開発）
- **Parallel Agent Dispatching**（並列エージェントディスパッチ）
- **Skills Architecture Optimization**（スキル構造最適化）
- **Agent Definition Format**（エージェント定義フォーマット）
- **Workflow Orchestration**（ワークフローオーケストレーション）
- **MCP Server Enhancement**（MCPサーバー強化）

### 1.3 EARS パターン凡例

| パターン | 説明 | 構文例 |
|----------|------|--------|
| **UBIQUITOUS** | システムが常に満たすべき要件 | THE システム SHALL... |
| **EVENT-DRIVEN** | 特定イベント発生時の要件 | WHEN <event>, THE システム SHALL... |
| **STATE-DRIVEN** | 特定状態における要件 | WHILE <state>, THE システム SHALL... |
| **UNWANTED** | 回避すべき動作の要件 | THE システム SHALL NOT... |
| **OPTIONAL** | 条件付き要件 | IF <condition>, THEN THE システム SHALL... |

### 1.4 優先度定義

| 優先度 | 説明 |
|--------|------|
| **P0** | 必須 - v2.4.0リリースに必要 |
| **P1** | 重要 - できる限り実装 |
| **P2** | 任意 - 時間があれば実装 |

---

## 2. サブエージェント駆動開発（Subagent-Driven Development）

### REQ-SDD-ENH-001: サブエージェントディスパッチャー

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN タスク分解（Phase 3）が完了し、TSK-*が定義された際,  
THE システム SHALL 各タスクに対して独立したサブエージェントをディスパッチし、  
AND THE サブエージェント SHALL 新鮮なコンテキストウィンドウで実行され、  
AND THE システム SHALL サブエージェント完了後に結果を収集する。

**検証方法**: 統合テスト、E2Eテスト  
**受入基準**:
- [ ] TSK-*からサブエージェントが自動ディスパッチされる
- [ ] 各サブエージェントが独立コンテキストで動作する
- [ ] サブエージェント結果が正しく収集される
- [ ] エラー時のフォールバックが機能する

**トレーサビリティ**: DES-SDD-ENH-001, TSK-SDD-ENH-001  
**憲法準拠**: Article III（Test-First Principle）

---

### REQ-SDD-ENH-002: 2段階レビューサイクル

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN サブエージェントがタスク実装を完了した際,  
THE システム SHALL スペック準拠レビュー（Spec Reviewer）を実行し、  
AND WHEN スペック準拠が確認された際,  
THE システム SHALL コード品質レビュー（Quality Reviewer）を実行し、  
AND THE システム SHALL 両レビューの結果をフィードバックとして記録する。

**検証方法**: 統合テスト、レビューログ検証  
**受入基準**:
- [ ] スペック準拠レビューが自動実行される
- [ ] コード品質レビューが自動実行される
- [ ] レビュー結果がフィードバックとして記録される
- [ ] 不合格時に修正サイクルが発動する

**トレーサビリティ**: DES-SDD-ENH-002, TSK-SDD-ENH-002  
**憲法準拠**: Article IX（Quality Gates）

---

### REQ-SDD-ENH-003: TDD自動統合

**種別**: STATE-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHILE サブエージェントがタスクを実行中,  
THE サブエージェント SHALL Red-Green-Blueサイクルに従い、  
AND THE サブエージェント SHALL テスト作成→実装→リファクタリングの順序で処理し、  
AND THE システム SHALL テストカバレッジ80%以上を確認してから完了とする。

**検証方法**: テストカバレッジ測定、サイクルログ検証  
**受入基準**:
- [ ] テストが実装より先に作成される
- [ ] Red→Green→Blueの順序が守られる
- [ ] カバレッジ80%未満で警告が出る
- [ ] TDDサイクルがログに記録される

**トレーサビリティ**: DES-SDD-ENH-003, TSK-SDD-ENH-003  
**憲法準拠**: Article III（Test-First Principle）

---

## 3. 並列エージェントディスパッチ（Parallel Agent Dispatching）

### REQ-PAD-001: 独立タスク検出

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN 複数のタスク（TSK-*）が定義された際,  
THE システム SHALL 依存関係グラフを構築し、  
AND THE システム SHALL 相互に依存しない独立タスクを識別し、  
AND THE システム SHALL 独立タスクを並列実行候補としてマークする。

**検証方法**: 依存関係解析テスト  
**受入基準**:
- [ ] タスク間の依存関係が正しく検出される
- [ ] 循環依存がエラーとして報告される
- [ ] 独立タスクが正しく識別される
- [ ] 依存グラフがJSONで出力可能

**トレーサビリティ**: DES-PAD-001, TSK-PAD-001  
**憲法準拠**: Article V（Traceability Mandate）

---

### REQ-PAD-002: 並列エージェント実行

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN 2つ以上の独立タスクが並列実行候補としてマークされた際,  
THE システム SHALL 各タスクに対して並列にサブエージェントをディスパッチし、  
AND THE システム SHALL 並列実行の進捗をリアルタイムで追跡し、  
AND THE システム SHALL 全サブエージェント完了後に結果を統合する。

**検証方法**: 並列実行テスト、タイミング測定  
**受入基準**:
- [ ] 2つ以上のサブエージェントが同時実行される
- [ ] 各サブエージェントの進捗が追跡可能
- [ ] 並列実行により処理時間が短縮される
- [ ] 結果統合が正しく行われる

**トレーサビリティ**: DES-PAD-002, TSK-PAD-002  
**憲法準拠**: Article I（Library-First Principle）

---

### REQ-PAD-003: コンフリクト検出・解決

**種別**: EVENT-DRIVEN  
**優先度**: P1（重要）

**要件**:  
WHEN 並列エージェントが同一ファイルを変更しようとした際,  
THE システム SHALL コンフリクトを検出し、  
AND THE システム SHALL 変更をマージするかユーザーに確認を求め、  
AND THE システム SHALL コンフリクト解決履歴を記録する。

**検証方法**: コンフリクト検出テスト  
**受入基準**:
- [ ] 同一ファイル変更がコンフリクトとして検出される
- [ ] 自動マージ可能な場合は自動解決される
- [ ] 自動マージ不可の場合はユーザー確認が求められる
- [ ] 解決履歴が記録される

**トレーサビリティ**: DES-PAD-003, TSK-PAD-003  
**憲法準拠**: Article VI（Project Memory）

---

## 4. スキル構造最適化（Skills Architecture）

### REQ-SKILL-001: Progressive Disclosureパターン

**種別**: UBIQUITOUS  
**優先度**: P1（重要）

**要件**:  
THE システム SHALL スキル定義（SKILL.md）を500行以下に抑え、  
AND THE システム SHALL 詳細内容を`references/`ディレクトリに分離し、  
AND THE システム SHALL 例を`examples/`ディレクトリに分離し、  
AND THE システム SHALL ユーティリティスクリプトを`scripts/`ディレクトリに分離する。

**検証方法**: ファイルサイズ検証、構造検証  
**受入基準**:
- [ ] SKILL.mdが500行以下
- [ ] 参照ファイルがreferences/に配置
- [ ] 例ファイルがexamples/に配置
- [ ] スクリプトがscripts/に配置

**トレーサビリティ**: DES-SKILL-001, TSK-SKILL-001  
**憲法準拠**: Article I（Library-First Principle）

---

### REQ-SKILL-002: スキルディレクトリ構造

**種別**: UBIQUITOUS  
**優先度**: P1（重要）

**要件**:  
THE 各スキル SHALL 以下の標準ディレクトリ構造に従い:
```
skill-name/
├── SKILL.md          # 概要 + ルーティング（500行以下）
├── README.md         # クイックスタートガイド
├── references/       # 詳細ドキュメント
├── examples/         # 実例
├── scripts/          # ユーティリティスクリプト
└── assets/           # テンプレート・静的リソース
```
AND THE システム SHALL この構造に準拠しないスキルに警告を出力する。

**検証方法**: 構造検証スクリプト  
**受入基準**:
- [ ] 既存スキルが標準構造に移行されている
- [ ] 新規スキルが標準構造で作成される
- [ ] 構造検証コマンドが提供される
- [ ] 非準拠時に警告が出力される

**トレーサビリティ**: DES-SKILL-002, TSK-SKILL-002  
**憲法準拠**: Article VII（Design Pattern Documentation）

---

## 5. エージェント定義フォーマット（Agent Definition）

### REQ-AGENT-001: YAML Frontmatter形式

**種別**: UBIQUITOUS  
**優先度**: P1（重要）

**要件**:  
THE エージェント定義ファイル SHALL 以下のYAML Frontmatter形式に従い:
```yaml
---
name: agent-identifier
description: |
  Use this agent when [triggering conditions]. Examples:
  <example>
  Context: [Scenario]
  user: "[User request]"
  assistant: "[Response]"
  <commentary>[Why this triggers]</commentary>
  </example>
model: inherit
color: blue
tools: ["Read", "Write", "Grep"]
---
```
AND THE システム SHALL このフォーマットを解析してエージェントを登録する。

**検証方法**: パーサーテスト、形式検証  
**受入基準**:
- [ ] YAML Frontmatterが正しく解析される
- [ ] トリガー条件（description）が認識される
- [ ] ツール制限（tools）が適用される
- [ ] 不正なフォーマットでエラーが出力される

**トレーサビリティ**: DES-AGENT-001, TSK-AGENT-001  
**憲法準拠**: Article VIII（Decision Records）

---

### REQ-AGENT-002: エージェントトリガー条件

**種別**: EVENT-DRIVEN  
**優先度**: P1（重要）

**要件**:  
WHEN ユーザーがリクエストを送信した際,  
THE システム SHALL 登録済みエージェントのdescription（トリガー条件）を評価し、  
AND THE システム SHALL 最も適切なエージェントを自動選択し、  
AND THE システム SHALL 選択理由をログに記録する。

**検証方法**: エージェント選択テスト  
**受入基準**:
- [ ] リクエストに基づいてエージェントが自動選択される
- [ ] 選択理由がログに記録される
- [ ] 複数候補がある場合は最適なものが選ばれる
- [ ] 該当エージェントがない場合はデフォルト動作

**トレーサビリティ**: DES-AGENT-002, TSK-AGENT-002  
**憲法準拠**: Article VI（Project Memory）

---

## 6. ワークフローオーケストレーション（Workflow Orchestration）

### REQ-ORCH-001: タスク依存関係管理

**種別**: UBIQUITOUS  
**優先度**: P1（重要）

**要件**:  
THE システム SHALL タスク間の依存関係をYAML/JSON形式で定義可能とし、  
AND THE システム SHALL 依存関係に基づいて実行順序を決定し、  
AND THE システム SHALL 循環依存を検出してエラーを報告する。

**検証方法**: 依存関係解析テスト  
**受入基準**:
- [ ] 依存関係がYAML/JSONで定義可能
- [ ] 実行順序が正しく決定される
- [ ] 循環依存がエラーとして検出される
- [ ] 依存グラフが可視化可能

**トレーサビリティ**: DES-ORCH-001, TSK-ORCH-001  
**憲法準拠**: Article V（Traceability Mandate）

---

### REQ-ORCH-002: 実行状態追跡

**種別**: STATE-DRIVEN  
**優先度**: P1（重要）

**要件**:  
WHILE ワークフローが実行中,  
THE システム SHALL 各タスクの状態（not-started, in-progress, completed, failed）を追跡し、  
AND THE システム SHALL 進捗をリアルタイムで表示し、  
AND THE システム SHALL 状態変更をイベントとして記録する。

**検証方法**: 状態追跡テスト  
**受入基準**:
- [ ] タスク状態が正しく追跡される
- [ ] 進捗がリアルタイムで表示される
- [ ] 状態変更がイベントログに記録される
- [ ] 失敗時にリトライ/スキップが選択可能

**トレーサビリティ**: DES-ORCH-002, TSK-ORCH-002  
**憲法準拠**: Article VI（Project Memory）

---

### REQ-ORCH-003: 品質ゲート統合

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN ワークフローがフェーズ境界（Phase 1→2, 2→3, 3→4）に到達した際,  
THE システム SHALL 品質ゲートチェックを自動実行し、  
AND THE システム SHALL チェック結果をユーザーに提示し、  
AND THE システム SHALL ユーザー承認なしに次フェーズに進んではならない。

**検証方法**: 品質ゲートテスト  
**受入基準**:
- [ ] 各フェーズ境界で品質チェックが実行される
- [ ] チェック結果がユーザーに提示される
- [ ] 承認なしに次フェーズに進まない
- [ ] 承認履歴が記録される

**トレーサビリティ**: DES-ORCH-003, TSK-ORCH-003  
**憲法準拠**: Article IX（Quality Gates）

---

## 7. MCPサーバー強化（MCP Server Enhancement）

### REQ-MCP-001: ツール命名規則準拠

**種別**: UBIQUITOUS  
**優先度**: P1（重要）

**要件**:  
THE MCPツール SHALL `category_action_target`形式（snake_case）で命名され、  
AND THE 既存ツール（`sdd_*`プレフィックス）SHALL 後方互換性のため維持され、  
AND THE v2.4.0新規ツール SHALL 機能カテゴリに応じたプレフィックス（`agent_*`, `workflow_*`, `skill_*`）を使用し、  
AND THE システム SHALL 命名規則に違反するツールに警告を出力する。

**根拠**:  
既存MCPツール（`sdd_create_requirements`, `sdd_validate_requirements`等）は`sdd_*`プレフィックスで実装済み。
後方互換性（REQ-NFR-002）を維持するため、既存ツールのリネームは行わない。

**検証方法**: 命名規則検証テスト  
**受入基準**:
- [ ] 全ツールがsnake_case形式
- [ ] 既存`sdd_*`ツールが維持されている
- [ ] 新規ツールが適切なプレフィックス（`agent_*`, `workflow_*`, `skill_*`）を使用
- [ ] 命名規則違反で警告が出力される

**トレーサビリティ**: DES-MCP-001, TSK-MCP-001  
**憲法準拠**: Article II（CLI Interface Mandate）

---

### REQ-MCP-002: ツールアノテーション

**種別**: UBIQUITOUS  
**優先度**: P1（重要）

**要件**:  
THE MCPツール SHALL 以下のアノテーションを含む:
- `readOnlyHint`: 読み取り専用か
- `destructiveHint`: 破壊的変更を行うか
- `idempotentHint`: 冪等性があるか
- `openWorldHint`: 外部エンティティと通信するか

AND THE システム SHALL アノテーションに基づいてツール使用の安全性を検証する。

**検証方法**: アノテーション検証テスト  
**受入基準**:
- [ ] 全ツールに4つのアノテーションがある
- [ ] アノテーション値が正確
- [ ] 安全性検証が機能する
- [ ] destructiveHintツール使用時に確認が求められる

**トレーサビリティ**: DES-MCP-002, TSK-MCP-002  
**憲法準拠**: Article IX（Quality Gates）

---

### REQ-MCP-003: Zodスキーマ検証

**種別**: UBIQUITOUS  
**優先度**: P1（重要）

**要件**:  
THE MCPツール SHALL Zodスキーマを使用して入力パラメータをランタイム検証し、  
AND THE スキーマ SHALL `.strict()`でストリクトモードを有効にし、  
AND THE システム SHALL スキーマ違反時に詳細なエラーメッセージを返す。

**検証方法**: スキーマ検証テスト  
**受入基準**:
- [ ] 全ツールがZodスキーマで検証される
- [ ] `.strict()`が有効
- [ ] スキーマ違反で詳細エラーが返る
- [ ] エラーメッセージがアクショナブル

**トレーサビリティ**: DES-MCP-003, TSK-MCP-003  
**憲法準拠**: Article III（Test-First Principle）

---

## 8. 非機能要件

### REQ-NFR-001: 並列処理パフォーマンス

**種別**: UBIQUITOUS  
**優先度**: P1（重要）

**要件**:  
THE 並列エージェント処理 SHALL 逐次処理と比較して30%以上の処理時間短縮を達成し、  
AND THE システム SHALL 並列処理のオーバーヘッドを10%以下に抑える。

**検証方法**: パフォーマンステスト  
**受入基準**:
- [ ] 並列処理で30%以上の時間短縮
- [ ] オーバーヘッドが10%以下
- [ ] メモリ使用量が許容範囲内
- [ ] パフォーマンス結果がログに記録される

**トレーサビリティ**: DES-NFR-001  
**憲法準拠**: Article IX（Quality Gates）

---

### REQ-NFR-002: 下位互換性

**種別**: UNWANTED  
**優先度**: P0（必須）

**要件**:  
THE システム SHALL 既存のMCPツール・スキル・エージェント定義を破壊してはならず、  
AND THE システム SHALL 既存のCLIコマンドシグネチャを変更してはならず、  
AND THE システム SHALL 既存のAPIを維持する。

**検証方法**: 後方互換性テスト  
**受入基準**:
- [ ] 既存MCPツールが動作する
- [ ] 既存スキルが動作する
- [ ] 既存CLIコマンドが動作する
- [ ] マイグレーションガイドが不要

**トレーサビリティ**: DES-NFR-002  
**憲法準拠**: Article I（Library-First Principle）

---

## 9. 要件サマリー

### 優先度別要件数

| 優先度 | 要件数 | 説明 |
|--------|--------|------|
| **P0** | 6 | 必須 - v2.4.0リリースに必要 |
| **P1** | 11 | 重要 - できる限り実装 |
| **P2** | 0 | 任意 - 時間があれば実装 |
| **合計** | **17** | |

### カテゴリ別要件数

| カテゴリ | 要件数 |
|---------|--------|
| サブエージェント駆動開発 | 3 |
| 並列エージェントディスパッチ | 3 |
| スキル構造最適化 | 2 |
| エージェント定義フォーマット | 2 |
| ワークフローオーケストレーション | 3 |
| MCPサーバー強化 | 3 |
| 非機能要件 | 2 |

---

## 10. 用語集

| 用語 | 定義 |
|------|------|
| **サブエージェント** | 特定タスク実行のためにディスパッチされる独立したAIエージェント |
| **Progressive Disclosure** | 情報を段階的に開示するパターン（概要→詳細） |
| **品質ゲート** | フェーズ間の遷移時に実行される品質チェックポイント |
| **冪等性** | 同じ操作を何度実行しても結果が同じになる性質 |
| **Zodスキーマ** | TypeScript/JavaScript向けの型安全なスキーマ検証ライブラリ |

---

## 11. 変更履歴

| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|----------|--------|
| 1.0 | 2026-01-11 | 初版作成 | AI Agent |

---

**文書終端**
