# 要件定義書: MUSUBIX v3.1.0 開発者体験強化

**Document ID**: REQ-DX-v3.1.0  
**Version**: 1.0.0  
**Created**: 2026-01-13  
**Author**: AI Agent  
**Status**: Draft  
**Priority**: P0 (必須)

---

## 1. 概要

### 1.1 目的

GitHub Copilot MCP Server拡張としてのMUSUBIXの開発者体験（DX）を向上させ、エンタープライズ品質保証機能を強化する。

### 1.2 スコープ

| 機能ID | 機能名 | 概要 |
|--------|--------|------|
| REQ-WATCH | 自動Lint/Test実行 | ファイル監視による継続的検証 |
| REQ-SPACES | Copilot Spaces統合 | Knowledge Store ↔ Spaces同期 |
| REQ-CODEQL | CodeQL連携 | セキュリティ分析結果のインポート/統合 |
| REQ-TEAM | チーム共有機能 | Knowledge StoreのGit同期・共有 |

### 1.3 対象バージョン

- **Target**: v3.1.0
- **Base**: v3.0.14

---

## 2. 機能要件: 自動Lint/Test実行（REQ-WATCH）

### 2.1 背景

現在のMUSUBIXは手動でCLIコマンドを実行する必要がある。競合（Windsurf/Aider）は自動実行を提供しており、開発者体験で遅れを取っている。

### 2.2 要件一覧

#### REQ-WATCH-001: ファイル監視モード

> **WHEN** ユーザーが `musubix watch` コマンドを実行する, **THE** システム **SHALL** 指定ディレクトリ内のファイル変更を監視し、変更検出時に自動的に検証を実行する。

| 属性 | 値 |
|------|-----|
| パターン | Event-driven |
| 優先度 | P0 |
| トレース | DES-WATCH-001 |

#### REQ-WATCH-002: Lint自動実行

> **WHEN** TypeScript/JavaScript/Pythonファイルが変更される, **THE** システム **SHALL** 対応するLinter（ESLint/Pylint）を自動実行し、結果をリアルタイムで表示する。

| 属性 | 値 |
|------|-----|
| パターン | Event-driven |
| 優先度 | P0 |
| トレース | DES-WATCH-002 |

#### REQ-WATCH-003: Test自動実行

> **WHEN** ソースファイルまたはテストファイルが変更される, **THE** システム **SHALL** 関連するテストスイートを自動実行し、結果を表示する。

| 属性 | 値 |
|------|-----|
| パターン | Event-driven |
| 優先度 | P0 |
| トレース | DES-WATCH-003 |

#### REQ-WATCH-004: EARS検証自動実行

> **WHEN** 要件ドキュメント（*.md）が変更される, **THE** システム **SHALL** EARS形式検証を自動実行し、違反を報告する。

| 属性 | 値 |
|------|-----|
| パターン | Event-driven |
| 優先度 | P1 |
| トレース | DES-WATCH-004 |

#### REQ-WATCH-005: セキュリティスキャン自動実行

> **WHEN** ソースコードファイルが変更される, **THE** システム **SHALL** セキュリティExtractorによる脆弱性スキャンを自動実行し、検出結果を表示する。

| 属性 | 値 |
|------|-----|
| パターン | Event-driven |
| 優先度 | P1 |
| トレース | DES-WATCH-005 |

#### REQ-WATCH-006: 結果通知

> **THE** システム **SHALL** 検証結果をターミナル出力およびJSON形式ファイルで提供し、Copilot Chatからの参照を可能にする。

| 属性 | 値 |
|------|-----|
| パターン | Ubiquitous |
| 優先度 | P0 |
| トレース | DES-WATCH-006 |

#### REQ-WATCH-007: デバウンス制御

> **THE** システム **SHALL** 連続するファイル変更に対して300msのデバウンスを適用し、過剰な検証実行を防止する。

| 属性 | 値 |
|------|-----|
| パターン | Ubiquitous |
| 優先度 | P1 |
| トレース | DES-WATCH-007 |

#### REQ-WATCH-008: 除外パターン

> **THE** システム **SHALL** `.gitignore`および`.musubixignore`で指定されたパターンを監視対象から除外する。

| 属性 | 値 |
|------|-----|
| パターン | Ubiquitous |
| 優先度 | P1 |
| トレース | DES-WATCH-008 |

---

## 3. 機能要件: Copilot Spaces統合（REQ-SPACES）

### 3.1 背景

GitHub Copilot Spacesはプロジェクト知識を共有する機能を提供する。MUSUBIXのKnowledge Storeとの同期により、SDDワークフローの成果物をチーム全体で活用可能にする。

### 3.2 要件一覧

#### REQ-SPACES-001: Spaces接続

> **WHEN** ユーザーが `musubix spaces connect` コマンドを実行する, **THE** システム **SHALL** GitHub Copilot Spacesとの接続を確立し、認証状態を保存する。

| 属性 | 値 |
|------|-----|
| パターン | Event-driven |
| 優先度 | P0 |
| トレース | DES-SPACES-001 |

#### REQ-SPACES-002: Knowledge Store → Spaces同期

> **WHEN** ユーザーが `musubix spaces push` コマンドを実行する, **THE** システム **SHALL** ローカルKnowledge Storeの内容をCopilot Spacesにアップロードする。

| 属性 | 値 |
|------|-----|
| パターン | Event-driven |
| 優先度 | P0 |
| トレース | DES-SPACES-002 |

#### REQ-SPACES-003: Spaces → Knowledge Store同期

> **WHEN** ユーザーが `musubix spaces pull` コマンドを実行する, **THE** システム **SHALL** Copilot Spacesの内容をローカルKnowledge Storeにダウンロードする。

| 属性 | 値 |
|------|-----|
| パターン | Event-driven |
| 優先度 | P0 |
| トレース | DES-SPACES-003 |

#### REQ-SPACES-004: 自動同期モード

> **WHERE** 自動同期が有効化されている, **THE** システム **SHALL** Knowledge Storeの変更を検出し、自動的にCopilot Spacesと同期する。

| 属性 | 値 |
|------|-----|
| パターン | Optional |
| 優先度 | P2 |
| トレース | DES-SPACES-004 |

#### REQ-SPACES-005: 同期対象選択

> **THE** システム **SHALL** 要件(REQ-*)、設計(DES-*)、タスク(TSK-*)、パターン、ADRを同期対象として選択可能にする。

| 属性 | 値 |
|------|-----|
| パターン | Ubiquitous |
| 優先度 | P1 |
| トレース | DES-SPACES-005 |

#### REQ-SPACES-006: 競合解決

> **WHEN** ローカルとSpacesで同一エンティティに競合が発生する, **THE** システム **SHALL** ユーザーに競合を通知し、手動解決またはマージ戦略の選択を求める。

| 属性 | 値 |
|------|-----|
| パターン | Event-driven |
| 優先度 | P1 |
| トレース | DES-SPACES-006 |

---

## 4. 機能要件: CodeQL連携（REQ-CODEQL）

### 4.1 背景

GitHub CodeQLは業界標準のセキュリティ分析ツールである。MUSUBIXのセキュリティExtractorとの統合により、より包括的なセキュリティ分析を提供する。

### 4.2 要件一覧

#### REQ-CODEQL-001: SARIF結果インポート

> **WHEN** ユーザーが `musubix codeql import <sarif-file>` コマンドを実行する, **THE** システム **SHALL** CodeQL SARIF結果をパースし、Knowledge Storeにセキュリティ検出結果として保存する。

| 属性 | 値 |
|------|-----|
| パターン | Event-driven |
| 優先度 | P0 |
| トレース | DES-CODEQL-001 |

#### REQ-CODEQL-002: 結果統合表示

> **THE** システム **SHALL** CodeQL結果とMUSUBIX Extractor結果を統合し、重複排除した上で一元的に表示する。

| 属性 | 値 |
|------|-----|
| パターン | Ubiquitous |
| 優先度 | P0 |
| トレース | DES-CODEQL-002 |

#### REQ-CODEQL-003: CWE/CVEマッピング

> **THE** システム **SHALL** CodeQL検出結果にCWE/CVE識別子をマッピングし、脆弱性の分類と優先度付けを支援する。

| 属性 | 値 |
|------|-----|
| パターン | Ubiquitous |
| 優先度 | P1 |
| トレース | DES-CODEQL-003 |

#### REQ-CODEQL-004: トレーサビリティリンク

> **THE** システム **SHALL** CodeQL検出結果を関連する要件・設計ドキュメントにトレースリンクできるようにする。

| 属性 | 値 |
|------|-----|
| パターン | Ubiquitous |
| 優先度 | P1 |
| トレース | DES-CODEQL-004 |

#### REQ-CODEQL-005: GitHub Actions統合

> **WHERE** プロジェクトにGitHub Actionsが設定されている, **THE** システム **SHALL** CodeQL分析ワークフローの設定テンプレートを生成する。

| 属性 | 値 |
|------|-----|
| パターン | Optional |
| 優先度 | P2 |
| トレース | DES-CODEQL-005 |

#### REQ-CODEQL-006: MCPツール提供

> **THE** システム **SHALL** `codeql_import`、`codeql_status`、`codeql_findings` MCPツールを提供し、Copilot Chatからの操作を可能にする。

| 属性 | 値 |
|------|-----|
| パターン | Ubiquitous |
| 優先度 | P0 |
| トレース | DES-CODEQL-006 |

---

## 5. 機能要件: チーム共有機能（REQ-TEAM）

### 5.1 背景

現在のKnowledge Storeはローカルファイルとして保存されている。Git同期によりチーム間での知識共有を実現する。

### 5.2 要件一覧

#### REQ-TEAM-001: Git同期初期化

> **WHEN** ユーザーが `musubix team init` コマンドを実行する, **THE** システム **SHALL** `.knowledge/`ディレクトリをGit管理対象として初期化し、リモートリポジトリとの接続を設定する。

| 属性 | 値 |
|------|-----|
| パターン | Event-driven |
| 優先度 | P0 |
| トレース | DES-TEAM-001 |

#### REQ-TEAM-002: Push操作

> **WHEN** ユーザーが `musubix team push` コマンドを実行する, **THE** システム **SHALL** ローカルKnowledge Storeの変更をリモートリポジトリにプッシュする。

| 属性 | 値 |
|------|-----|
| パターン | Event-driven |
| 優先度 | P0 |
| トレース | DES-TEAM-002 |

#### REQ-TEAM-003: Pull操作

> **WHEN** ユーザーが `musubix team pull` コマンドを実行する, **THE** システム **SHALL** リモートリポジトリからKnowledge Storeの変更を取得してマージする。

| 属性 | 値 |
|------|-----|
| パターン | Event-driven |
| 優先度 | P0 |
| トレース | DES-TEAM-003 |

#### REQ-TEAM-004: 競合検出・解決

> **WHEN** リモートとローカルで同一エンティティに競合が発生する, **THE** システム **SHALL** 競合を検出し、3-way mergeまたは手動解決をサポートする。

| 属性 | 値 |
|------|-----|
| パターン | Event-driven |
| 優先度 | P0 |
| トレース | DES-TEAM-004 |

#### REQ-TEAM-005: 変更履歴表示

> **THE** システム **SHALL** Knowledge Storeの変更履歴（コミットログ）を表示し、特定バージョンへのロールバックを可能にする。

| 属性 | 値 |
|------|-----|
| パターン | Ubiquitous |
| 優先度 | P1 |
| トレース | DES-TEAM-005 |

#### REQ-TEAM-006: アクセス制御

> **THE** システム **SHALL** GitHubリポジトリのアクセス権限に基づいてKnowledge Storeの読み取り/書き込み権限を制御する。

| 属性 | 値 |
|------|-----|
| パターン | Ubiquitous |
| 優先度 | P1 |
| トレース | DES-TEAM-006 |

#### REQ-TEAM-007: 差分表示

> **WHEN** ユーザーが `musubix team diff` コマンドを実行する, **THE** システム **SHALL** ローカルとリモートのKnowledge Store差分を人間可読形式で表示する。

| 属性 | 値 |
|------|-----|
| パターン | Event-driven |
| 優先度 | P1 |
| トレース | DES-TEAM-007 |

#### REQ-TEAM-008: MCPツール提供

> **THE** システム **SHALL** `team_push`、`team_pull`、`team_status`、`team_diff` MCPツールを提供し、Copilot Chatからの操作を可能にする。

| 属性 | 値 |
|------|-----|
| パターン | Ubiquitous |
| 優先度 | P0 |
| トレース | DES-TEAM-008 |

---

## 6. 非機能要件

### NFR-001: パフォーマンス

> **THE** システム **SHALL** Watch Modeでのファイル変更検出から検証開始まで500ms以内に応答する。

### NFR-002: スケーラビリティ

> **THE** システム **SHALL** 10,000ファイル以上のプロジェクトでもWatch Modeを安定稼働させる。

### NFR-003: セキュリティ

> **THE** システム **SHALL NOT** 認証トークンをログファイルに出力する。

### NFR-004: 可用性

> **THE** システム **SHALL** ネットワーク切断時もローカルKnowledge Store操作を継続可能にする。

### NFR-005: 互換性

> **THE** システム **SHALL** 既存のv3.0.x Knowledge Storeフォーマットとの後方互換性を維持する。

---

## 7. 要件サマリー

| カテゴリ | 要件数 | P0 | P1 | P2 |
|---------|--------|----|----|-----|
| REQ-WATCH | 8 | 3 | 4 | 1 |
| REQ-SPACES | 6 | 3 | 2 | 1 |
| REQ-CODEQL | 6 | 3 | 2 | 1 |
| REQ-TEAM | 8 | 4 | 3 | 1 |
| NFR | 5 | 5 | 0 | 0 |
| **合計** | **33** | **18** | **11** | **4** |

---

## 8. 承認

| 役割 | 名前 | 日付 | 署名 |
|------|------|------|------|
| 作成者 | AI Agent | 2026-01-13 | ✓ |
| レビュアー | | | |
| 承認者 | | | |

---

## 9. 変更履歴

| バージョン | 日付 | 変更者 | 変更内容 |
|-----------|------|--------|---------|
| 1.0.0 | 2026-01-13 | AI Agent | 初版作成 |
