# プロンプトガイド

MUSUBIXでは、CLIコマンドを直接実行する必要はありません。AIエージェント（Claude Code, GitHub Copilot等）に自然言語で話しかけるだけで、内部的にコマンドやMCPツールが実行されます。

このガイドでは、各フェーズで**何をプロンプトとして書けばいいか**と、**内部で何が起きるか**を対応表で説明します。

---

## 開発フロー概要

```
Phase 1        Phase 2      Phase 3        Phase 4       Phase 5
要件定義  ──→  設計   ──→  タスク分解 ──→  実装    ──→  完了
  ↓             ↓            ↓
レビュー      レビュー      レビュー
  ↓             ↓            ↓
承認          承認          承認
```

各フェーズの承認キーワード: `承認` / `OK` / `LGTM` / `approve` / `進める`

---

## Phase 1: 要件定義

### プロンプト → 内部処理 対応表

| ユーザーのプロンプト例 | 内部で実行される処理 | 出力 |
|---------------------|-------------------|------|
| 「〇〇システムの要件を定義して」 | MCPツール `sdd_create_requirements` | EARS形式の要件ドキュメント |
| 「要件定義を開始して」 | 同上 | コンテキスト不足時は明確化質問を返す |
| 「要件をレビューして」 | CLI `musubix requirements validate <file>` | 検証結果（OK/警告/NG） |
| 「要件を修正して」 | 指摘事項に基づいてファイルを修正 | 修正済み要件ドキュメント |
| 「承認」 | Phase 2（設計）に遷移 | — |

### 詳細フロー

**プロンプト**: 「ユーザー認証機能の要件を定義して」

```
Step 1: AIエージェントが sdd_create_requirements を呼び出し
        ↓
        コンテキスト不足の場合、5つの明確化質問を返す:
        - WHY: なぜこの機能が必要か？
        - WHO: 対象ユーザーは？
        - WHAT-IF: 成功時の理想状態は？
        - CONSTRAINT: 制約条件は？
        - SUCCESS: 成功基準は？

Step 2: ユーザーが質問に回答
        ↓
Step 3: AIエージェントがEARS形式の要件を生成
        → musubix requirements validate で自動検証
        → レビュー結果を表示
        ↓
        ┌─────────────────────────────────────────┐
        │ レビュー結果:                             │
        │ ✅ EARS形式: 準拠                        │
        │ ✅ 優先度設定: 完了                      │
        │ ⚠️ 測定可能な基準が不足（3件）          │
        │                                          │
        │ 修正しますか？それとも承認しますか？      │
        └─────────────────────────────────────────┘

Step 4: ユーザーが「承認」→ Phase 2へ
        または「測定可能な基準を追加して」→ 修正して再レビュー
```

### 生成されるEARS形式の例

```
REQ-AUTH-001: ログイン認証
EARS形式: Event-driven
WHEN a user submits valid credentials,
THE authentication system SHALL generate a JWT token
AND redirect the user to the dashboard within 2 seconds.

REQ-AUTH-002: パスワード保護
EARS形式: Unwanted
THE authentication system SHALL NOT store plain-text passwords.

REQ-AUTH-003: アカウントロック
EARS形式: Optional
IF the user fails authentication 5 times,
THEN THE system SHALL lock the account for 30 minutes.
```

### 成果物の保存先

`storage/specs/REQ-*.md`

---

## Phase 2: 設計

### プロンプト → 内部処理 対応表

| ユーザーのプロンプト例 | 内部で実行される処理 | 出力 |
|---------------------|-------------------|------|
| 「設計を作成して」 | MCPツール `sdd_create_design` | C4モデル設計ドキュメント |
| 「設計ドキュメントを生成して」 | 同上 | Context/Container/Component レベル設計 |
| 「C4ダイアグラムを作成して」 | CLI `musubix design c4 <file>` | Mermaid形式のダイアグラム |
| 「設計をレビューして」 | CLI `musubix design validate <file>` | SOLID/トレーサビリティ検証結果 |
| 「承認」 | Phase 3（タスク分解）に遷移 | — |

### 詳細フロー

**プロンプト**: 「設計を作成して」

```
Step 1: AIエージェントが sdd_design_generation プロンプトを使用
        → 要件ファイル（REQ-*）を読み込み
        → C4モデル（Context → Container → Component）を生成
        ↓
Step 2: 自動検証
        → sdd_validate_design でトレーサビリティ検証（REQ-* → DES-*）
        → SOLID原則チェック（5項目）
        → 憲法準拠チェック（Article V, VII, IX）
        ↓
        ┌─────────────────────────────────────────────┐
        │ レビュー結果: 100% (8/8 checks)              │
        │                                              │
        │ 憲法準拠:                                    │
        │   ✅ Article V  - トレーサビリティ           │
        │   ✅ Article VII - 設計パターン              │
        │   ✅ Article IX  - 品質ゲート                │
        │                                              │
        │ SOLID原則:                                   │
        │   ✅ [S] 単一責任                            │
        │   ✅ [O] 開放閉鎖                            │
        │   ✅ [L] リスコフ置換                        │
        │   ✅ [I] インターフェース分離                │
        │   ✅ [D] 依存性逆転                          │
        └─────────────────────────────────────────────┘

Step 3: ユーザーが「承認」→ Phase 3へ
```

> **注意**: Phase 2（設計）から Phase 4（実装）に直接進むことはできません。必ず Phase 3（タスク分解）を経てください。

### 成果物の保存先

`storage/design/DES-*.md`

---

## Phase 3: タスク分解

### プロンプト → 内部処理 対応表

| ユーザーのプロンプト例 | 内部で実行される処理 | 出力 |
|---------------------|-------------------|------|
| 「タスク分解して」 | MCPプロンプト `sdd_task_decomposition` | TSK-* リスト |
| 「実装タスクに分解して」 | 同上 | 優先度・依存関係付きタスク |
| 「タスクをレビューして」 | MCPツール `sdd_validate_traceability` | REQ↔DES↔TSK 対応検証 |
| 「承認」 | Phase 4（実装）に遷移 | — |

### 詳細フロー

**プロンプト**: 「タスク分解して」

```
Step 1: AIエージェントが sdd_task_decomposition を使用
        → 設計ファイル（DES-*）を読み込み
        → 1〜4時間粒度のタスクに分解
        ↓
Step 2: タスクリスト提示
        ┌──────────────────────────────────────────────────┐
        │ 基盤設定:                                         │
        │   TSK-001: プロジェクト初期設定                    │
        │   TSK-002: ドメインモデル定義                      │
        │                                                   │
        │ コア機能（P0）:                                    │
        │   TSK-003: 認証サービス実装 ← REQ-AUTH-001        │
        │   TSK-004: パスワードハッシュ化 ← REQ-AUTH-002    │
        │   TSK-005: アカウントロック ← REQ-AUTH-003         │
        │                                                   │
        │ テスト:                                            │
        │   TSK-006: ユニットテスト作成                      │
        │   TSK-007: 統合テスト作成                          │
        └──────────────────────────────────────────────────┘

Step 3: トレーサビリティ検証
        → sdd_validate_traceability で REQ↔DES↔TSK の対応を確認
        ↓
Step 4: ユーザーが「承認」→ Phase 4へ
```

---

## Phase 4: 実装

### プロンプト → 内部処理 対応表

| ユーザーのプロンプト例 | 内部で実行される処理 | 出力 |
|---------------------|-------------------|------|
| 「実装を開始して」 | TSK-* に基づいてコード生成 | テスト + 実装コード |
| 「コードを生成して」 | CLI `musubix codegen generate <file>` | スケルトンコード |
| 「セキュリティスキャンして」 | CLI `musubix codegen security <path>` | 脆弱性レポート |
| 「トレーサビリティを検証して」 | CLI `musubix trace validate` | REQ→DES→TSK→Code 追跡結果 |

### 実装の進め方（Red-Green-Blue）

各タスクは以下のサイクルで進みます：

```
1. Red:  テストを書く（まだ失敗する状態）
2. Green: テストが通る最小限の実装を書く
3. Blue:  リファクタリング（コード品質の向上）
```

---

## Phase 5: 完了

### プロンプト → 内部処理 対応表

| ユーザーのプロンプト例 | 内部で実行される処理 | 出力 |
|---------------------|-------------------|------|
| 「CHANGELOGを更新して」 | CHANGELOG.md にバージョン情報を追記 | 更新済みCHANGELOG |
| 「コミットして」 | git add + git commit | コミット |

---

## よく使うプロンプト集（Phase横断）

### 要件・設計

| やりたいこと | プロンプト例 |
|------------|------------|
| 要件のEARS変換 | 「この機能の要件をEARS形式で分析して」 |
| 設計生成 | 「設計ドキュメントを生成して」 |
| C4ダイアグラム | 「C4ダイアグラムを作成して」 |
| ADR作成 | 「この技術選定をADRとして記録して」 |
| パターン推奨 | 「設計パターンを推奨して」 |

### 検証・品質

| やりたいこと | プロンプト例 |
|------------|------------|
| トレーサビリティ検証 | 「トレーサビリティを検証して」 |
| 影響分析 | 「REQ-001の変更影響を分析して」 |
| セキュリティチェック | 「セキュリティスキャンして」 |
| 憲法準拠確認 | 「憲法準拠を検証して」 |

### 学習・知識

| やりたいこと | プロンプト例 |
|------------|------------|
| 学習状態確認 | 「学習状態を確認して」 |
| ベストプラクティス | 「ベストプラクティスを表示して」 |
| 知識グラフ検索 | 「〇〇に関連する知識を検索して」 |

### コード解析

| やりたいこと | プロンプト例 |
|------------|------------|
| 依存関係表示 | 「このモジュールの依存関係を表示して」 |
| 呼び出し元検索 | 「この関数の呼び出し元を検索して」 |
| コードグラフ統計 | 「コードグラフの統計を表示して」 |

---

## 内部コマンド対応表（リファレンス）

上級者やデバッグ時に直接CLIを実行する場合の対応表です。

| プロンプト | 内部CLIコマンド |
|-----------|---------------|
| 要件のEARS変換 | `npx musubix requirements analyze <file>` |
| 要件の検証 | `npx musubix requirements validate <file>` |
| 設計の生成 | `npx musubix design generate <file>` |
| 設計の検証 | `npx musubix design validate <file>` |
| C4ダイアグラム | `npx musubix design c4 <file>` |
| ADR生成 | `npx musubix design adr <decision>` |
| コード生成 | `npx musubix codegen generate <file>` |
| セキュリティスキャン | `npx musubix codegen security <path>` |
| テスト生成 | `npx musubix test generate <file>` |
| トレーサビリティマトリクス | `npx musubix trace matrix` |
| 影響分析 | `npx musubix trace impact <id>` |
| トレーサビリティ検証 | `npx musubix trace validate` |
| 学習状態 | `npx musubix learn status` |
| ベストプラクティス | `npx musubix learn best-practices` |
| 知識グラフクエリ | `npx musubix knowledge query` |
| コードグラフインデックス | `npx musubix cg index <path>` |
| コードグラフ依存関係 | `npx musubix cg deps <name>` |

> **pnpmの場合**: `npx` を `pnpm exec` に置き換えてください。
