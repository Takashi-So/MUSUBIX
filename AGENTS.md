# MUSUBIX - Neuro-Symbolic AI Integration System

> **AI Coding Agent向け**: このファイルはAIエージェント（GitHub Copilot、Claude等）がMUSUBIXプロジェクトを理解するためのガイドです。

## 🎯 プロジェクト概要

**MUSUBIX**は、**Neural（LLM）** と **Symbolic（Knowledge Graph）** 推論を統合した次世代AIコーディングシステムです。MUSUBI SDD方法論とYATA知識グラフ推論を組み合わせ、高品質なソフトウェア開発を支援します。

| 項目 | 詳細 |
|------|------|
| **バージョン** | 1.1.0 |
| **言語** | TypeScript |
| **ランタイム** | Node.js >= 20.0.0 |
| **パッケージマネージャ** | npm >= 10.0.0 |
| **ビルドシステム** | モノレポ（npm workspaces） |
| **テストフレームワーク** | Vitest |
| **テスト数** | 439 (全合格) |

---

## 📦 アーキテクチャ

### パッケージ構成

```
packages/
├── core/           # @nahisaho/musubix-core
├── mcp-server/     # @nahisaho/musubix-mcp-server  
└── yata-client/    # @nahisaho/musubix-yata-client
```

| パッケージ | npm | 役割 |
|-----------|-----|------|
| `packages/core/` | `@nahisaho/musubix-core` | コアライブラリ - CLI、EARS検証、コード生成、設計パターン |
| `packages/mcp-server/` | `@nahisaho/musubix-mcp-server` | MCPサーバー - 9ツール、3プロンプト |
| `packages/yata-client/` | `@nahisaho/musubix-yata-client` | YATAクライアント - 知識グラフ連携 |

### Core パッケージモジュール

```
packages/core/src/
├── auth/           # 認証・認可
├── cli/            # CLIインターフェース
├── codegen/        # コード生成・解析
├── design/         # 設計パターン・C4モデル
├── error/          # エラーハンドリング
├── explanation/    # 説明生成・可視化
├── learning/       # 自己学習システム（NEW!）
├── requirements/   # 要件分析・分解
├── traceability/   # トレーサビリティ
├── types/          # 型定義
├── utils/          # ユーティリティ
└── validators/     # EARS検証
```

---

## 🛠️ CLI コマンド

```bash
# プロジェクト初期化
npx musubix init [path] [--name <name>] [--force]

# 要件分析（EARS形式）
npx musubix requirements analyze <file>    # 自然言語 → EARS変換
npx musubix requirements validate <file>   # EARS構文検証
npx musubix requirements map <file>        # オントロジーマッピング
npx musubix requirements search <query>    # 関連要件検索

# 設計生成
npx musubix design generate <file>         # 要件から設計生成
npx musubix design patterns <context>      # パターン検出
npx musubix design validate <file>         # SOLID準拠検証
npx musubix design c4 <file>               # C4ダイアグラム生成
npx musubix design adr <decision>          # ADR生成

# コード生成
npx musubix codegen generate <file>        # 設計からコード生成
npx musubix codegen analyze <file>         # 静的解析
npx musubix codegen security <path>        # セキュリティスキャン

# テスト
npx musubix test generate <file>           # テスト生成
npx musubix test coverage <dir>            # カバレッジ測定

# トレーサビリティ
npx musubix trace matrix                   # トレーサビリティマトリクス
npx musubix trace impact <id>              # 影響分析
npx musubix trace validate                 # リンク検証

# 説明生成
npx musubix explain why <id>               # 決定理由の説明
npx musubix explain graph <id>             # 推論グラフ生成

# 自己学習システム
npx musubix learn status                   # 学習状態ダッシュボード
npx musubix learn feedback <id>            # フィードバック記録
npx musubix learn patterns                 # パターン一覧表示
npx musubix learn add-pattern <name>       # パターン手動登録
npx musubix learn remove-pattern <id>      # パターン削除
npx musubix learn recommend                # コンテキストベースの推奨
npx musubix learn decay                    # 未使用パターンの減衰
npx musubix learn export                   # 学習データエクスポート
npx musubix learn import <file>            # 学習データインポート

# ヘルプ
npx musubix --help
npx musubix help <command>
```

---

## 🔌 MCP Server

### 起動方法

```bash
npx @nahisaho/musubix-mcp-server
npx musubix-mcp --transport stdio
```

### ツール一覧（9ツール）

| ツール名 | 説明 |
|---------|------|
| `sdd_create_requirements` | EARS形式の要件ドキュメント作成 |
| `sdd_validate_requirements` | 要件のEARS検証・憲法準拠チェック |
| `sdd_create_design` | C4モデル設計ドキュメント作成 |
| `sdd_validate_design` | 設計の要件トレーサビリティ検証 |
| `sdd_create_tasks` | 設計から実装タスク生成 |
| `sdd_query_knowledge` | YATA知識グラフへのクエリ |
| `sdd_update_knowledge` | 知識グラフの更新 |
| `sdd_validate_constitution` | 9憲法条項への準拠検証 |
| `sdd_validate_traceability` | 要件↔設計↔タスクのトレーサビリティ検証 |

### プロンプト一覧（3プロンプト）

| プロンプト名 | 説明 |
|-------------|------|
| `sdd_requirements_analysis` | 機能説明からEARS形式要件を生成 |
| `sdd_requirements_review` | 要件の完全性・憲法準拠レビュー |
| `sdd_design_generation` | 要件からC4モデル設計を生成 |

---

## 📋 9憲法条項（Constitutional Articles）

すべての開発活動を統治する不変のルールです。

| 条項 | 名称 | 概要 |
|-----|------|------|
| **I** | Library-First | 機能は独立ライブラリとして開始 |
| **II** | CLI Interface | すべてのライブラリはCLI公開必須 |
| **III** | Test-First | Red-Green-Blueサイクルでテスト先行 |
| **IV** | EARS Format | 要件はEARS形式で記述 |
| **V** | Traceability | 要件↔設計↔コード↔テストの100%追跡 |
| **VI** | Project Memory | steering/を参照してから決定 |
| **VII** | Design Patterns | 設計パターン適用の文書化 |
| **VIII** | Decision Records | すべての決定をADRで記録 |
| **IX** | Quality Gates | フェーズ移行前の品質検証 |

**詳細**: [steering/rules/constitution.md](steering/rules/constitution.md)

---

## 📁 プロジェクトメモリ（Steering）

AIエージェントは決定前に必ずこれらのファイルを参照してください。

| ファイル | 内容 |
|---------|------|
| `steering/structure.ja.md` | アーキテクチャパターン、レイヤー構造 |
| `steering/tech.ja.md` | 技術スタック（TypeScript, Node.js 20+） |
| `steering/product.ja.md` | プロダクトコンテキスト |
| `steering/rules/constitution.md` | 9憲法条項 |
| `steering/project.yml` | プロジェクト設定 |

---

## 📂 ストレージ構造

| パス | 内容 |
|-----|------|
| `storage/specs/` | 要件(REQ-*)、設計(DES-*)、タスク(TSK-*) |
| `storage/design/` | 設計ドキュメント、C4ダイアグラム |
| `storage/traceability/` | トレーサビリティマトリクス |
| `storage/reviews/` | コードレビュー、検証結果 |
| `storage/changes/` | 変更履歴 |
| `storage/archive/` | アーカイブ |

---

## 🧪 開発コマンド

```bash
# 依存関係インストール
npm install

# 全パッケージビルド
npm run build

# テスト実行
npm run test              # 全テスト
npm run test:unit         # ユニットテスト
npm run test:integration  # 統合テスト
npm run test:coverage     # カバレッジ計測

# コード品質
npm run lint              # ESLint
npm run lint:fix          # ESLint 自動修正
npm run typecheck         # TypeScript型チェック

# クリーンアップ
npm run clean
```

---

## 🔑 主要機能

### 1. Neuro-Symbolic統合（REQ-INT-001〜003準拠）
- **Neural（LLM）**: 創造的なコード生成、自然言語理解
- **Symbolic（YATA）**: 知識グラフによる精密な推論、一貫性検証
- **信頼度評価ルール** (REQ-INT-002):
  | シンボリック結果 | ニューラル信頼度 | 最終決定 |
  |-----------------|-----------------|---------|
  | invalid | - | ニューラル結果を棄却 |
  | valid | ≥0.8 | ニューラル結果を採用 |
  | valid | <0.8 | シンボリック結果を優先 |

### 2. EARS要件分析
5つのEARSパターンで要件を形式化（REQ-RA-001準拠）：

| パターン | 構文 | 用途 |
|---------|------|------|
| Ubiquitous | `THE [system] SHALL [requirement]` | システムが常に満たすべき要件 |
| Event-driven | `WHEN [event], THE [system] SHALL [response]` | 特定イベント発生時の要件 |
| State-driven | `WHILE [state], THE [system] SHALL [response]` | 特定状態における要件 |
| Unwanted | `THE [system] SHALL NOT [behavior]` | 回避すべき動作の要件 |
| Optional | `IF [condition], THEN THE [system] SHALL [response]` | 条件付き要件 |

**要件総数**: 41要件（REQ-MUSUBIX-001定義）  
**優先度**: P0（必須）、P1（重要）、P2（任意）

### 3. C4モデル設計
4つのレベルで設計を構造化：
- **Context**: システム境界と外部アクター
- **Container**: 技術選択とコンテナ構成
- **Component**: コンテナ内部構造
- **Code**: 実装詳細

**C4コード生成** (v1.0.12 NEW!):
```bash
# C4設計ドキュメントからTypeScriptスケルトンコードを自動生成
npx musubix codegen generate <design.md> --output src/
```
- 設計パターン（Repository, Service, Factory等）を自動検出
- コンポーネントごとにTypeScriptファイル生成
- 設計との完全なトレーサビリティを維持

### 4. 完全なトレーサビリティ
```
要件(REQ-*) → 設計(DES-*) → タスク(TSK-*) → コード → テスト
```

### 5. 自己学習システム（REQ-LEARN-001〜006準拠）
- **フィードバック収集**: accept/reject/modifyの記録と分析
- **パターン抽出**: 繰り返しパターンの自動検出・登録
- **適応的推論**: 学習済みパターンに基づく推論調整
- **プライバシー保護**: 機密情報の自動フィルタリング（ローカルストレージのみ）

```
フィードバック → パターン候補 → 閾値超過 → パターン登録 → 推論に適用
```

---

## 📚 ドキュメント

| ドキュメント | 説明 |
|-------------|------|
| [docs/INSTALL-GUIDE.md](docs/INSTALL-GUIDE.md) | インストールガイド |
| [docs/USER-GUIDE.md](docs/USER-GUIDE.md) | ユーザーガイド |
| [docs/API-REFERENCE.md](docs/API-REFERENCE.md) | APIリファレンス |
| [README.md](README.md) | 英語版README |
| [README.ja.md](README.ja.md) | 日本語版README |

---

## 🤝 AI Agent向けガイドライン

### コード生成時の注意点

1. **憲法条項の遵守**: 9条項を必ず確認
2. **steering/参照**: 決定前にproject memoryを確認
3. **EARS形式**: 要件は必ずEARS形式で記述
4. **トレーサビリティ**: コードコメントに要件IDを記載
5. **テスト先行**: Red-Green-Blueサイクルを遵守
6. **モノレポ構造**: パッケージ間の依存関係に注意

### 推奨ワークフロー

```
1. steering/ を読む
2. 要件をEARS形式で定義
3. C4モデルで設計
4. テストを先に書く（Red）
5. 最小限のコードで実装（Green）
6. リファクタリング（Blue）
7. トレーサビリティを検証
```

---

**Agent**: GitHub Copilot / Claude
**Last Updated**: 2026-01-04
**Version**: 1.1.0
**Repository**: https://github.com/nahisaho/MUSUBIX
