# MUSUBIX - Neuro-Symbolic AI Integration System

**バージョン**: 1.7.5 (Formal Verification Edition)  
**最終更新**: 2026-01-06

---

## 1. 概要

**MUSUBIX**（ムスビックス）は、**Neural（LLM/大規模言語モデル）** と **Symbolic（Knowledge Graph/知識グラフ）** 推論を統合した次世代AIコーディング支援システムです。

MUSUBI SDD（Specification-Driven Development）方法論とYATA知識グラフ推論エンジンを組み合わせ、高品質なソフトウェア開発を実現します。

### 1.1 主要な特徴

| 特徴 | 説明 |
|------|------|
| **Neuro-Symbolic統合** | LLMの創造性とシンボリック推論の精密性を融合 |
| **EARS形式要件** | 5パターンの形式的要件記述（Easy Approach to Requirements Syntax） |
| **9条憲法** | 開発プロセスを統治する9つの不変ルール |
| **完全トレーサビリティ** | 要件→設計→コード→テストの100%追跡 |
| **形式検証** | Z3 SMTソルバによる数学的正確性の検証 |
| **自己学習** | フィードバックに基づくパターン学習と適応 |
| **知識グラフ** | SQLiteベースのローカル知識グラフとグローバル共有 |

### 1.2 システム要件

| 項目 | 要件 |
|------|------|
| **ランタイム** | Node.js >= 20.0.0 |
| **パッケージマネージャ** | npm >= 10.0.0 |
| **言語** | TypeScript 5.x |
| **ビルドシステム** | npm workspaces（モノレポ） |
| **テストフレームワーク** | Vitest |

---

## 2. アーキテクチャ

### 2.1 パッケージ構成

```
packages/
├── core/           # @nahisaho/musubix-core
├── mcp-server/     # @nahisaho/musubix-mcp-server  
├── formal-verify/  # @nahisaho/musubix-formal-verify
├── yata-client/    # @nahisaho/musubix-yata-client
├── yata-local/     # @nahisaho/yata-local
├── yata-global/    # @nahisaho/yata-global
├── yata-ui/        # @nahisaho/yata-ui
├── pattern-mcp/    # @nahisaho/musubix-pattern-mcp
├── ontology-mcp/   # @nahisaho/musubix-ontology-mcp
├── wake-sleep/     # @nahisaho/musubix-wake-sleep
└── sdd-ontology/   # @nahisaho/musubix-sdd-ontology
```

### 2.2 パッケージ一覧

| パッケージ | npm | 役割 |
|-----------|-----|------|
| **core** | `@nahisaho/musubix-core` | コアライブラリ - CLI、EARS検証、コード生成、設計パターン |
| **mcp-server** | `@nahisaho/musubix-mcp-server` | MCPサーバー - AIエージェント連携 |
| **formal-verify** | `@nahisaho/musubix-formal-verify` | 形式検証 - Z3統合、Hoare検証 |
| **yata-client** | `@nahisaho/musubix-yata-client` | YATAクライアント - 知識グラフAPI |
| **yata-local** | `@nahisaho/yata-local` | ローカル知識グラフ - SQLiteベース |
| **yata-global** | `@nahisaho/yata-global` | グローバル知識グラフ - 分散共有 |
| **yata-ui** | `@nahisaho/yata-ui` | Web UI - 可視化・管理 |
| **pattern-mcp** | `@nahisaho/musubix-pattern-mcp` | パターン学習 - 抽出・圧縮 |
| **ontology-mcp** | `@nahisaho/musubix-ontology-mcp` | オントロジー - N3Store・推論 |
| **wake-sleep** | `@nahisaho/musubix-wake-sleep` | Wake-Sleep学習サイクル |
| **sdd-ontology** | `@nahisaho/musubix-sdd-ontology` | SDD方法論オントロジー |

### 2.3 依存関係図

```
┌─────────────────────────────────────────────────────────────┐
│                    MCP Server                               │
│  ┌─────────────────────────────────────────────────────┐    │
│  │ Claude Code / GitHub Copilot / Cursor / Gemini CLI  │    │
│  └─────────────────────────────────────────────────────┘    │
└──────────────────────┬──────────────────────────────────────┘
                       │
┌──────────────────────▼──────────────────────────────────────┐
│                    MUSUBIX Core                             │
│  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────────────┐    │
│  │Symbolic │ │ CodeGen │ │ Design  │ │   Traceability  │    │
│  └────┬────┘ └────┬────┘ └────┬────┘ └────────┬────────┘    │
│       │           │           │               │             │
│  ┌────▼───────────▼───────────▼───────────────▼──────────┐  │
│  │              Learning System                          │  │
│  └───────────────────────────┬───────────────────────────┘  │
└──────────────────────────────┼──────────────────────────────┘
                               │
┌──────────────────────────────▼──────────────────────────────┐
│                    YATA Knowledge Graph                     │
│  ┌─────────────┐    ┌──────────────┐    ┌─────────────┐     │
│  │ YATA Local  │◄──►│ YATA Global  │◄──►│   YATA UI   │     │
│  │  (SQLite)   │    │ (Distributed)│    │   (Web)     │     │
│  └─────────────┘    └──────────────┘    └─────────────┘     │
└─────────────────────────────────────────────────────────────┘
```

---

## 3. 9条憲法（Constitutional Articles）

MUSUBIXのすべての開発活動を統治する不変のルールです。

| 条項 | 名称 | 概要 |
|------|------|------|
| **I** | Library-First | 機能は独立ライブラリとして開始 |
| **II** | CLI Interface | すべてのライブラリはCLI公開必須 |
| **III** | Test-First | Red-Green-Blueサイクルでテスト先行 |
| **IV** | EARS Format | 要件はEARS形式で記述 |
| **V** | Traceability | 要件↔設計↔コード↔テストの100%追跡 |
| **VI** | Project Memory | steering/を参照してから決定 |
| **VII** | Design Patterns | 設計パターン適用の文書化 |
| **VIII** | Decision Records | すべての決定をADRで記録 |
| **IX** | Quality Gates | フェーズ移行前の品質検証 |

---

## 4. EARS要件形式

5つのEARSパターンで要件を形式化します。

| パターン | 構文 | 用途 |
|---------|------|------|
| **Ubiquitous** | `THE [system] SHALL [requirement]` | システムが常に満たすべき要件 |
| **Event-driven** | `WHEN [event], THE [system] SHALL [response]` | 特定イベント発生時の要件 |
| **State-driven** | `WHILE [state], THE [system] SHALL [response]` | 特定状態における要件 |
| **Unwanted** | `THE [system] SHALL NOT [behavior]` | 回避すべき動作の要件 |
| **Optional** | `IF [condition], THEN THE [system] SHALL [response]` | 条件付き要件 |

### 例

```
# Ubiquitous（常時）
THE system SHALL encrypt all user data at rest.

# Event-driven（イベント駆動）
WHEN a user submits a login form, THE system SHALL validate credentials within 2 seconds.

# State-driven（状態駆動）
WHILE the system is in maintenance mode, THE system SHALL reject all API requests.

# Unwanted（禁止）
THE system SHALL NOT store passwords in plain text.

# Optional（条件付き）
IF the user has admin privileges, THEN THE system SHALL display the admin dashboard.
```

---

## 5. Neuro-Symbolic統合

### 5.1 統合アーキテクチャ

MUSUBIXは、LLM（Neural）の創造性とシンボリック推論の精密性を組み合わせます。

```
┌─────────────────────────────────────────────────────────────┐
│                    User Request                             │
└──────────────────────┬──────────────────────────────────────┘
                       │
┌──────────────────────▼──────────────────────────────────────┐
│                  Neural (LLM)                               │
│  • コード生成                                                │
│  • 自然言語理解                                              │
│  • 創造的問題解決                                            │
└──────────────────────┬──────────────────────────────────────┘
                       │
┌──────────────────────▼──────────────────────────────────────┐
│              Symbolic Verification                          │
│  • 知識グラフ検証                                            │
│  • 憲法準拠チェック                                          │
│  • ハルシネーション検出                                      │
│  • 形式検証（Z3）                                            │
└──────────────────────┬──────────────────────────────────────┘
                       │
┌──────────────────────▼──────────────────────────────────────┐
│               Confidence Router                             │
│  ┌─────────────────────────────────────────────────────┐    │
│  │ Symbolic結果    Neural信頼度    最終決定              │    │
│  │ ─────────────  ─────────────  ─────────────         │    │
│  │ invalid        -              Neural結果を棄却       │    │
│  │ valid          ≥0.8           Neural結果を採用       │    │
│  │ valid          <0.8           Symbolic結果を優先     │    │
│  └─────────────────────────────────────────────────────┘    │
└─────────────────────────────────────────────────────────────┘
```

### 5.2 信頼度評価

| シンボリック結果 | ニューラル信頼度 | 最終決定 |
|-----------------|-----------------|---------|
| `invalid` | - | ニューラル結果を**棄却** |
| `valid` | ≥0.8 | ニューラル結果を**採用** |
| `valid` | <0.8 | シンボリック結果を**優先** |

---

## 6. クイックスタート

### 6.1 インストール

```bash
# グローバルインストール
npm install -g @nahisaho/musubix-core

# プロジェクトにインストール
npm install @nahisaho/musubix-core
```

### 6.2 プロジェクト初期化

```bash
npx musubix init my-project
cd my-project
```

### 6.3 基本的なワークフロー

```bash
# 1. 要件をEARS形式で定義
npx musubix requirements analyze requirements.md

# 2. 設計を生成
npx musubix design generate requirements.md

# 3. コードを生成
npx musubix codegen generate design.md

# 4. テストを生成
npx musubix test generate src/

# 5. トレーサビリティを検証
npx musubix trace validate
```

---

## 7. 関連ドキュメント

| ドキュメント | 説明 |
|-------------|------|
| [MUSUBIX-Core.md](MUSUBIX-Core.md) | Coreパッケージ詳細 |
| [MUSUBIX-FormalVerify.md](MUSUBIX-FormalVerify.md) | 形式検証パッケージ |
| [MUSUBIX-MCP-Server.md](MUSUBIX-MCP-Server.md) | MCPサーバー |
| [MUSUBIX-YATA.md](MUSUBIX-YATA.md) | YATA知識グラフ |
| [MUSUBIX-Learning.md](MUSUBIX-Learning.md) | 学習システム |
| [USER-GUIDE.md](USER-GUIDE.md) | ユーザーガイド |
| [API-REFERENCE.md](API-REFERENCE.md) | APIリファレンス |

---

## 8. ライセンス

MIT License

---

**© 2026 MUSUBIX Project**
