# MUSUBIX アーキテクチャ概要

> このドキュメントはMUSUBIX自体を開発するコントリビューター向けです。
> MUSUBIXを使って開発したい方は [ユーザードキュメント](../user/README.md) を参照してください。

---

## システム概要

MUSUBIXは25パッケージで構成されるTypeScriptモノレポです。

```
MUSUBIX System v3.8
├── Core Layer          ← CLI・コアロジック・知識管理
├── Agent Layer         ← MCPサーバー・スキル管理・エージェント調整
├── Learning Layer      ← 自己学習・Wake-Sleep・Deep Research
├── Verification Layer  ← セキュリティ分析・形式検証
└── Analysis Layer      ← DFG/CFG・コードグラフ・ニューラル検索
```

## パッケージ一覧

### Core Layer

| パッケージ | npm | 役割 |
|-----------|-----|------|
| `packages/core/` | `@nahisaho/musubix-core` | コアライブラリ（CLI、EARS検証、コード生成、設計パターン） |
| `packages/musubix/` | `musubix` | CLIエントリポイント |
| `packages/musubi/` | `@nahisaho/musubi` | AI要約 |
| `packages/knowledge/` | `@musubix/knowledge` | Git-friendly JSON知識グラフ |
| `packages/policy/` | `@musubix/policy` | 憲法条項検証エンジン |
| `packages/decisions/` | `@musubix/decisions` | ADRマネージャー |

### Agent Layer

| パッケージ | npm | 役割 |
|-----------|-----|------|
| `packages/mcp-server/` | `@nahisaho/musubix-mcp-server` | MCPサーバー（107ツール、5プロンプト） |
| `packages/agent-orchestrator/` | `@nahisaho/musubix-agent-orchestrator` | サブエージェント分散・複雑度分析 |
| `packages/workflow-engine/` | `@nahisaho/musubix-workflow-engine` | 5フェーズ制御・品質ゲート |
| `packages/skill-manager/` | `@nahisaho/musubix-skill-manager` | スキル登録・実行・検証 |
| `packages/expert-delegation/` | `@nahisaho/musubix-expert-delegation` | 7種AI専門家・VS Code LM API統合 |

### Learning Layer

| パッケージ | npm | 役割 |
|-----------|-----|------|
| `packages/wake-sleep/` | `@nahisaho/musubix-wake-sleep` | Wake-Sleep学習サイクル |
| `packages/pattern-mcp/` | `@nahisaho/musubix-pattern-mcp` | パターン学習（抽出・圧縮・ライブラリ） |
| `packages/library-learner/` | `@nahisaho/musubix-library-learner` | APIパターン抽出、メトリクスエクスポート |
| `packages/deep-research/` | `@nahisaho/musubix-deep-research` | AI駆動型深層リサーチ |
| `packages/neural-search/` | `@nahisaho/musubix-neural-search` | 意味的コード検索、軌跡ロギング |
| `packages/synthesis/` | `@nahisaho/musubix-synthesis` | ニューラル誘導プログラム合成 |

### Verification Layer

| パッケージ | npm | 役割 |
|-----------|-----|------|
| `packages/security/` | `@nahisaho/musubix-security` | 脆弱性検出、シークレット検出、テイント解析 |
| `packages/formal-verify/` | `@nahisaho/musubix-formal-verify` | Z3統合、Hoare検証、EARS→SMT変換 |

### Analysis Layer

| パッケージ | npm | 役割 |
|-----------|-----|------|
| `packages/dfg/` | `@nahisaho/musubix-dfg` | データフロー・制御フロー解析 |
| `packages/codegraph/` | `@nahisaho/musubix-codegraph` | コード構造解析・依存関係追跡（16言語対応） |
| `packages/sdd-ontology/` | `@nahisaho/musubix-sdd-ontology` | SDD方法論オントロジー |
| `packages/ontology-mcp/` | `@nahisaho/musubix-ontology-mcp` | N3Store・推論エンジン |
| `packages/assistant-axis/` | `@nahisaho/musubix-assistant-axis` | マルチモーダル統合 |
| `packages/lean/` | `@nahisaho/musubix-lean` | Lean 4統合・定理証明 |

## Core パッケージの内部構造

```
packages/core/src/
├── auth/           # 認証・認可
├── cli/            # CLIインターフェース
│   └── generators/ # スキャフォールドジェネレーター
├── codegen/        # コード生成・解析
├── design/         # 設計パターン・C4モデル
├── error/          # エラーハンドリング
├── explanation/    # 説明生成・可視化
├── learning/       # 自己学習システム
├── requirements/   # 要件分析・分解
├── symbolic/       # シンボリック推論
├── traceability/   # トレーサビリティ
├── types/          # 型定義
├── utils/          # ユーティリティ
└── validators/     # EARS検証
```

## 依存関係の方向

```
musubix (CLI)
  └── @nahisaho/musubix-core
       ├── @musubix/knowledge
       ├── @musubix/policy
       └── @musubix/decisions

@nahisaho/musubix-mcp-server
  ├── @nahisaho/musubix-core
  ├── @nahisaho/musubix-skill-manager
  ├── @nahisaho/musubix-workflow-engine
  └── @nahisaho/musubix-agent-orchestrator
```

> 依存関係は常に上位レイヤーから下位レイヤーへ向かいます（依存性逆転原則に準拠）。

## 技術スタック

| 項目 | 技術 |
|------|------|
| 言語 | TypeScript 5.3+ |
| ランタイム | Node.js 20+ |
| パッケージマネージャ | npm 10+（npm workspaces） |
| ビルド | `tsc -b`（プロジェクト参照） |
| テスト | Vitest |
| リント | ESLint |
| フォーマット | Prettier |

## 関連ドキュメント

| ドキュメント | 内容 |
|-------------|------|
| [開発ガイド](development.md) | ビルド・テスト・リントの実行方法 |
| [APIリファレンス](api-reference.md) | パブリックAPI一覧 |
| [ADR](adr/) | Architecture Decision Records |
