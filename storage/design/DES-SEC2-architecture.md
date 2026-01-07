# MUSUBIX Security v2.0 アーキテクチャ設計書

**プロジェクト**: MUSUBIX Security Subsystem
**バージョン**: 2.0.0
**ステータス**: Draft
**作成日**: 2026-01-07
**最終更新**: 2026-01-07
**作成者**: AI Agent (Claude)
**要件定義**: [REQ-SEC-v2.0.md](../specs/REQ-SEC-v2.0.md)

---

## 1. 設計概要

### 1.1 目的

本ドキュメントは、MUSUBIX Security v2.0のアーキテクチャをC4モデルに基づいて定義します。
GitHub Advanced Securityを上回るNeuro-Symbolic AIベースのセキュリティ分析プラットフォームを実現します。

### 1.2 設計原則

| 原則 | 説明 | 根拠 |
|------|------|------|
| **Library-First** | 独立ライブラリとして設計 | 憲法Article I |
| **CLI-First** | 全機能をCLI経由で公開 | 憲法Article II |
| **Neuro-Symbolic** | LLM + 知識グラフ + 形式検証の統合 | REQ-SEC2-SAST-002 |
| **Extensibility** | カスタムルール・プラグイン対応 | REQ-SEC2-EXT-001 |
| **Performance** | 10,000行/秒以上の処理速度 | REQ-SEC2-PERF-001 |

### 1.3 アーキテクチャスタイル

- **レイヤードアーキテクチャ**: Domain → Application → Infrastructure → Interface
- **プラグインアーキテクチャ**: 言語別アナライザー、カスタムルール
- **パイプライン＆フィルター**: 解析パイプライン
- **イベント駆動**: 脆弱性検出時の通知・修正提案

---

## 2. C4 Level 1: システムコンテキスト図

### 2.1 概要

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              External Actors                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌──────────┐   ┌──────────┐   ┌──────────┐   ┌──────────┐   ┌──────────┐ │
│  │Developer │   │  CI/CD   │   │   IDE    │   │ Security │   │   AI     │ │
│  │          │   │ Pipeline │   │(VS Code) │   │  Team    │   │  Agent   │ │
│  └────┬─────┘   └────┬─────┘   └────┬─────┘   └────┬─────┘   └────┬─────┘ │
│       │              │              │              │              │        │
│       │    CLI       │   Actions    │     LSP      │   Dashboard  │   MCP  │
│       ▼              ▼              ▼              ▼              ▼        │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                                                                     │   │
│  │                    MUSUBIX Security System                          │   │
│  │                                                                     │   │
│  │   ┌─────────────────────────────────────────────────────────────┐   │   │
│  │   │  • 脆弱性スキャン (SAST)                                    │   │   │
│  │   │  • テイント分析                                             │   │   │
│  │   │  • シークレット検出                                         │   │   │
│  │   │  • 依存関係監査                                             │   │   │
│  │   │  • 自動修正 (LLM + Z3)                                      │   │   │
│  │   │  • コンテナ/IaCスキャン                                     │   │   │
│  │   │  • AI/MLセキュリティ                                        │   │   │
│  │   │  • コンプライアンス検証                                     │   │   │
│  │   └─────────────────────────────────────────────────────────────┘   │   │
│  │                                                                     │   │
│  └───────────────────────────┬─────────────────────────────────────────┘   │
│                              │                                              │
├──────────────────────────────┼──────────────────────────────────────────────┤
│                              │                                              │
│  ┌──────────┐   ┌────────────┴───┐   ┌──────────┐   ┌──────────┐          │
│  │   YATA   │   │    LLM API     │   │   CVE    │   │  Package │          │
│  │Knowledge │   │ (OpenAI/Claude)│   │ Database │   │ Registry │          │
│  │  Graph   │   └────────────────┘   │(NVD/OSV) │   │(npm/PyPI)│          │
│  └──────────┘                        └──────────┘   └──────────┘          │
│                         External Systems                                    │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 2.2 外部アクター定義

| アクター | 説明 | インターフェース | 関連要件 |
|---------|------|-----------------|---------|
| **Developer** | コードを書く開発者 | CLI, IDE Extension | REQ-SEC2-CLI-001 |
| **CI/CD Pipeline** | GitHub Actions, GitLab CI等 | CLI, SARIF出力 | REQ-SEC2-INT-002 |
| **IDE (VS Code)** | 開発環境 | Language Server Protocol | REQ-SEC2-INT-001 |
| **Security Team** | セキュリティ監査担当 | Dashboard, Reports | REQ-SEC2-REPORT-001 |
| **AI Agent** | Claude, GitHub Copilot等 | MCP Protocol | REQ-SEC2-INT-003 |

### 2.3 外部システム定義

| システム | 説明 | 通信方式 | 関連要件 |
|---------|------|---------|---------|
| **YATA Knowledge Graph** | セキュリティ知識グラフ | GraphQL/REST | REQ-SEC2-SAST-002 |
| **LLM API** | OpenAI, Anthropic, Azure OpenAI | REST API | REQ-SEC2-FIX-001, REQ-SEC2-AI-001 |
| **CVE Database** | NVD, GitHub Advisory, OSV, Snyk | REST API | REQ-SEC2-DEP-001 |
| **Package Registry** | npm, PyPI, Maven Central | REST API | REQ-SEC2-DEP-002 |

---

## 3. C4 Level 2: コンテナ図

### 3.1 概要

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        MUSUBIX Security System                              │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                        Interface Layer                               │   │
│  │  ┌────────────┐  ┌────────────┐  ┌────────────┐  ┌────────────┐    │   │
│  │  │    CLI     │  │ MCP Server │  │ LSP Server │  │  REST API  │    │   │
│  │  │  (Node.js) │  │  (Node.js) │  │  (Node.js) │  │  (Node.js) │    │   │
│  │  │            │  │            │  │            │  │            │    │   │
│  │  │ DES-SEC2-  │  │ DES-SEC2-  │  │ DES-SEC2-  │  │ DES-SEC2-  │    │   │
│  │  │ CLI-001    │  │ INT-003    │  │ INT-001    │  │ REPORT-002 │    │   │
│  │  └─────┬──────┘  └─────┬──────┘  └─────┬──────┘  └─────┬──────┘    │   │
│  └────────┼───────────────┼───────────────┼───────────────┼────────────┘   │
│           │               │               │               │                │
│           └───────────────┴───────┬───────┴───────────────┘                │
│                                   │                                        │
│  ┌────────────────────────────────▼────────────────────────────────────┐   │
│  │                      Application Layer                               │   │
│  │  ┌─────────────────────────────────────────────────────────────┐    │   │
│  │  │                   Security Engine                            │    │   │
│  │  │                     (TypeScript)                             │    │   │
│  │  │                                                              │    │   │
│  │  │  • Orchestration Service                                     │    │   │
│  │  │  • Analysis Pipeline                                         │    │   │
│  │  │  • Fix Generation Service                                    │    │   │
│  │  │  • Report Generation Service                                 │    │   │
│  │  │                                                              │    │   │
│  │  └─────────────────────────────────────────────────────────────┘    │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                   │                                        │
│  ┌────────────────────────────────▼────────────────────────────────────┐   │
│  │                        Domain Layer                                  │   │
│  │  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐  │   │
│  │  │   SAST   │ │  Taint   │ │  Secret  │ │   Dep    │ │   Fix    │  │   │
│  │  │ Analyzer │ │ Analyzer │ │ Detector │ │ Auditor  │ │Generator │  │   │
│  │  │          │ │          │ │          │ │          │ │          │  │   │
│  │  │DES-SEC2- │ │DES-SEC2- │ │DES-SEC2- │ │DES-SEC2- │ │DES-SEC2- │  │   │
│  │  │SAST-001  │ │TAINT-001 │ │SECRET-001│ │DEP-001   │ │FIX-001   │  │   │
│  │  └──────────┘ └──────────┘ └──────────┘ └──────────┘ └──────────┘  │   │
│  │  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐  │   │
│  │  │Container │ │   IaC    │ │   AI/ML  │ │Compliance│ │ Neuro-   │  │   │
│  │  │ Scanner  │ │ Analyzer │ │ Security │ │  Engine  │ │ Symbolic │  │   │
│  │  │          │ │          │ │          │ │          │ │          │  │   │
│  │  │DES-SEC2- │ │DES-SEC2- │ │DES-SEC2- │ │DES-SEC2- │ │DES-SEC2- │  │   │
│  │  │CONTAINER │ │IAC-001   │ │AI-001    │ │COMP-001  │ │SAST-002  │  │   │
│  │  └──────────┘ └──────────┘ └──────────┘ └──────────┘ └──────────┘  │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                   │                                        │
│  ┌────────────────────────────────▼────────────────────────────────────┐   │
│  │                     Infrastructure Layer                             │   │
│  │  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐  │   │
│  │  │   AST    │ │   YATA   │ │   LLM    │ │   CVE    │ │  Report  │  │   │
│  │  │  Parser  │ │  Client  │ │  Client  │ │  Client  │ │Generator │  │   │
│  │  │(ts-morph)│ │          │ │          │ │          │ │          │  │   │
│  │  └──────────┘ └──────────┘ └──────────┘ └──────────┘ └──────────┘  │   │
│  │  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐  │   │
│  │  │  Config  │ │  Audit   │ │   File   │ │   Z3     │ │  Cache   │  │   │
│  │  │ Manager  │ │  Logger  │ │ Scanner  │ │ Verifier │ │  Store   │  │   │
│  │  │          │ │          │ │          │ │          │ │          │  │   │
│  │  └──────────┘ └──────────┘ └──────────┘ └──────────┘ └──────────┘  │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 3.2 コンテナ定義

| コンテナ | 技術 | 責務 | 関連要件 |
|---------|------|------|---------|
| **CLI** | Node.js, Commander.js | コマンドライン入力処理 | REQ-SEC2-CLI-001/002 |
| **MCP Server** | Node.js, @modelcontextprotocol/sdk | AIエージェント統合 | REQ-SEC2-INT-003 |
| **LSP Server** | Node.js, vscode-languageserver | IDE統合 | REQ-SEC2-INT-001 |
| **REST API** | Node.js, Fastify | ダッシュボード・CI/CD統合 | REQ-SEC2-REPORT-002, REQ-SEC2-INT-002 |
| **Security Engine** | TypeScript | 解析オーケストレーション | 全解析要件 |
| **SAST Analyzer** | TypeScript, ts-morph | 静的解析 | REQ-SEC2-SAST-001/002/003/004 |
| **Taint Analyzer** | TypeScript | テイント追跡 | REQ-SEC2-TAINT-001/002/003 |
| **Secret Detector** | TypeScript | シークレット検出 | REQ-SEC2-SECRET-001/002/003 |
| **Dep Auditor** | TypeScript | 依存関係監査 | REQ-SEC2-DEP-001/002/003 |
| **Fix Generator** | TypeScript | 自動修正 | REQ-SEC2-FIX-001/002/003 |
| **Container Scanner** | TypeScript | コンテナスキャン | REQ-SEC2-CONTAINER-001/002 |
| **IaC Analyzer** | TypeScript | IaC分析 | REQ-SEC2-IAC-001/002 |
| **AI/ML Security** | TypeScript | プロンプトインジェクション検出 | REQ-SEC2-AI-001/002 |
| **Compliance Engine** | TypeScript | コンプライアンス検証 | REQ-SEC2-COMP-001/002 |
| **Neuro-Symbolic** | TypeScript | LLM+知識グラフ統合 | REQ-SEC2-SAST-002 |

### 3.3 コンテナ間通信

| From | To | Protocol | 目的 |
|------|-----|----------|------|
| CLI | Security Engine | Function Call | コマンド実行 |
| MCP Server | Security Engine | Function Call | ツール実行 |
| LSP Server | Security Engine | Function Call | リアルタイム解析 |
| Security Engine | All Analyzers | Function Call | 解析実行 |
| Analyzers | YATA Client | GraphQL | 知識グラフ問い合わせ |
| Fix Generator | LLM Client | REST | 修正生成 |
| Fix Generator | Z3 Verifier | Function Call | 形式検証 |
| Dep Auditor | CVE Client | REST | 脆弱性照合 |

---

## 4. 技術スタック

### 4.1 コア技術

| カテゴリ | 技術 | バージョン | 用途 |
|---------|------|-----------|------|
| **言語** | TypeScript | 5.x | 主要実装言語 |
| **ランタイム** | Node.js | 20.x+ | 実行環境 |
| **パッケージマネージャ** | npm | 10.x+ | 依存関係管理 |
| **ビルド** | tsc | 5.x | TypeScriptコンパイル |
| **テスト** | Vitest | 1.x | ユニット/統合テスト |

### 4.2 解析技術

| カテゴリ | 技術 | 用途 |
|---------|------|------|
| **AST解析** | ts-morph | TypeScript/JavaScript AST操作 |
| **パターンマッチ** | semgrep (参考) | ルールベース検出 |
| **データフロー** | 自社実装 | テイント追跡 |
| **形式検証** | z3-solver (WASM) | 修正検証 |

### 4.3 外部連携

| カテゴリ | 技術 | 用途 |
|---------|------|------|
| **LLM** | OpenAI API, Anthropic API | 修正生成、説明生成 |
| **知識グラフ** | YATA Local/Global | セキュリティパターン |
| **CVEデータベース** | NVD API, OSV API | 脆弱性情報 |
| **MCP** | @modelcontextprotocol/sdk | AIエージェント統合 |
| **LSP** | vscode-languageserver | IDE統合 |

---

## 5. 設計決定記録 (ADR)

### ADR-001: Neuro-Symbolic統合アプローチ

**ステータス**: Accepted
**日付**: 2026-01-07

**コンテキスト**:
- 従来のSASTツールはパターンベースで誤検出が多い
- LLM単独では精度・一貫性に課題
- GitHub Advanced Securityを上回る精度が必要

**決定**:
Neuro-Symbolic統合アプローチを採用：
1. **Neural (LLM)**: コンテキスト理解、修正生成、説明生成
2. **Symbolic (YATA)**: 既知パターンマッチング、一貫性検証
3. **Formal (Z3)**: 修正の安全性証明

**結果**:
- 検出精度95%以上を実現可能
- 誤検出率5%未満を達成可能
- 修正の安全性を形式的に保証

**トレーサビリティ**: REQ-SEC2-SAST-002, REQ-SEC2-FIX-002

---

### ADR-002: プラグインアーキテクチャ

**ステータス**: Accepted
**日付**: 2026-01-07

**コンテキスト**:
- 多言語対応が必要（TypeScript, Python, Java, Go, Rust）
- カスタムルール対応が必要
- 将来の拡張性確保

**決定**:
言語別アナライザーをプラグインとして実装：
```
analyzers/
├── typescript/
├── python/
├── java/
├── go/
└── rust/
```

**結果**:
- 言語追加が容易
- カスタムルールの追加が容易
- テストの独立性確保

**トレーサビリティ**: REQ-SEC2-SAST-001, REQ-SEC2-EXT-001

---

### ADR-003: パイプラインアーキテクチャ

**ステータス**: Accepted
**日付**: 2026-01-07

**コンテキスト**:
- 複数の解析を効率的に実行する必要
- 解析結果の集約が必要
- 並列処理による高速化が必要

**決定**:
パイプライン＆フィルターパターンを採用：
```
Source → Parse → Analyze → Filter → Aggregate → Report
                    │
                    ├── SAST Pipeline
                    ├── Taint Pipeline
                    ├── Secret Pipeline
                    └── Dependency Pipeline
```

**結果**:
- 解析の並列実行が可能
- 段階的な処理で効率化
- 中間結果のキャッシュが可能

**トレーサビリティ**: REQ-SEC2-PERF-001

---

## 6. 次のステップ

1. **C4 Level 3: Component図** - 各コンテナ内部のコンポーネント詳細設計
2. **C4 Level 4: Code設計** - 主要クラス・インターフェースの詳細設計
3. **シーケンス図** - 主要フローの動的設計
4. **API設計** - CLI, MCP, LSP, RESTのインターフェース設計

---

## 7. 改訂履歴

| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|---------|--------|
| 0.1.0 | 2026-01-07 | 初版作成（Context, Container図） | AI Agent |

