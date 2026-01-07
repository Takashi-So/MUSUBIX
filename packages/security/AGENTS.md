# MUSUBIX - Neuro-Symbolic AI Integration System

> **AI Coding Agent向け**: このファイルはAIエージェント（GitHub Copilot、Claude等）がMUSUBIXプロジェクトを理解するためのガイドです。

## 🎯 プロジェクト概要

**MUSUBIX**は、**Neural（LLM）** と **Symbolic（Knowledge Graph）** 推論を統合した次世代AIコーディングシステムです。MUSUBI SDD方法論とYATA知識グラフ推論を組み合わせ、高品質なソフトウェア開発を支援します。

| 項目 | 詳細 |
|------|------|
| **バージョン** | 1.8.0 (Security Analysis Edition) |
| **言語** | TypeScript |
| **ランタイム** | Node.js >= 20.0.0 |
| **パッケージマネージャ** | npm >= 10.0.0 |
| **ビルドシステム** | モノレポ（npm workspaces） |
| **テストフレームワーク** | Vitest |
| **テスト数** | 1586 (全合格) |
| **コンポーネント数** | 249 (62ドメイン対応) |
| **Agent Skills** | 12 (Claude Code対応) |

---

## 📦 アーキテクチャ

### パッケージ構成

```
packages/
├── core/           # @nahisaho/musubix-core
├── mcp-server/     # @nahisaho/musubix-mcp-server  
├── security/       # @nahisaho/musubix-security (NEW!)
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

| パッケージ | npm | 役割 |
|-----------|-----|------|
| `packages/core/` | `@nahisaho/musubix-core` | コアライブラリ - CLI、EARS検証、コード生成、設計パターン |
| `packages/mcp-server/` | `@nahisaho/musubix-mcp-server` | MCPサーバー - 19ツール、3プロンプト |
| `packages/security/` | `@nahisaho/musubix-security` | **セキュリティ分析** - 脆弱性検出、シークレット検出、テイント解析 (NEW!) |
| `packages/formal-verify/` | `@nahisaho/musubix-formal-verify` | 形式検証 - Z3統合、Hoare検証、EARS→SMT変換 |
| `packages/yata-client/` | `@nahisaho/musubix-yata-client` | YATAクライアント - 知識グラフ連携 |
| `packages/yata-local/` | `@nahisaho/yata-local` | **YATA Local** - SQLiteベースローカル知識グラフ |
| `packages/yata-global/` | `@nahisaho/yata-global` | **YATA Global** - 分散型知識グラフプラットフォーム |
| `packages/yata-ui/` | `@nahisaho/yata-ui` | **YATA UI** - Web可視化・管理インターフェース |
| `packages/pattern-mcp/` | `@nahisaho/musubix-pattern-mcp` | パターン学習 - 抽出・圧縮・ライブラリ |
| `packages/ontology-mcp/` | `@nahisaho/musubix-ontology-mcp` | オントロジー - N3Store・推論エンジン |
| `packages/wake-sleep/` | `@nahisaho/musubix-wake-sleep` | Wake-Sleep学習サイクル |
| `packages/sdd-ontology/` | `@nahisaho/musubix-sdd-ontology` | SDD方法論オントロジー |

### Core パッケージモジュール

```
packages/core/src/
├── auth/           # 認証・認可
├── cli/            # CLIインターフェース
├── codegen/        # コード生成・解析
├── design/         # 設計パターン・C4モデル
├── error/          # エラーハンドリング
├── explanation/    # 説明生成・可視化
├── learning/       # 自己学習システム
├── requirements/   # 要件分析・分解
├── symbolic/       # シンボリック推論（v1.2.0 NEW!）
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
npx musubix trace matrix -p <project>      # 指定プロジェクトのマトリクス
npx musubix trace impact <id>              # 影響分析
npx musubix trace validate                 # リンク検証
npx musubix trace sync                     # トレースマトリクス自動更新 (v1.6.7 NEW!)
npx musubix trace sync --dry-run           # プレビューのみ

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
  # オプション: --output <file>, --privacy-filter, --patterns-only, --feedback-only, --min-confidence <n>
npx musubix learn import <file>            # 学習データインポート
  # オプション: --merge-strategy <skip|overwrite|merge>, --dry-run, --patterns-only, --feedback-only

# オントロジー操作 (v1.4.1 NEW!)
npx musubix ontology validate -f <file>    # 知識グラフ整合性検証
npx musubix ontology check-circular -f <file>  # 循環依存チェック
npx musubix ontology stats -f <file>       # 統計表示

# Interactive REPL (v1.5.0 NEW!)
npx musubix repl                           # 対話的シェルを起動
npx musubix repl --history <file>          # カスタム履歴ファイル
npx musubix repl --no-color                # 色なしモード

# KGPR - Knowledge Graph Pull Request (v1.6.4 NEW!)
npx musubix kgpr create -t "title"         # KGPR作成
npx musubix kgpr diff                      # 差分プレビュー
npx musubix kgpr list                      # KGPR一覧
npx musubix kgpr submit <id>               # KGPR送信
npx musubix kgpr show <id>                 # KGPR詳細表示
npx musubix kgpr close <id>                # KGPRクローズ
  # オプション: --namespace <ns>, --entity-types <types>, --privacy <strict|moderate|none>

# SDDプロジェクトスキャフォールド (v1.6.7 NEW!)
npx musubix scaffold domain-model <name>   # DDDプロジェクト生成
npx musubix scaffold domain-model <name> -e "Entity1,Entity2"  # エンティティ指定
npx musubix scaffold domain-model <name> -d DOMAIN  # ドメイン接頭辞指定
npx musubix scaffold minimal <name>        # 最小構成プロジェクト

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

### ツール一覧（24ツール）

#### SDD基本ツール（9ツール）

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

#### パターン統合ツール（7ツール）- v1.3.0 NEW!

| ツール名 | 説明 |
|---------|------|
| `pattern_extract` | コードからパターンを抽出 |
| `pattern_compress` | パターンの抽象化・圧縮 |
| `pattern_store` | パターンライブラリへの保存 |
| `pattern_query` | パターンの検索・取得 |
| `pattern_consolidate` | 類似パターンの統合 |
| `ontology_query` | オントロジーグラフへのクエリ |
| `ontology_infer` | オントロジーによる推論実行 |

#### オントロジー検証ツール（3ツール）- v1.4.1 NEW!

| ツール名 | 説明 |
|---------|------|
| `consistency_validate` | 知識グラフの整合性検証 |
| `validate_triple` | 単一トリプルの事前検証 |
| `check_circular` | 循環依存の検出 |

#### KGPRツール（5ツール）- v1.6.4 NEW!

| ツール名 | 説明 |
|---------|------|
| `kgpr_create` | KGPR作成（ローカルKGからドラフト作成） |
| `kgpr_diff` | 差分プレビュー |
| `kgpr_list` | KGPR一覧表示 |
| `kgpr_submit` | KGPR送信（レビュー用） |
| `kgpr_review` | KGPRレビュー（approve/changes_requested/commented） |

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

### 6. Wake-Sleep学習サイクル（v1.3.0 NEW!）

Wake-Sleepアルゴリズムに基づいた継続的学習システム：

| フェーズ | 処理内容 |
|---------|----------|
| **Wake** | コード観察 → パターン抽出 → 知識グラフ更新 |
| **Sleep** | パターン統合 → 類似パターン圧縮 → メモリ最適化 |

```
Wake Phase: observe() → extractPatterns() → updateKnowledge()
Sleep Phase: consolidate() → compress() → optimize()
```

**主要コンポーネント**:
- `WakeSleepCycle`: 学習サイクル全体の制御
- `PatternLibrary`: 学習済みパターンの永続化管理
- `PatternOntologyBridge`: パターン↔オントロジー相互変換
- `N3Store`: RDF/OWLベースの知識グラフストレージ

---

## 📚 学習済みベストプラクティス（v1.1.10 Updated!）

Project-07〜14の実装から学習したパターンです。

### コードパターン

| ID | 名称 | 概要 | 信頼度 |
|----|------|------|--------|
| BP-CODE-001 | Entity Input DTO | エンティティ作成にInput DTOオブジェクトを使用 | 95% |
| BP-CODE-002 | Date-based ID Format | PREFIX-YYYYMMDD-NNN形式でIDを生成 | 90% |
| BP-CODE-003 | Value Objects | ドメイン概念にValue Objectを使用 | 90% |
| BP-CODE-004 | Function-based Value Objects | クラスではなくinterface+factory関数でVO実装 | 95% |
| BP-CODE-005 | Result Type | 失敗可能な操作にResult<T, E>を使用 | 95% |

**Function-based Value Object例**:
```typescript
// ✅ 推奨: Interface + Factory Function
interface Price {
  readonly amount: number;
  readonly currency: 'JPY';
}

function createPrice(amount: number): Result<Price, ValidationError> {
  if (amount < 100 || amount > 1_000_000) {
    return err(new ValidationError('Price must be between 100 and 1,000,000 JPY'));
  }
  return ok({ amount, currency: 'JPY' });
}

// ❌ 非推奨: クラスベース（構造的型付けと相性が悪い）
class Price {
  private constructor(readonly amount: number) {}
  static create(amount: number): Price { ... }
}
```

### 設計パターン

| ID | 名称 | 概要 | 信頼度 |
|----|------|------|--------|
| BP-DESIGN-001 | Status Transition Map | 有効なステータス遷移をMapで定義 | 95% |
| BP-DESIGN-002 | Repository Async Pattern | 将来のDB移行に備えてasync化 | 85% |
| BP-DESIGN-003 | Service Layer with DI | リポジトリをDIしたService層 | 90% |
| BP-DESIGN-004 | Optimistic Locking | 同時編集検出のためのversion管理 | 90% |
| BP-DESIGN-005 | AuditService | データ変更の監査ログ記録 | 85% |
| BP-DESIGN-006 | Entity Counter Reset | テスト用のresetXxxCounter()関数を提供 | 95% |
| BP-DESIGN-007 | Expiry Time Logic | 有効期限をexpiresAtフィールドで明示管理 | 90% |

**Status Transition Map例**:
```typescript
const validStatusTransitions: Record<Status, Status[]> = {
  draft: ['active', 'cancelled'],
  active: ['completed', 'cancelled'],
  completed: [],
  cancelled: [],
};
```

### テストパターン

| ID | 名称 | 概要 | 信頼度 |
|----|------|------|--------|
| BP-TEST-001 | Test Counter Reset | beforeEachでIDカウンターをリセット | 95% |
| BP-TEST-002 | Verify API Before Test | テスト前にAPIシグネチャを確認 | 80% |
| BP-TEST-003 | Vitest ESM Configuration | Vitest + TypeScript ESM構成 | 85% |
| BP-TEST-004 | Result Type Test Pattern | isOk()/isErr()で両方のケースをテスト | 95% |
| BP-TEST-005 | Status Transition Testing | 有効・無効な遷移を網羅的にテスト | 90% |

**Result Type Test例**:
```typescript
describe('createPrice', () => {
  it('should create valid price', () => {
    const result = createPrice(1000);
    expect(result.isOk()).toBe(true);
    if (result.isOk()) {
      expect(result.value.amount).toBe(1000);
    }
  });

  it('should reject price below minimum', () => {
    const result = createPrice(50);
    expect(result.isErr()).toBe(true);
    if (result.isErr()) {
      expect(result.error.message).toContain('100');
    }
  });
});
```

### CLIでベストプラクティスを表示

```bash
# 全ベストプラクティス表示
npx musubix learn best-practices

# カテゴリ別フィルタ
npx musubix learn best-practices --category code
npx musubix learn best-practices --category design
npx musubix learn best-practices --category test

# 高信頼度パターンのみ
npx musubix learn best-practices --high-confidence

# Markdown出力
npx musubix learn best-practices --format markdown
```

---

## �📚 ドキュメント

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
**Last Updated**: 2026-01-06
**Version**: 1.6.4
