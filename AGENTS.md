# AGENTS.md — MUSUBIX v3.7.2

> **AI Agent向け最適化ナレッジ** — WHEN/DO構文で明確なトリガーとアクションを定義

## 🎯 クイックリファレンス

| 項目 | 値 |
|------|-----|
| バージョン | 3.7.2 |
| テストカバレッジ | 92%+ |
| パッケージ数 | 28 |
| MCP ツール | 114 |
| Agent Skills | 15 |

---

## 📦 パッケージ構成

| カテゴリ | パッケージ | 用途 |
|----------|------------|------|
| **Core** | `@musubix/core` | エンティティ・値オブジェクト |
| | `@musubix/knowledge` | ナレッジグラフ CRUD |
| | `@musubix/musubi` | AI要約（300字以内） |
| | `@musubix/codegraph` | コード解析・依存関係抽出 |
| **SDD** | `@musubix/sdd-ontology` | オントロジー管理 |
| | `@musubix/decisions` | ADR管理・トレーサビリティ |
| | `@musubix/synthesis` | 情報統合 |
| **Verification** | `@musubix/formal-verify` | Lean4形式検証 |
| | `@musubix/lean` | Lean4連携 |
| | `@musubix/policy` | ルール駆動検証 |
| **Agent** | `@musubix/assistant-axis` | マルチモーダル統合 |
| | `@musubix/expert-delegation` | 専門家委譲 |
| | `@musubix/skill-manager` | スキル動的ロード |
| | `@musubix/agent-orchestrator` | 階層的オーケストレーション |
| **Learning** | `@musubix/wake-sleep` | 自律学習 |
| | `@musubix/deep-research` | 深層調査 |
| | `@musubix/library-learner` | ライブラリ学習 |
| **Search** | `@musubix/neural-search` | ベクトル・ハイブリッド検索 |
| **Workflow** | `@musubix/workflow-engine` | DAGワークフロー |
| | `@musubix/dfg` | データフローグラフ |
| **MCP** | `@musubix/mcp-server` | MCP統合サーバー |
| | `@musubix/ontology-mcp` | オントロジーMCP |
| | `@musubix/pattern-mcp` | パターンMCP |

---

## 🛠️ CLI コマンド

### 基本操作

```bash
# プロジェクト全体
pnpm i && pnpm build && pnpm test

# 個別パッケージ
pnpm --filter @musubix/core test
pnpm --filter @musubix/knowledge test
```

### ナレッジ操作

```bash
# 追加・検索
musubix knowledge add --source ./src --output ./knowledge.json
musubix knowledge search "認証" --semantic --top-k 5

# コードグラフ
musubix codegraph analyze ./src --include-dependencies
musubix codegraph query "関数 -> 依存関係"
```

### SDD ワークフロー

```bash
# 仕様駆動開発
musubix sdd init --domain "Eコマース" --output ./specs
musubix sdd validate ./specs --strict
musubix sdd generate ./specs --output ./src
```

### MCP サーバー

```bash
# 起動
musubix-mcp serve
musubix-mcp serve --port 3000 --skills-dir ./skills
```

---

## 🔌 MCP ツール（主要）

| カテゴリ | ツール | 用途 |
|----------|--------|------|
| **Knowledge** | `knowledge_add`, `knowledge_search`, `knowledge_import`, `knowledge_export` | ナレッジ CRUD |
| **CodeGraph** | `codegraph_analyze`, `codegraph_query`, `codegraph_visualize` | コード解析 |
| **SDD** | `sdd_init`, `sdd_validate`, `sdd_generate`, `sdd_trace` | 仕様駆動開発 |
| **Wake-Sleep** | `wake_observe`, `wake_optimize`, `sleep_consolidate`, `sleep_generate` | 自律学習 |
| **Formal** | `formal_translate`, `formal_verify`, `formal_prove` | 形式検証 |
| **Search** | `neural_search`, `hybrid_search`, `graph_search` | 検索 |

**全114ツール**: `musubix-mcp list-tools` で確認

---

## 📜 10憲法条項

| # | 条項 | ルール |
|---|------|--------|
| 1 | コンテキスト最優先 | Steering/product.ja.md, structure.ja.md を必ず参照 |
| 2 | ナレッジ駆動 | 既存知識を検索・活用してから回答 |
| 3 | 仕様駆動 (SDD) | 要件→設計→実装→検証の順序厳守 |
| 4 | トレーサビリティ | 決定事項は ADR として記録 |
| 5 | 段階的詳細化 | 抽象から具体へ、一度に1レベル |
| 6 | 自律学習 | Wake-Sleepサイクルで継続的改善 |
| 7 | 形式検証 | 重要ロジックはLean4で証明 |
| 8 | パターン適用 | 学習済みベストプラクティスを活用 |
| 9 | 明示的コミュニケーション | 不明点は確認、仮定を明示 |
| 10 | 品質最優先 | テスト・レビュー・検証を省略しない |

---

## 🧭 Project Memory（Steering）

| ファイル | 用途 | 参照タイミング |
|----------|------|----------------|
| `steering/product.ja.md` | 製品ビジョン・ゴール | プロジェクト理解時 |
| `steering/structure.ja.md` | アーキテクチャ構造 | 設計・実装時 |
| `steering/tech.ja.md` | 技術スタック・制約 | 技術選定時 |
| `steering/project.yml` | プロジェクトメタデータ | CI/CD設定時 |
| `steering/rules/*.md` | ドメイン固有ルール | コード生成時 |

---

## 🔬 主要機能

### 1. Wake-Sleep 自律学習

```typescript
// WHEN: パターン学習が必要
// DO: Wake-Sleepサイクルを実行
const result = await wakeSleep.observe("./src/**/*.ts");
const patterns = await wakeSleep.consolidate(result);
await wakeSleep.apply(patterns);
```

### 2. Knowledge Graph

```typescript
// WHEN: 情報の関連付けが必要
// DO: エンティティとリレーションを追加
await knowledge.addEntity({ type: "Function", name: "auth" });
await knowledge.addRelation("auth", "uses", "jwt-library");
const related = await knowledge.search("認証", { semantic: true });
```

### 3. CodeGraph 解析

```typescript
// WHEN: コード依存関係の把握が必要
// DO: 解析してクエリ実行
const graph = await codegraph.analyze("./src");
const deps = await codegraph.query("Function -> Dependency");
```

### 4. SDD ワークフロー

```typescript
// WHEN: 新機能の仕様策定
// DO: init → validate → generate
await sdd.init({ domain: "Payment", output: "./specs" });
await sdd.validate("./specs", { strict: true });
await sdd.generate("./specs", { output: "./src" });
```

### 5. Formal Verification

```typescript
// WHEN: 重要ロジックの証明が必要
// DO: Lean4に変換して検証
const leanCode = await formal.translate(tsCode);
const proof = await formal.verify(leanCode);
```

---

## 📚 学習済みベストプラクティス

| パターン | 適用条件 | 効果 |
|----------|----------|------|
| Result型 | エラーハンドリング | 型安全なエラー処理 |
| Repository | データアクセス | 永続化層の抽象化 |
| ValueObject | 不変データ | 値の整合性保証 |
| AggregateRoot | 整合性境界 | トランザクション境界の明確化 |
| CQRS | 読み書き分離 | パフォーマンス最適化 |
| EventSourcing | 状態追跡 | 完全な監査証跡 |
| DomainEvent | 疎結合通知 | モジュール間の依存削減 |
| Specification | 条件カプセル化 | 再利用可能なビジネスルール |
| Factory | 生成ロジック | 複雑なオブジェクト生成の隠蔽 |
| Strategy | アルゴリズム切替 | 実行時の振る舞い変更 |

---

## 🤖 Agent Skills（15スキル）

### Core Skills

| スキル | トリガー | 機能 |
|--------|----------|------|
| `knowledge-capture` | 新情報入力時 | エンティティ抽出・関係構築 |
| `knowledge-integration` | 統合要求時 | 複数ソースの知識統合 |
| `structured-summary` | 要約要求時 | 構造化300字要約 |
| `deep-research` | 調査要求時 | 多段階深層調査 |
| `learning-extraction` | パターン発見時 | ベストプラクティス抽出 |

### SDD Skills

| スキル | トリガー | 機能 |
|--------|----------|------|
| `musubix-domain-inference` | 要件分析時 | ドメインモデル推論 |
| `musubix-sdd-workflow` | SDD開始時 | 仕様駆動開発ガイド |
| `musubix-code-generation` | コード生成時 | SDD準拠コード生成 |
| `musubix-test-generation` | テスト生成時 | 仕様ベーステスト生成 |
| `musubix-traceability` | 追跡確認時 | 要件-実装追跡 |

### Documentation Skills

| スキル | トリガー | 機能 |
|--------|----------|------|
| `musubix-adr-generation` | 決定記録時 | ADR自動生成 |
| `musubix-c4-design` | 設計図作成時 | C4モデル生成 |
| `musubix-technical-writing` | 文書作成時 | 技術文書生成 |
| `musubix-best-practices` | ノウハウ整理時 | ベストプラクティス文書化 |
| `musubix-ears-validation` | 要件検証時 | EARS構文検証 |

---

## 📋 AI Agent ガイドライン

### WHEN: 新規タスク開始

```
DO:
1. steering/ を読んでコンテキスト把握
2. knowledge search で既存知識確認
3. 関連 ADR を確認
4. 必要なスキルを特定
```

### WHEN: コード生成

```
DO:
1. SDD ワークフローに従う
2. 学習済みパターンを適用
3. テストを同時生成
4. トレーサビリティを維持
```

### WHEN: エラー発生

```
DO:
1. Result型でエラーをラップ
2. コンテキスト情報を付加
3. リカバリー戦略を検討
4. 学習データとして記録
```

### WHEN: 不明点がある

```
DO:
1. 仮定を明示して確認を求める
2. 複数の選択肢を提示
3. 決定事項は ADR に記録
```

---

## 🔄 推奨ワークフロー

```
Phase 1: Context   │ steering/ 読込 → knowledge search → ADR確認
        ↓
Phase 2: Plan      │ スキル選定 → タスク分解 → 依存関係整理
        ↓
Phase 3: Execute   │ SDD準拠実装 → パターン適用 → テスト生成
        ↓
Phase 4: Verify    │ 形式検証 → トレーサビリティ確認 → レビュー
        ↓
Phase 5: Learn     │ Wake-Sleep → パターン抽出 → ナレッジ更新
```

---

## 📁 ストレージ構造

| ディレクトリ | 用途 |
|--------------|------|
| `storage/learning/` | 学習データ |
| `storage/specs/` | SDD仕様 |
| `storage/design/` | 設計文書 |
| `storage/changes/` | 変更履歴 |
| `storage/reviews/` | レビュー記録 |
| `storage/dashboard/` | メトリクス |

---

## 🚨 重要な制約

| 制約 | 理由 |
|------|------|
| Node.js 20+ | ESM・最新API |
| TypeScript strict | 型安全性 |
| pnpm workspace | モノレポ管理 |
| Vitest | 高速テスト |
| ESLint flat config | 統一リント |

---

## 📞 トラブルシューティング

| 症状 | 対処 |
|------|------|
| 依存解決エラー | `pnpm i --force` |
| 型エラー | `pnpm build` で再ビルド |
| テスト失敗 | `pnpm --filter <pkg> test` で個別実行 |
| MCP接続失敗 | ポート確認、`--debug` オプション |

---

**最終更新**: 2025-01-29 | **バージョン**: 3.7.2
