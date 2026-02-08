# AGENTS.md — MUSUBIX v3.8.1

> **AI Agent向け最適化ナレッジ** — 実際のCLIコマンド・MCP APIに基づく正確なリファレンス

## クイックリファレンス

| 項目 | 値 |
|------|-----|
| バージョン | 3.8.1 |
| パッケージ数 | 25 |
| テスト数 | 5,738+ |
| MCP ツール | 107 |
| Agent Skills | 13 |
| パッケージマネージャ | npm (workspaces) |

---

## パッケージ構成

| カテゴリ | パッケージ | 用途 |
|----------|------------|------|
| **Core** | `@nahisaho/musubix-core` | CLI・EARS検証・コード生成・設計パターン |
| | `@musubix/knowledge` | Git-friendly JSON知識グラフ (ゼロ依存) |
| | `@nahisaho/musubix-codegraph` | コード解析・依存関係追跡 (16言語) |
| | `@nahisaho/musubi` | AI要約 |
| **SDD** | `@nahisaho/musubix-sdd-ontology` | SDD方法論オントロジー |
| | `@musubix/decisions` | ADR管理 (ゼロ依存) |
| | `@nahisaho/musubix-synthesis` | プログラム合成 |
| | `@musubix/policy` | 9憲法条項検証 |
| **Verification** | `@nahisaho/musubix-formal-verify` | Z3/Hoare形式検証 |
| | `@nahisaho/musubix-lean` | Lean4連携 |
| **Agent** | `@nahisaho/musubix-assistant-axis` | マルチモーダル統合 |
| | `@nahisaho/musubix-expert-delegation` | 7種AI専門家委譲 |
| | `@nahisaho/musubix-skill-manager` | スキル動的ロード |
| | `@nahisaho/musubix-agent-orchestrator` | 階層的オーケストレーション |
| **Learning** | `@nahisaho/musubix-wake-sleep` | Wake-Sleep自律学習 |
| | `@nahisaho/musubix-deep-research` | AI深層調査 |
| | `@nahisaho/musubix-library-learner` | ライブラリ学習 |
| **Search** | `@nahisaho/musubix-neural-search` | ベクトル・ハイブリッド検索 |
| **Workflow** | `@nahisaho/musubix-workflow-engine` | DAGワークフロー |
| | `@nahisaho/musubix-dfg` | データフローグラフ |
| **Security** | `@nahisaho/musubix-security` | 脆弱性・シークレット検出 |
| **MCP** | `@nahisaho/musubix-mcp-server` | MCP統合サーバー (107ツール) |
| | `@nahisaho/musubix-ontology-mcp` | オントロジーMCP |
| | `@nahisaho/musubix-pattern-mcp` | パターンMCP |
| **CLI** | `musubix` | CLIエントリポイント |

---

## CLI コマンド（実際の `--help` 出力に基づく）

### プロジェクト初期化・スキャフォールド

```bash
npx musubix init [path] [--name <name>] [--force]
npx musubix scaffold domain-model <name> -e "Entity1,Entity2" [-d PREFIX] [-v "VO1"] [-s "Entity=status"]
npx musubix scaffold minimal <name>
npx musubix scaffold api-service <name>
```

### 要件分析（EARS形式）

```bash
npx musubix requirements analyze <file>     # 自然言語 → EARS変換
npx musubix requirements validate <file>    # EARS構文検証
npx musubix requirements map <file>         # オントロジーマッピング
npx musubix requirements search <query>     # 関連要件検索
npx musubix requirements new <feature>      # 対話的要件作成
```

### 設計生成・検証

```bash
npx musubix design generate <requirements>  # 要件→設計生成
npx musubix design validate <file>          # SOLID準拠検証
npx musubix design c4 <file>                # C4ダイアグラム生成
npx musubix design adr <decision>           # ADR生成
npx musubix design patterns <context>       # パターン検出
npx musubix design traceability [--min-coverage 80]  # REQ↔DES検証
```

### コード生成・解析

```bash
npx musubix codegen generate <design>       # 設計→コード生成
npx musubix codegen generate <design> --full-skeleton  # 4ファイル生成
npx musubix codegen generate <design> --with-tests     # テスト付き
npx musubix codegen analyze <path>          # 静的解析
npx musubix codegen security <path>         # セキュリティスキャン
npx musubix codegen status <spec> [--enum]  # ステータス遷移コード生成
```

### テスト・トレーサビリティ

```bash
npx musubix test generate <path>            # テスト生成
npx musubix test coverage <dir>             # カバレッジ測定
npx musubix trace matrix [-p <project>]     # トレーサビリティマトリクス
npx musubix trace impact <id>               # 影響分析
npx musubix trace validate                  # リンク検証
npx musubix trace sync [--dry-run]          # 自動更新
```

### 自己学習システム

```bash
npx musubix learn status                    # 学習ダッシュボード
npx musubix learn dashboard                 # インタラクティブダッシュボード
npx musubix learn patterns                  # パターン一覧
npx musubix learn best-practices [--category code|design|test] [--high-confidence]
npx musubix learn bp-list                   # ベストプラクティスID一覧
npx musubix learn bp-show <id>              # ベストプラクティス詳細
npx musubix learn recommend -a <type>       # 推奨（-a 必須: code|design|test）
npx musubix learn feedback <artifactId>     # フィードバック記録
npx musubix learn add-pattern <name>        # パターン手動登録
npx musubix learn remove-pattern <id>       # パターン削除
npx musubix learn decay                     # 未使用パターン減衰
npx musubix learn wake                      # Wakeフェーズ実行
npx musubix learn sleep                     # Sleepフェーズ実行
npx musubix learn cycle                     # Wake-Sleep完全サイクル
npx musubix learn compress                  # パターン圧縮・最適化
npx musubix learn export [--output <file>] [--privacy-filter]
npx musubix learn import <file> [--merge-strategy skip|overwrite|merge]
```

### 知識グラフ (Knowledge)

```bash
npx musubix knowledge add <type> <id> <name>  # エンティティ追加
npx musubix knowledge get <id>                 # エンティティ取得
npx musubix knowledge delete <id>              # エンティティ削除
npx musubix knowledge link <source> <type> <target>  # リレーション追加
npx musubix knowledge query [--type <type>]    # クエリ検索
npx musubix knowledge traverse <id>            # グラフ走査
npx musubix knowledge stats                    # 統計表示
```

### ADR (Architecture Decision Records)

```bash
npx musubix decision create <title>         # ADR作成
npx musubix decision list                   # ADR一覧
npx musubix decision get <id>               # ADR詳細
npx musubix decision accept <id>            # ADR承認
npx musubix decision deprecate <id>         # ADR廃止
npx musubix decision search <query>         # ADRキーワード検索
npx musubix decision index                  # ADRインデックス生成
```

### ポリシー検証

```bash
npx musubix policy validate [path]          # プロジェクト検証
npx musubix policy list                     # ポリシー一覧
npx musubix policy info <id>                # ポリシー詳細
npx musubix policy check <file>             # 単一ファイル検証
```

### コードグラフ (16言語対応)

```bash
npx musubix cg index <path>                 # インデックス作成
npx musubix cg query [name]                 # エンティティ検索
npx musubix cg search <query>               # セマンティック検索
npx musubix cg deps <name>                  # 依存関係
npx musubix cg callers <name>               # 呼び出し元
npx musubix cg callees <name>               # 呼び出し先
npx musubix cg languages                    # 対応言語一覧
npx musubix cg stats                        # 統計
```

### オントロジー・説明生成

```bash
npx musubix ontology validate               # 知識グラフ整合性検証
npx musubix ontology check-circular          # 循環依存チェック
npx musubix ontology stats                   # 統計表示
npx musubix explain why <id>                 # 決定理由の説明
npx musubix explain graph <id>               # 推論グラフ生成
```

### その他

```bash
npx musubix library learn <file>             # コードからパターン学習
npx musubix library query <query>            # パターン検索
npx musubix library stats                    # パターン統計
npx musubix synthesize <examples.json>       # プログラム合成
npx musubix synthesize pbe <examples.json>   # PBE特化合成
npx musubix deep-research <query> [-i <iterations>] [-o <file>]
npx musubix perf benchmark                   # パフォーマンスベンチマーク
npx musubix perf startup                     # 起動時間計測
npx musubix perf memory                      # メモリ使用量
npx musubix skills list                      # スキル一覧
npx musubix skills validate [skill-name]     # スキル検証
npx musubix tasks list                       # タスク一覧
npx musubix tasks stats                      # タスク統計
npx musubix watch [paths...] [--lint] [--test] [--security]
npx musubix repl                             # 対話的REPL
```

---

## MCP Server

### 起動

```bash
npx @nahisaho/musubix-mcp-server
npx musubix-mcp --transport stdio
```

### 主要MCPツール

| カテゴリ | ツール名 | 説明 |
|----------|---------|------|
| **SDD** | `sdd_create_requirements` | EARS形式要件作成 |
| | `sdd_validate_requirements` | EARS検証・憲法準拠チェック |
| | `sdd_create_design` | C4モデル設計作成 |
| | `sdd_validate_design` | 設計トレーサビリティ検証 |
| | `sdd_create_tasks` | 設計→タスク生成 |
| | `sdd_validate_constitution` | 9憲法条項検証 |
| | `sdd_validate_traceability` | 全体トレーサビリティ検証 |
| **Pattern** | `pattern_extract` | パターン抽出 |
| | `pattern_compress` | パターン圧縮 |
| | `pattern_store` | パターン保存 |
| | `pattern_query` | パターン検索 |
| | `pattern_consolidate` | パターン統合 |
| | `ontology_query` | オントロジークエリ |
| | `ontology_infer` | オントロジー推論 |
| **Validation** | `consistency_validate` | 整合性検証 |
| | `validate_triple` | トリプル検証 |
| | `check_circular` | 循環依存検出 |
| **Knowledge** | `knowledge_put_entity` | エンティティ作成・更新 |
| | `knowledge_get_entity` | エンティティ取得 |
| | `knowledge_delete_entity` | エンティティ削除 |
| | `knowledge_add_relation` | リレーション追加 |
| | `knowledge_query` | グラフクエリ |
| | `knowledge_traverse` | グラフ走査 |
| **Policy** | `policy_validate` | ポリシー検証 |
| | `policy_list` | ポリシー一覧 |
| | `policy_get` | ポリシー詳細 |
| | `policy_check_file` | ファイル検証 |
| **Decision** | `decision_create` | ADR作成 |
| | `decision_list` | ADR一覧 |
| | `decision_get` | ADR詳細 |
| | `decision_accept` | ADR承認 |
| | `decision_deprecate` | ADR廃止 |
| | `decision_search` | ADR検索 |
| | `decision_find_by_requirement` | 要件→ADR検索 |
| | `decision_generate_index` | インデックス生成 |
| **Synthesis** | `synthesis_from_examples` | プログラム合成 |
| | `synthesis_analyze_examples` | 例題分析 |
| | `synthesis_learn_patterns` | パターン学習 |
| | `synthesis_query_patterns` | パターン検索 |
| | `synthesis_get_stats` | 統計取得 |
| **Orchestrator** | `agent_analyze_complexity` | タスク複雑度分析 |
| | `agent_dispatch` | サブエージェントディスパッチ |
| | `agent_collect_results` | 結果収集・統合 |
| | `agent_get_status` | 実行状態取得 |
| **Workflow** | `workflow_create` | ワークフロー作成 |
| | `workflow_advance_phase` | フェーズ遷移 |
| | `workflow_set_approval` | 承認設定 |
| | `workflow_get_status` | 状態取得 |
| | `workflow_validate_transition` | 遷移事前検証 |
| **Skill** | `skill_register` | スキル登録 |
| | `skill_execute` | スキル実行 |
| | `skill_list` | スキル一覧 |
| | `skill_get_info` | スキル詳細 |
| | `skill_validate` | スキル検証 |

---

## 9憲法条項

| # | 条項 | ルール |
|---|------|--------|
| I | Library-First | 機能は独立ライブラリとして開始 |
| II | CLI Interface | すべてのライブラリはCLI公開必須 |
| III | Test-First | Red-Green-Blueサイクルでテスト先行 |
| IV | EARS Format | 要件はEARS形式で記述 |
| V | Traceability | REQ↔DES↔CODE↔TESTの100%追跡 |
| VI | Project Memory | steering/ を参照してから決定 |
| VII | Design Patterns | 設計パターン適用の文書化 |
| VIII | Decision Records | すべての決定をADRで記録 |
| IX | Quality Gates | フェーズ移行前の品質検証 |

---

## 推奨ワークフロー

> **重要**: Phase 2（設計）から直接Phase 4（実装）に進むことは禁止。必ずPhase 3（タスク分解）を経ること。

```
Phase 1: 要件定義  │ steering/読込 → requirements analyze → レビュー → 承認
       ↓
Phase 2: 設計      │ design generate → design validate → レビュー → 承認
       ↓
Phase 3: タスク分解 │ タスク定義 → 依存関係整理 → レビュー → 承認
       ↓
Phase 4: 実装      │ test generate(Red) → 実装(Green) → リファクタ(Blue)
       ↓
Phase 5: 完了      │ trace validate → CHANGELOG更新 → コミット
```

---

## 開発コマンド

```bash
npm install              # 依存関係インストール
npm run build            # 全パッケージビルド (tsc -b)
npm run test             # 全テスト
npm run test:unit        # ユニットテスト
npm run test:integration # 統合テスト
npm run test:coverage    # カバレッジ計測
npm run lint             # ESLint
npm run lint:fix         # ESLint自動修正
npm run typecheck        # TypeScript型チェック
npm run format           # Prettier
npm run format:check     # Prettierチェック
npm run clean            # クリーンアップ
```

---

**最終更新**: 2026-02-08 | **バージョン**: 3.8.1
