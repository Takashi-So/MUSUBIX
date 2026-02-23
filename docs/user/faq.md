# よくある質問（FAQ）

---

## 基本

### Q: MUSUBIXは何をするツールですか？

AIコーディングエージェント（Claude Code, GitHub Copilot等）が「正しいものを正しく作る」ための品質保証基盤です。要件→設計→実装→テストの各フェーズで自動レビューとトレーサビリティを提供します。

Vibe Coding（雰囲気でコーディング）では品質が不安定になりがちですが、MUSUBIXは**仕様駆動型開発（SDD）**によって一貫した品質を保証します。

### Q: GitHub CopilotやClaude Codeを置き換えるものですか？

いいえ。それらを**強化**するものです。

AIエージェントは「コードを素早く生成する」ことに優れていますが、「なぜそのコードを書くのか」「このコードは要件を満たしているか」という上流の品質管理は苦手です。MUSUBIXはこのギャップを埋めます。

| AIエージェント | MUSUBIX |
|--------------|---------|
| コード生成が得意 | 仕様・設計の構造化が得意 |
| 瞬時の補完・編集 | 長期的な知識の蓄積 |
| 創造的なソリューション | 一貫性と品質の保証 |
| 個別タスクの自動化 | プロジェクト全体の品質統治 |

### Q: CLIコマンドを覚える必要がありますか？

いいえ。AIエージェントに自然言語で話しかけるだけで、内部的にCLIコマンドが実行されます。

例:
- 「この機能の要件をEARS形式で分析して」→ 内部で `requirements analyze` が実行
- 「設計ドキュメントを生成して」→ 内部で `design generate` が実行

CLIを直接使うのはデバッグやスクリプト自動化の場合のみです。詳しくは[プロンプトガイド](prompt-guide.md)を参照してください。

### Q: 個人プロジェクトでも使えますか？

はい。ただし、MUSUBIXが最も価値を発揮するのはチーム開発やプロダクション品質が求められる場面です。

| ユースケース | 推奨 |
|-------------|------|
| プロトタイプ・実験 | MUSUBIXなしでOK（Vibe Codingで十分） |
| 個人の本格プロジェクト | MUSUBIXを推奨（品質維持に有効） |
| チーム開発 | MUSUBIXを強く推奨 |
| エンタープライズ・規制産業 | MUSUBIX必須（トレーサビリティが法的要件） |

### Q: MUSUBIとMUSUBIXの違いは？

MUSUBIはSDD実践のための汎用フレームワーク（前身）です。MUSUBIXはMUSUBIにNeuro-Symbolic AIを統合し、知識グラフ管理とSwarm Codingを実現した進化版です。

| 項目 | MUSUBI | MUSUBIX |
|-----|--------|---------|
| 知識管理 | プロジェクトメモリのみ | Git-Native知識グラフ |
| 推論 | LLMのみ | Neuro-Symbolic（LLM + シンボリック） |
| 学習 | なし | 自己学習システム |
| エージェント連携 | 7エージェント対応 | Claude Code + GitHub Copilotに最適化 |

### Q: 無料で使えますか？

はい。MUSUBIXはMITライセンスのオープンソースソフトウェアです。ただし、AIエージェント（Claude Code, GitHub Copilot等）自体の利用料金は各サービスに従います。

---

## セットアップ

### Q: Node.js 18でも動きますか？

いいえ。Node.js **20.0.0以上**が必須です。

<details>
<summary>npmを使っている場合</summary>

```bash
# バージョン確認
node --version

# nvmでアップグレード
nvm install 20
nvm use 20
```

</details>

<details>
<summary>pnpmを使っている場合</summary>

```bash
# バージョン確認
node --version

# nvmでアップグレード
nvm install 20
nvm use 20

# pnpmのNode.jsバージョン指定（package.json）
# "engines": { "node": ">=20.0.0" }
```

</details>

### Q: MCP設定は必要ですか？

AIエージェントによって異なります：

| AIエージェント | MCP設定 | 備考 |
|--------------|--------|------|
| Claude Code | 不要 | `.claude/` が自動利用される |
| GitHub Copilot | 不要 | `AGENTS.md` と `.github/` が自動利用される |
| Cursor | 必要 | `.cursor/mcp.json` を作成 |
| Windsurf | 必要 | MCP設定ファイルを作成 |

### Q: グローバルとローカル、どちらでインストールすべきですか？

| ユースケース | 推奨 | 理由 |
|-------------|------|------|
| チーム開発 | ローカル | 全員が同じバージョンを使用、CI/CDでも自動インストール |
| 個人（複数プロジェクト） | グローバル | 毎回インストール不要 |
| お試し・学習 | グローバル | 手軽に試せる |
| プロダクション | ローカル | 再現性が高い |

迷ったら**ローカルインストール**を選んでください。

インストール方法の詳細は[クイックスタート](quickstart.md)を参照してください。

### Q: `musubix init` で既存プロジェクトに追加できますか？

はい。既存のプロジェクトディレクトリで実行できます。

<details>
<summary>npmを使っている場合</summary>

```bash
cd existing-project
npx musubix init . --force
```

</details>

<details>
<summary>pnpmを使っている場合</summary>

```bash
cd existing-project
pnpm dlx musubix init . --force
```

</details>

`--force` オプションを付けると、既存の `musubix.config.json` を上書きします。AIエージェント設定ファイル（`AGENTS.md`, `CLAUDE.md`等）が既に存在する場合は上書きされません。

---

## ワークフロー

### Q: 「承認」と言わないと次に進めませんか？

はい。各フェーズ（要件→設計→タスク分解→実装）はユーザーの明示的な承認が必要です。これは品質ゲート（憲法条項 Article IX）の一部です。

承認キーワード：
- `承認` / `approve`
- `OK` / `LGTM`
- `進める`

### Q: 設計から直接実装に進めますか？

**いいえ。** 必ず「タスク分解」フェーズ（Phase 3）を経る必要があります。これは憲法条項で定められた不変のルールです。

```
Phase 2（設計）→ Phase 3（タスク分解）→ Phase 4（実装）  ✅ 正しい順序
Phase 2（設計）→ Phase 4（実装）                          ❌ 禁止
```

### Q: 要件定義を省略していきなり実装できますか？

技術的には可能ですが、MUSUBIXの品質保証メリットが失われます。少なくとも要件定義だけでも行うことを強く推奨します。

### Q: 9つの憲法条項とは何ですか？

MUSUBIXのすべての開発活動を統治する不変のルールです：

| # | 条項 | 概要 |
|---|------|------|
| I | Library-First | 機能は独立ライブラリとして開始 |
| II | CLI Interface | すべてのライブラリはCLI公開必須 |
| III | Test-First | テスト先行開発（Red-Green-Blue） |
| IV | EARS Format | 要件はEARS形式で記述 |
| V | Traceability | 要件↔設計↔コード↔テストの100%追跡 |
| VI | Project Memory | steering/を参照してから決定 |
| VII | Design Patterns | 設計パターン適用の文書化 |
| VIII | Decision Records | すべての決定をADRで記録 |
| IX | Quality Gates | フェーズ移行前の品質検証 |

詳しくは[SDDワークフロー](workflow.md)を参照してください。

### Q: レビューで指摘が消えない場合はどうすればいいですか？

指摘内容を確認し、AIエージェントに具体的に修正を依頼してください：

```
# 曖昧な指示（うまくいかないことが多い）
修正して

# 具体的な指示（推奨）
REQ-001に応答時間の基準（2秒以内）を追加して
```

修正後、再度レビューが自動実行されます。指摘がゼロになるまで繰り返してください。

### Q: EARS形式がよく分かりません

[SDDワークフロー](workflow.md)の「Phase 1: 要件定義」セクションに5つのパターンと具体例を記載しています。

簡単にまとめると：
- **常にやること** → `THE system SHALL ...`
- **何かが起きた時** → `WHEN ..., THE system SHALL ...`
- **ある状態の間** → `WHILE ..., THE system SHALL ...`
- **やってはいけないこと** → `THE system SHALL NOT ...`
- **条件付き** → `IF ..., THEN THE system SHALL ...`

---

## その他

### Q: 学習データはどこに保存されますか？

すべてローカルに保存されます。外部サーバーには送信されません。

- 知識グラフ: `.knowledge/graph.json`
- パターン学習: ローカルストレージ
- セッション: `~/.musubix/sessions/`

### Q: 複数人で同じプロジェクトを開発する場合は？

`steering/` と `storage/` ディレクトリをGitで管理してください。これにより、要件・設計・タスクの変更履歴がチーム全体で共有されます。

### Q: バグを見つけた / 機能リクエストしたい

GitHubのIssueで報告してください：
https://github.com/nahisaho/MUSUBIX/issues

---

## 関連ドキュメント

| ドキュメント | 内容 |
|-------------|------|
| [クイックスタート](quickstart.md) | 5分で始めるMUSUBIX |
| [プロンプトガイド](prompt-guide.md) | プロンプト例と内部処理の対応表 |
| [SDDワークフロー](workflow.md) | 開発フロー全体の詳細 |
| [トラブルシューティング](troubleshooting.md) | エラー別の対処法 |
