# 5分で始めるMUSUBIX

> MUSUBIXは、AIコーディングエージェント（Claude Code, GitHub Copilot等）と連携し、「要件→設計→実装→検証」の品質を自動で保証するツールです。

---

## 前提条件

| 項目 | 要件 |
|------|------|
| **Node.js** | 20.0.0 以上 |
| **パッケージマネージャ** | npm 10.0.0 以上 または pnpm |
| **AIエージェント** | Claude Code, GitHub Copilot, Cursor のいずれか |

---

## Step 1: インストール（1分）

npm と pnpm のどちらか一方を選んでください。

### npm を使う場合

<details>
<summary>グローバルインストール（お試し・個人プロジェクト向け）</summary>

```bash
npm install -g musubix
```

**インストール先**: `$(npm config get prefix)/lib/node_modules/musubix/`
（例: `/usr/local/lib/node_modules/musubix/`、nvm使用時は `~/.nvm/versions/node/v22.x.x/lib/node_modules/musubix/`）

`musubix` コマンドがPATHに追加され、どのディレクトリからでも実行できます。

```bash
# 確認
musubix --version
```

</details>

<details open>
<summary>ローカルインストール（チーム開発向け・推奨）</summary>

```bash
cd your-project
npm install --save-dev musubix
```

**インストール先**: `your-project/node_modules/musubix/`

`package.json` の `devDependencies` に追加され、チーム全員が `npm install` で同じバージョンを使えます。実行時は `npx` を付けます。

```bash
# 確認
npx musubix --version
```

</details>

### pnpm を使う場合

<details>
<summary>グローバルインストール（お試し・個人プロジェクト向け）</summary>

```bash
pnpm add -g musubix
```

**インストール先**: pnpmのグローバルストア
（macOS: `~/Library/pnpm/global/5/node_modules/musubix/`、Linux: `~/.local/share/pnpm/global/5/node_modules/musubix/`）

`musubix` コマンドがPATHに追加され、どのディレクトリからでも実行できます。

```bash
# 確認
musubix --version
```

</details>

<details open>
<summary>ローカルインストール（チーム開発向け・推奨）</summary>

```bash
cd your-project
pnpm add -D musubix
```

**インストール先**: `your-project/node_modules/musubix/`（pnpmのコンテンツアドレッサブルストアからリンク）

`package.json` の `devDependencies` に追加され、チーム全員が `pnpm install` で同じバージョンを使えます。実行時は `pnpm dlx` または `pnpm exec` を付けます。

```bash
# 確認
pnpm exec musubix --version
```

</details>

> **チーム開発ではローカルインストールを推奨します。** `package.json` でバージョンが管理され、CI/CDでも再現性が高くなります。

---

## Step 2: プロジェクト初期化（1分）

```bash
# npm の場合
npx musubix init my-project

# pnpm の場合
pnpm dlx musubix init my-project
```

```bash
cd my-project
```

以下のファイル・ディレクトリが自動生成されます：

### プロジェクト設定

| 生成物 | 役割 |
|-------|------|
| `musubix.config.json` | プロジェクト設定（バージョン、パス、LLM設定等） |

### プロジェクトメモリ（steering/）

| 生成物 | 役割 |
|-------|------|
| `steering/rules/constitution.md` | 9つの憲法条項（品質ルールのテンプレート） |
| `steering/product.md` | プロダクトコンテキスト（テンプレート） |
| `steering/tech.md` | 技術スタック定義（テンプレート） |
| `steering/structure.md` | プロジェクト構造定義（テンプレート） |

### 成果物ストレージ（storage/）

| 生成物 | 役割 |
|-------|------|
| `storage/specs/` | 要件(REQ-*)・設計(DES-*)・タスク(TSK-*)の保存先 |
| `storage/archive/.gitkeep` | アーカイブ用ディレクトリ |
| `storage/changes/.gitkeep` | 変更履歴用ディレクトリ |

### AIエージェント設定

| 生成物 | 対象エージェント | 役割 |
|-------|----------------|------|
| `AGENTS.md` | GitHub Copilot | AI指示ファイル（プロジェクトルート） |
| `CLAUDE.md` | Claude Code | AI指示ファイル（プロジェクトルート） |
| `.github/copilot-instructions.md` | GitHub Copilot | Copilot固有の追加指示 |
| `.github/prompts/` | GitHub Copilot | 12個のSDDプロンプトテンプレート |
| `.github/skills/` | GitHub Copilot | 20個のスキル定義 |
| `.claude/CLAUDE.md` | Claude Code | Claude固有の追加指示 |
| `.claude/settings.json` | Claude Code | Claude Code設定 |
| `.claude/prompts/` | Claude Code | 12個のSDDプロンプトテンプレート |
| `.claude/skills/` | Claude Code | 20個のスキル定義 |

<details>
<summary>SDDプロンプト一覧（12ファイル）</summary>

| ファイル名 | 用途 |
|-----------|------|
| `sdd-requirements.prompt.md` | 要件定義 |
| `sdd-design.prompt.md` | 設計生成 |
| `sdd-tasks.prompt.md` | タスク分解 |
| `sdd-implement.prompt.md` | 実装 |
| `sdd-test.prompt.md` | テスト生成 |
| `sdd-review.prompt.md` | レビュー |
| `sdd-validate.prompt.md` | 検証 |
| `sdd-security.prompt.md` | セキュリティチェック |
| `sdd-steering.prompt.md` | ステアリング更新 |
| `sdd-change-init.prompt.md` | 変更管理初期化 |
| `sdd-change-apply.prompt.md` | 変更適用 |
| `sdd-change-archive.prompt.md` | 変更アーカイブ |

</details>

<details>
<summary>スキル一覧（20ディレクトリ）</summary>

**MUSUBIX SDDスキル（11個）**:

| スキル | 用途 |
|-------|------|
| `musubix-sdd-workflow/` | SDDワークフロー制御 |
| `musubix-ears-validation/` | EARS要件検証 |
| `musubix-c4-design/` | C4モデル設計 |
| `musubix-code-generation/` | コード生成 |
| `musubix-test-generation/` | テスト生成 |
| `musubix-adr-generation/` | ADR生成 |
| `musubix-traceability/` | トレーサビリティ管理 |
| `musubix-best-practices/` | ベストプラクティス適用 |
| `musubix-domain-inference/` | ドメイン推論 |
| `musubix-technical-writing/` | テクニカルライティング |

**開発補助スキル（9個）**:

| スキル | 用途 |
|-------|------|
| `checkpoint/` | Git状態スナップショット・復元 |
| `build-fix/` | ビルドエラー自動修正 |
| `verification-loop/` | 多段階検証（ビルド/型/lint/テスト） |
| `session-manager/` | セッション永続化・復元 |
| `learning-hooks/` | パターン自動学習 |
| `context-optimizer/` | コンテキスト圧縮最適化 |
| `codemap/` | リポジトリ構造解析 |
| `e2e-runner/` | E2Eテスト実行 |
| `eval-harness/` | 評価ハーネス |
| `refactor-cleaner/` | デッドコード検出・削除 |

</details>

---

## Step 3: AIエージェントで開発開始（3分）

**CLIコマンドを覚える必要はありません。** AIエージェントに自然言語で話しかけるだけです。

### 3-1. 要件定義

AIエージェントに以下のように話しかけます：

```
TODOアプリを開発したい。要件定義を開始して
```

AIエージェントが以下を自動で実行します：
1. コンテキスト不足時は明確化の質問を返す（WHY, WHO, CONSTRAINT等）
2. あなたが回答すると、EARS形式の要件ドキュメントを生成
3. 自動レビュー結果を表示

レビュー結果が表示されたら、内容を確認して：

```
承認
```

### 3-2. 設計

```
設計を作成して
```

C4モデルの設計ドキュメントが自動生成され、レビュー結果が表示されます。
確認して問題なければ：

```
承認
```

### 3-3. タスク分解

```
タスク分解して
```

設計が実装可能な単位のタスクに分解されます。確認して：

```
承認
```

### 3-4. 実装

```
実装を開始して
```

タスクごとにテスト先行（Red-Green-Blue）でコードが生成されます。

---

## 開発フローの全体像

```
要件定義 ──→ 設計 ──→ タスク分解 ──→ 実装 ──→ 完了
 (REQ-*)    (DES-*)    (TSK-*)      コード    CHANGELOG
    ↑          ↑          ↑
    └──────────┴──────────┘
    各フェーズで「レビュー→承認」の品質ゲート
```

> **重要**: 設計からタスク分解を飛ばして実装に進むことはできません。これは品質を保証するための不変ルールです。

---

## AIエージェント別セットアップ

### Claude Code を使う場合

追加設定は不要です。`musubix init` で生成された `.claude/` ディレクトリのファイルが自動的に使われます。

### GitHub Copilot を使う場合

追加設定は不要です。`AGENTS.md` と `.github/` ディレクトリのファイルが自動的に GitHub Copilot に読み込まれます。

### Cursor / Windsurf を使う場合

MCPサーバーの設定が必要です。`.cursor/mcp.json` を作成してください：

```json
{
  "mcpServers": {
    "musubix": {
      "command": "npx",
      "args": ["@nahisaho/musubix-mcp-server"]
    }
  }
}
```

---

## 次のステップ

| ドキュメント | 内容 |
|-------------|------|
| [プロンプトガイド](prompt-guide.md) | どんなプロンプトを書けばいいか、内部で何が起きるかの対応表 |
| [SDDワークフロー](workflow.md) | 開発フロー全体の詳細説明 |
| [チュートリアル](tutorial/01-setup.md) | 備品管理システムを実際に作るハンズオン |
| [よくある質問](faq.md) | セットアップ・ワークフローの疑問解消 |
