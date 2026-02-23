# トラブルシューティング

エラーメッセージ別の対処法をまとめています。

---

## インストール・環境

### Node.jsバージョンエラー

```
Error: MUSUBIX requires Node.js >= 20.0.0
```

**原因**: Node.js 18以下を使用しています。

**対処法**:
```bash
# 現在のバージョン確認
node --version

# nvmでアップグレード
nvm install 20
nvm use 20

# 直接インストールする場合は https://nodejs.org/ からダウンロード
```

### npmパーミッションエラー

```
EACCES: permission denied
```

**原因**: グローバルインストール先への書き込み権限がありません。

**対処法**:

<details>
<summary>npmを使っている場合</summary>

```bash
# npmのグローバルディレクトリを変更
mkdir ~/.npm-global
npm config set prefix '~/.npm-global'
echo 'export PATH=~/.npm-global/bin:$PATH' >> ~/.zshrc  # macOS
source ~/.zshrc

# 再度インストール
npm install -g musubix
```

</details>

<details>
<summary>pnpmを使っている場合</summary>

pnpmはデフォルトでユーザーディレクトリにインストールするため、通常このエラーは発生しません。発生した場合：

```bash
# pnpmのグローバルディレクトリを確認
pnpm config get global-dir

# 権限を確認
ls -la $(pnpm config get global-dir)
```

</details>

### `musubix` コマンドが見つからない

```
command not found: musubix
```

**原因**: PATHにmusubixのインストール先が含まれていません。

**対処法（グローバルインストールの場合）**:

<details>
<summary>npmを使っている場合</summary>

```bash
# npmのグローバルbin先を確認
npm config get prefix

# PATHに追加（~/.zshrc または ~/.bashrc に追記）
export PATH="$(npm config get prefix)/bin:$PATH"
source ~/.zshrc
```

</details>

<details>
<summary>pnpmを使っている場合</summary>

```bash
# pnpmのセットアップを実行
pnpm setup

# ターミナルを再起動、または
source ~/.zshrc
```

</details>

**対処法（ローカルインストールの場合）**:

ローカルインストールの場合は `npx` または `pnpm exec` を付けて実行してください：

```bash
# npm
npx musubix --version

# pnpm
pnpm exec musubix --version
```

---

## プロジェクト初期化

### `musubix init` が既存ファイルと衝突する

```
Error: musubix.config.json already exists
```

**対処法**: `--force` オプションで上書きできます。

<details>
<summary>npmを使っている場合</summary>

```bash
npx musubix init . --force
```

</details>

<details>
<summary>pnpmを使っている場合</summary>

```bash
pnpm dlx musubix init . --force
```

</details>

> `AGENTS.md` や `CLAUDE.md` は既に存在する場合は上書きされません。

### 初期化後にスキルファイルが生成されない

**原因**: `npm install` / `pnpm install` のpostinstallスクリプトがスキップされた可能性があります。

**対処法**:

<details>
<summary>npmを使っている場合</summary>

```bash
# postinstallを明示的に実行
npm run postinstall

# または、foreground-scriptsで再インストール
npm install musubix --foreground-scripts
```

</details>

<details>
<summary>pnpmを使っている場合</summary>

```bash
# postinstallを明示的に実行
pnpm run postinstall

# または再インストール
pnpm add -D musubix
```

</details>

---

## ワークフロー

### 「コンテキストが不足しています」と言われた

**原因**: MUSUBIXが要件定義に必要な情報を収集しています。これはエラーではなく正常な動作です。

**対処法**: 表示された質問に回答してください。通常、以下の5種類の質問が表示されます：

| 質問タイプ | 内容 | 回答例 |
|-----------|------|-------|
| WHY | なぜこの機能が必要か | 「ユーザーの利便性向上のため」 |
| WHO | 対象ユーザーは | 「社内の事務スタッフ」 |
| WHAT-IF | 成功時の理想状態 | 「全備品の所在がリアルタイムで把握できる」 |
| CONSTRAINT | 制約条件 | 「既存のDBスキーマに影響を与えない」 |
| SUCCESS | 成功基準 | 「備品検索が2秒以内に完了する」 |

### orphan（孤児）警告が出る

```
⚠️ Found 1 issues (0 broken links, 1 orphans)
```

**原因**: 要件に対応する実装がまだないことを示しています。

**対処法**: 開発初期段階では正常な状態です。実装が進むにつれて自動的に解消されます。

### 設計から実装に進めない

```
⚠️ 実装への直接遷移は禁止！必ずタスク分解を経ること
```

**原因**: Phase 2（設計）から Phase 4（実装）への直接遷移が試みられました。

**対処法**: Phase 3（タスク分解）を先に実行してください：

```
タスク分解して
```

タスク分解が完了し「承認」した後に、実装に進めます。

### レビューが永遠に終わらない

**原因**: 修正が指摘内容と合致していない可能性があります。

**対処法**:
1. レビュー結果の指摘内容を確認する
2. AIエージェントに**具体的に**修正を依頼する
3. 修正後、再度レビュー結果を確認する

```
# 悪い例
修正して

# 良い例
REQ-001の応答時間を「200ms以内」に変更して
DES-002にRepository パターンを適用して
```

---

## MCPサーバー

### MCP接続エラー

```
Error: Failed to connect to MCP server
```

**対処法**:
1. サーバーが起動しているか確認

<details>
<summary>npmを使っている場合</summary>

```bash
# MCPサーバーの動作確認
npx @nahisaho/musubix-mcp-server --help

# プロセス確認
ps aux | grep musubix
```

</details>

<details>
<summary>pnpmを使っている場合</summary>

```bash
# MCPサーバーの動作確認
pnpm dlx @nahisaho/musubix-mcp-server --help

# プロセス確認
ps aux | grep musubix
```

</details>

2. ポートが使用中でないか確認

```bash
lsof -i :3000
```

3. MCP設定ファイルのパスが正しいか確認

---

## それでも解決しない場合

1. **デバッグモード**で詳細ログを確認：

<details>
<summary>npmを使っている場合</summary>

```bash
DEBUG=musubix* npx musubix <command>
```

</details>

<details>
<summary>pnpmを使っている場合</summary>

```bash
DEBUG=musubix* pnpm exec musubix <command>
```

</details>

2. **GitHubのIssue**で報告：
   https://github.com/nahisaho/MUSUBIX/issues

   以下の情報を含めてください：
   - Node.jsバージョン（`node --version`）
   - MUSUBIXバージョン（`musubix --version`）
   - OS（macOS / Linux / Windows）
   - エラーメッセージ全文
   - 再現手順

---

## 関連ドキュメント

| ドキュメント | 内容 |
|-------------|------|
| [クイックスタート](quickstart.md) | 5分で始めるMUSUBIX |
| [FAQ](faq.md) | よくある質問 |
| [プロンプトガイド](prompt-guide.md) | プロンプト例と内部処理の対応表 |
