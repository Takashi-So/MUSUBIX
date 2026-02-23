# MUSUBIX 開発ガイド

> このドキュメントはMUSUBIX自体を開発するコントリビューター向けです。

---

## 開発環境のセットアップ

### 前提条件

| 項目 | 要件 |
|------|------|
| Node.js | 20.0.0 以上 |
| npm | 10.0.0 以上 |
| TypeScript | 5.3 以上 |
| Git | 最新版 |

### リポジトリのクローンとビルド

```bash
git clone https://github.com/nahisaho/MUSUBIX.git
cd MUSUBIX

# 依存関係のインストール
npm install

# 全パッケージのビルド
npm run build

# リンク（開発用）
npm link
```

---

## 主要コマンド

### ビルド

```bash
# 全パッケージビルド
npm run build

# 特定パッケージのビルド
npm run build -w packages/core
npm run build -w packages/mcp-server
```

### テスト

```bash
# 全テスト実行
npm run test

# ユニットテストのみ
npm run test:unit

# 統合テストのみ
npm run test:integration

# カバレッジ計測
npm run test:coverage

# 特定パッケージのテスト
npm run test -w packages/core
npm run test -w packages/security
```

### コード品質

```bash
# ESLint
npm run lint

# ESLint 自動修正
npm run lint:fix

# TypeScript型チェック
npm run typecheck
```

### クリーンアップ

```bash
npm run clean
```

### パフォーマンス

```bash
# ベンチマーク
npx musubix perf benchmark

# 起動時間計測
npx musubix perf startup

# メモリ使用量
npx musubix perf memory

# キャッシュ統計
npx musubix perf cache-stats
```

---

## モノレポ構造

MUSUBIXはnpm workspacesを使用したモノレポです。

### パッケージ間の依存を追加する場合

```bash
# packages/mcp-server に packages/core への依存を追加
npm install @nahisaho/musubix-core -w packages/mcp-server
```

### 新しいパッケージを追加する場合

1. `packages/` 以下にディレクトリを作成
2. `package.json` を作成（`name`, `version`, `main`, `types` を設定）
3. `tsconfig.json` でプロジェクト参照を設定
4. ルートの `package.json` の `workspaces` に追加

---

## テスト規約

- テストフレームワーク: **Vitest**
- テストファイル: `*.test.ts` または `*.spec.ts`
- テストディレクトリ: ソースファイルと同じディレクトリ、または `__tests__/`
- カウンターリセット: `beforeEach` でIDカウンターをリセット（BP-TEST-001）
- Result型テスト: `isOk()` / `isErr()` で両パスをテスト（BP-TEST-004）

---

## コーディング規約

### 9つの憲法条項（開発時も適用）

MUSUBIXの開発自体も9つの憲法条項に従います。特に重要なもの：

- **Article I (Library-First)**: 新機能は独立パッケージとして作成
- **Article III (Test-First)**: テストを先に書く
- **Article V (Traceability)**: 変更の理由をコミットメッセージに明記

### コードスタイル

- **Value Object**: クラスではなく `interface` + factory関数（BP-CODE-004）
- **エラーハンドリング**: `Result<T, E>` パターン（BP-CODE-005）
- **ステータス遷移**: `Record<Status, Status[]>` マップ（BP-DESIGN-001）
- **Repository**: async化（将来のDB移行に備え）（BP-DESIGN-002）
- **Service**: リポジトリをDI（BP-DESIGN-003）

---

## コミット規約

Conventional Commits形式を使用：

```
feat(core): EARS検証にカスタムルールを追加
fix(mcp-server): ツール一覧のフィルタリングバグを修正
docs(user): クイックスタートガイドを更新
test(security): テイント解析のエッジケースを追加
refactor(knowledge): グラフ走査のパフォーマンス改善
```

---

## 関連ドキュメント

| ドキュメント | 内容 |
|-------------|------|
| [アーキテクチャ](architecture.md) | 25パッケージの構成と依存関係 |
| [APIリファレンス](api-reference.md) | パブリックAPI一覧 |
