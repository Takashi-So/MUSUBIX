# GitHub Actions npm Publish Setup Guide

このドキュメントでは、GitHub Actionsを使用してMUSUBIXパッケージをnpmに自動公開する設定方法を説明します。

## 1. NPM_TOKEN シークレットの設定

### 1.1 npmアクセストークンの作成

1. [npmjs.com](https://www.npmjs.com) にログイン
2. 右上のアバター → **Access Tokens** をクリック
3. **Generate New Token** → **Classic Token** を選択
4. トークン名を入力（例: `MUSUBIX_GITHUB_ACTIONS`）
5. タイプは **Automation** を選択（CIでの使用に最適）
6. **Generate Token** をクリック
7. 表示されたトークンをコピー（このトークンは一度しか表示されません）

### 1.2 GitHubシークレットへの登録

1. GitHub リポジトリ（https://github.com/nahisaho/MUSUBIX）を開く
2. **Settings** タブをクリック
3. 左メニューの **Secrets and variables** → **Actions** を選択
4. **New repository secret** をクリック
5. 以下を入力:
   - **Name**: `NPM_TOKEN`
   - **Secret**: （コピーしたnpmトークン）
6. **Add secret** をクリック

## 2. ワークフローの説明

### 2.1 CI ワークフロー (`.github/workflows/ci.yml`)

プルリクエストとmainブランチへのプッシュ時に自動実行:

- ✅ Node.js 20, 22 でのビルドテスト
- ✅ TypeScriptコンパイル
- ✅ Lintチェック
- ✅ ユニットテスト
- ✅ CLI動作確認
- ✅ モジュールインポート確認

### 2.2 Publish ワークフロー (`.github/workflows/publish.yml`)

以下のタイミングで実行:

1. **リリース作成時**: GitHubでリリースを作成すると自動的にnpmへ公開
2. **手動実行**: Actions タブから手動でトリガー可能（ドライランオプション付き）

## 3. 使用方法

### 3.1 リリース作成による自動公開

```bash
# 1. バージョンを更新
npm version patch  # または minor, major

# 2. 変更をプッシュ
git push origin main --tags

# 3. GitHubでリリースを作成
#    - https://github.com/nahisaho/MUSUBIX/releases/new
#    - タグを選択（例: v1.0.1）
#    - リリースノートを記入
#    - "Publish release" をクリック
```

リリースが公開されると、GitHub Actionsが自動的にnpmへパッケージを公開します。

### 3.2 手動実行

1. https://github.com/nahisaho/MUSUBIX/actions を開く
2. 左メニューから **Publish to npm** を選択
3. **Run workflow** をクリック
4. オプション:
   - **Dry run**: `true` にすると実際の公開をスキップ（テスト用）
5. **Run workflow** をクリック

## 4. トラブルシューティング

### 4.1 認証エラー

```
npm ERR! code E401
npm ERR! 401 Unauthorized
```

**解決策**:
- NPM_TOKEN シークレットが正しく設定されているか確認
- トークンの有効期限が切れていないか確認
- トークンのタイプが "Automation" または "Publish" であるか確認

### 4.2 パッケージ名の競合

```
npm ERR! code E403
npm ERR! 403 Forbidden - Package name too similar to existing packages
```

**解決策**:
- パッケージ名がnpmで利用可能か確認
- スコープ付きパッケージ名（@musubix/xxx）を使用

### 4.3 バージョンの重複

```
npm ERR! code E403
npm ERR! 403 Forbidden - You cannot publish over the previously published version
```

**解決策**:
- `package.json` のバージョンを更新
- `npm version patch/minor/major` でバージョンを上げる

## 5. セキュリティのベストプラクティス

1. **トークンの管理**:
   - トークンは定期的にローテーション
   - Automationタイプを使用（2FA不要）
   - 最小権限の原則に従う

2. **Provenance（来歴）**:
   - `--provenance` フラグでnpmパッケージの来歴を証明
   - GitHubとnpmアカウントの紐付けを確認可能

3. **ブランチ保護**:
   - mainブランチへの直接プッシュを制限
   - プルリクエストでのレビューを必須化

## 6. 関連リンク

- [npm Access Tokens Documentation](https://docs.npmjs.com/about-access-tokens)
- [GitHub Actions Secrets](https://docs.github.com/en/actions/security-guides/encrypted-secrets)
- [npm Provenance](https://docs.npmjs.com/generating-provenance-statements)
