---
name: refactor-cleaner
description: |
  リファクタリング・クリーナースキル。デッドコード検出・安全な削除を実行する。
  knip, depcheck, ts-pruneと連携してコードベースをクリーンに保つ。
  削除操作は常にログに記録し、復元可能な状態を維持する。
version: 1.0.0
license: MIT
author: MUSUBIX Team
tags:
  - refactoring
  - dead-code
  - cleanup
  - maintenance
triggers:
  - /refactor
  - /cleanup
  - /deadcode
  - dead code detection
  - unused exports
---

# Refactor Cleaner Skill

デッドコードを検出し、安全に削除するためのスキルです。

## 概要

このスキルは以下の機能を提供します：

1. **デッドコード検出** - knip, depcheck, ts-pruneを使用した未使用コード検出
2. **安全な削除** - 動的参照チェック後の安全な削除
3. **削除ログ** - すべての削除操作の記録と復元情報
4. **リスク分類** - SAFE/CAUTION/DANGERの3段階分類

## コマンド

### `/refactor analyze`

デッドコードを分析し、レポートを生成します。

```
/refactor analyze [--path <dir>] [--include-deps]
```

**オプション**:
- `--path`: 分析対象ディレクトリ（デフォルト: `.`）
- `--include-deps`: npm依存関係も分析

### `/refactor clean`

検出されたデッドコードを安全に削除します。

```
/refactor clean [--safe-only] [--dry-run]
```

**オプション**:
- `--safe-only`: SAFEレベルのみ削除
- `--dry-run`: 削除せずにプレビューのみ

### `/refactor report`

デッドコード分析レポートを表示します。

```
/refactor report [--format <md|json>]
```

## 実行手順

### REQ-RC-001: デッドコード検出

以下のツールを使用してデッドコードを検出してください：

#### 1. knip - 未使用ファイル・エクスポート・依存関係

```bash
# knipがインストールされていない場合
npm install -D knip

# 分析実行
npx knip

# JSON形式で出力
npx knip --reporter json > .reports/knip-report.json
```

**knip検出項目**:
- 未使用ファイル
- 未使用エクスポート
- 未使用依存関係（dependencies, devDependencies）
- 未使用タイプ

#### 2. depcheck - 未使用npm依存関係

```bash
# depcheckがインストールされていない場合
npm install -g depcheck

# 分析実行
depcheck

# JSON形式で出力
depcheck --json > .reports/depcheck-report.json
```

**depcheck検出項目**:
- 未使用dependencies
- 未使用devDependencies
- package.jsonに未記載だがインポートされているパッケージ

#### 3. ts-prune - 未使用TypeScriptエクスポート

```bash
# ts-pruneがインストールされていない場合
npm install -D ts-prune

# 分析実行
npx ts-prune

# 結果をファイルに保存
npx ts-prune > .reports/ts-prune-report.txt
```

### REQ-RC-002: 安全な削除

コード削除前に、以下の検証を必ず実行してください：

#### 1. 動的インポートチェック

```bash
# 動的インポートパターンを検索
grep -rn "import(" src/
grep -rn "require(" src/
grep -rn "await import" src/

# 検出されたファイルは削除対象から除外
```

#### 2. テストでの参照チェック

```bash
# テストファイルでの参照を確認
grep -rn "削除対象の関数/クラス名" tests/ __tests__ *.test.ts *.spec.ts
```

#### 3. ドキュメントでの参照チェック

```bash
# ドキュメントでの参照を確認
grep -rn "削除対象" docs/ README.md *.md
```

#### 4. 設定ファイルでの参照チェック

```bash
# 設定ファイルでの参照を確認
grep -rn "削除対象" *.config.* .github/ .vscode/
```

### REQ-RC-003: 削除ログ

すべての削除操作を `docs/DELETION_LOG.md` に記録してください：

```markdown
# Deletion Log

## [YYYY-MM-DD] Cleanup Session

### Summary
- **Files deleted**: X
- **Exports removed**: Y
- **Dependencies removed**: Z
- **Estimated reduction**: ~XX KB

### Deleted Items

#### Files

| File | Reason | Git SHA |
|------|--------|---------|
| `src/old-feature.ts` | Unused for 6+ months | abc1234 |
| `src/utils/deprecated.ts` | Replaced by new implementation | def5678 |

#### Exports

| File | Export | Reason |
|------|--------|--------|
| `src/index.ts` | `oldFunction` | No external usage |

#### Dependencies

| Package | Version | Reason |
|---------|---------|--------|
| `lodash` | ^4.17.21 | Replaced with native methods |

### Restoration

To restore deleted code:

\```bash
# Restore specific file
git checkout abc1234 -- src/old-feature.ts

# Restore all deleted files from this session
git checkout abc1234~1 -- <file1> <file2> ...
\```
```

### REQ-RC-004: リスク分類とレポート

検出されたデッドコードを以下の3段階で分類してください：

#### SAFE (自動削除可能)

以下の条件をすべて満たす場合：
- 静的解析で参照がゼロ
- 動的インポートパターンなし
- テスト/ドキュメントでの参照なし
- 内部ユーティリティ（公開APIではない）

```markdown
🟢 SAFE: 削除しても影響が限定的
- `src/internal/old-helper.ts` - 未使用ヘルパー関数
- `src/utils/deprecated-formatter.ts` - 新実装で置換済み
```

#### CAUTION (確認が必要)

以下のいずれかに該当する場合：
- 動的インポートの可能性あり
- テストでは参照されている
- 最近（3ヶ月以内）に変更された

```markdown
🟡 CAUTION: 追加確認が必要
- `src/plugins/optional-feature.ts` - 動的ロードの可能性
- `src/experimental/beta-api.ts` - 一部テストで使用中
```

#### DANGER (自動削除禁止)

以下のいずれかに該当する場合：
- 公開API（エクスポートされている）
- エントリーポイント
- 設定ファイルで参照
- ドキュメントで説明されている

```markdown
🔴 DANGER: 自動削除禁止（手動レビュー必須）
- `src/index.ts` の `publicApi` - 外部パッケージが依存
- `bin/cli.js` - エントリーポイント
```

#### レポート出力

`.reports/dead-code-analysis.md` に以下の形式でレポートを出力：

```markdown
# Dead Code Analysis Report

**Generated**: [timestamp]
**Analyzed paths**: [paths]

## Summary

| Category | Count | Estimated Size |
|----------|-------|----------------|
| 🟢 SAFE | X | ~YY KB |
| 🟡 CAUTION | X | ~YY KB |
| 🔴 DANGER | X | ~YY KB |

## Details

### 🟢 SAFE (Auto-deletable)

[SAFEアイテムのリスト]

### 🟡 CAUTION (Review Required)

[CAUTIONアイテムのリスト]

### 🔴 DANGER (Manual Review Only)

[DANGERアイテムのリスト]

## Recommendations

1. [推奨アクション1]
2. [推奨アクション2]
```

## MCPツール統合

このスキルはMUSUBIX MCPサーバーの以下のツールと連携します：

- `codegraph_analyze`: コード構造解析
- `codegraph_dependencies`: 依存関係追跡
- `security_scan`: セキュリティ関連の未使用コード検出

## 安全ガードレール

### 削除禁止リスト

以下のパターンは自動削除から除外されます：

```yaml
# .refactor-ignore
patterns:
  - "**/index.ts"           # エントリーポイント
  - "**/bin/**"             # CLI実行ファイル
  - "**/*.d.ts"             # 型定義ファイル
  - "**/migrations/**"      # DBマイグレーション
  - "**/__mocks__/**"       # テストモック
  - "**/fixtures/**"        # テストフィクスチャ
```

### 確認プロンプト

CAUTION/DANGERレベルの削除時は必ずユーザーに確認：

```
⚠️ 以下のファイルを削除しますか？

🟡 CAUTION:
  - src/plugins/optional.ts (動的インポートの可能性)

🔴 DANGER:
  - src/api/public.ts (公開API)

[y] Yes, delete all
[s] Safe only (SAFE items)
[r] Review each
[n] Cancel
```

## ベストプラクティス

1. **定期実行**: 月1回の定期クリーンアップを推奨
2. **PR単位**: 大きな削除は専用PRで実施
3. **段階的削除**: まずSAFEのみ、次にCAUTION
4. **テスト実行**: 削除後は必ずテストスイートを実行
5. **削除ログ更新**: すべての削除を記録

## 関連スキル

- `codemap`: コード構造の可視化
- `verification-loop`: 削除後の検証
- `checkpoint`: 削除前のチェックポイント作成

---

**Traceability**: REQ-RC-001, REQ-RC-002, REQ-RC-003, REQ-RC-004
