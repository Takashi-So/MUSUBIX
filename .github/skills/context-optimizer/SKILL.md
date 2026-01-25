---
name: context-optimizer
description: |
  コンテキストウィンドウ最適化スキル。ツール呼び出し回数を追跡し、
  戦略的なタイミングでコンテキスト圧縮を提案する。モードベースの
  コンテキスト注入もサポートする。PostToolUse/PreToolUse Hooks、
  Doc Blockerも含む。
license: MIT
version: 1.0.0
author: MUSUBIX Team
tags:
  - context
  - optimization
  - hooks
  - compaction
---

# Context Optimizer スキル

コンテキストウィンドウを最適化し、効率的なセッション管理を支援します。

## 概要

このスキルは以下の機能を提供します：

1. **Strategic Compact Suggestion** - ツール呼び出し回数に基づく圧縮提案
2. **Tool Call Counter** - ツール呼び出しの追跡とリマインダー
3. **Context Mode Injection** - dev/review/researchモードの注入
4. **PostToolUse Hooks** - ファイル編集後の自動チェック
5. **PreToolUse Hooks** - 危険なコマンド実行前の確認
6. **Doc Blocker** - 不要なドキュメント作成の抑制

---

## 1. Strategic Compact Suggestion (REQ-CO-001)

### 圧縮提案のタイミング

ツール呼び出し回数が**50回**に達した場合、以下の論理的なフェーズ遷移点で手動圧縮を提案してください：

| タイミング | 説明 |
|-----------|------|
| 計画フェーズ完了後 | 要件定義・設計が承認された後 |
| デバッグ完了後 | 問題が解決し、テストが合格した後 |
| マイルストーン達成後 | 主要機能の実装が完了した後 |

### 提案フォーマット

```markdown
💡 **コンテキスト圧縮の提案**

ツール呼び出しが**50回**に達しました。
現在のフェーズ: [フェーズ名]

コンテキストを圧縮する良いタイミングです。以下を確認してください：

1. 現在のタスクの状態を保存しましたか？
2. 次のステップは明確ですか？
3. 重要なコンテキストをNotes for Next Sessionに記録しましたか？

圧縮を実行する場合は、session-managerスキルで事前に状態を保存してください。
```

---

## 2. Tool Call Counter (REQ-CO-002)

### カウンターの動作

セッション中にツール呼び出し回数を追跡し、以下のタイミングで通知：

| 回数 | アクション |
|------|----------|
| 50回 | 圧縮提案を表示 |
| 75回 | リマインダー表示 |
| 100回 | 強い警告を表示 |
| 以降25回ごと | リマインダー表示 |

### リマインダーフォーマット

```markdown
⚠️ **ツール呼び出しリマインダー**

現在のツール呼び出し回数: **[N]回**

コンテキストウィンドウが限界に近づいている可能性があります。
圧縮を検討してください。
```

---

## 3. Context Mode Injection (REQ-CO-003)

### 利用可能なモード

| モード | フォーカス | 推奨ツール | 使用場面 |
|--------|----------|----------|----------|
| `dev` | 実装・コーディング | Edit, Write, Bash | 機能実装、バグ修正 |
| `review` | コードレビュー | Read, Grep, Glob | PR確認、品質チェック |
| `research` | 調査・探索 | Read, Grep, semantic_search | 技術調査、コード理解 |

### モード切り替え指示

ユーザーがモードを指定した場合、対応するコンテキストを注入してください：

#### dev モード
```markdown
**モード: dev（実装）**

- コード品質を重視
- テスト駆動開発（Red-Green-Blue）
- 型安全性の確保
- エラーハンドリングの実装
```

#### review モード
```markdown
**モード: review（レビュー）**

- コードの読みやすさを確認
- 潜在的なバグを検出
- セキュリティ問題を確認
- パフォーマンス問題を確認
- ベストプラクティスへの準拠
```

#### research モード
```markdown
**モード: research（調査）**

- 幅広い情報収集
- 関連コードの探索
- ドキュメントの確認
- 類似実装の調査
```

---

## 4. PostToolUse Hooks (REQ-CO-004)

### ファイル編集後のチェック

ファイル編集ツール（Edit, Write）を使用した後、以下のチェックを**提案**してください：

| ファイル種別 | チェック内容 | コマンド |
|-------------|-------------|---------|
| `.ts`, `.tsx` | 型チェック | `npx tsc --noEmit` |
| `.js`, `.ts`, `.tsx` | フォーマット | `npx prettier --check <file>` |
| `.ts`, `.tsx` | console.log検出 | `grep -n "console\\.log" <file>` |
| `*.test.ts` | テスト実行 | `npx vitest run <file>` |

### チェック提案フォーマット

```markdown
📝 **編集後チェック提案**

`[ファイル名]` を編集しました。以下のチェックを推奨します：

- [ ] 型チェック: `npx tsc --noEmit`
- [ ] フォーマット確認: `npx prettier --check [ファイル]`
- [ ] console.log残存確認

実行しますか？
```

### 自動検出と警告

TypeScript/JavaScriptファイルを編集した際、以下を自動検出して警告：

1. **console.log/console.debug残存**: 本番コードへの混入を防止
2. **debugger文残存**: デバッグコードの混入を防止
3. **TODO/FIXME追加**: 未完了項目の追跡

---

## 5. PreToolUse Hooks (REQ-CO-005)

### 長時間実行コマンドの確認

以下のコマンドをBashツールで実行しようとする場合、**tmuxまたはバックグラウンド実行**を提案：

| コマンドパターン | 提案内容 |
|-----------------|----------|
| `npm install`, `pnpm install`, `yarn install` | tmux使用を提案 |
| `npm run build`, `pnpm build` | バックグラウンド実行を提案 |
| `cargo build` | tmux使用を提案 |
| `docker build` | バックグラウンド実行を提案 |

### 提案フォーマット

```markdown
⏱️ **長時間コマンドの検出**

`[コマンド]` は実行に時間がかかる可能性があります。

以下の方法での実行を推奨します：
- tmux内で実行: `tmux new -s build && [コマンド]`
- バックグラウンド実行: `[コマンド] &`

続行しますか？
```

### 危険な操作の警告

以下のコマンドを実行しようとする場合、**実行前に警告**：

| コマンドパターン | 警告内容 |
|-----------------|----------|
| `git push` | 変更内容の最終確認を促す |
| `git push --force` | 強い警告を表示 |
| `rm -rf` | 削除対象の確認を促す |
| `git reset --hard` | 変更が失われることを警告 |
| `DROP TABLE`, `DELETE FROM` | データ削除の確認を促す |

### 警告フォーマット

```markdown
⚠️ **危険な操作の検出**

`[コマンド]` は以下のリスクがあります：
- [リスクの説明]

実行前に以下を確認してください：
1. [確認事項1]
2. [確認事項2]

本当に実行しますか？
```

---

## 6. Doc Blocker (REQ-CO-006)

### 不要なドキュメント作成の抑制

以下のファイルを作成しようとする場合、**本当に必要か確認**：

- `.md`ファイル（README以外）
- `.txt`ファイル
- `notes.`で始まるファイル
- `temp.`で始まるファイル

### 除外対象（ブロックしない）

以下のファイルは確認なしで作成可能：

- `README.md`
- `CHANGELOG.md`
- `LICENSE`
- `docs/`配下のファイル
- `.github/`配下のファイル
- `storage/specs/`配下のファイル（要件定義）
- `storage/design/`配下のファイル（設計書）
- `storage/tasks/`配下のファイル（タスク分解）

### 確認フォーマット

```markdown
📄 **ドキュメント作成の確認**

`[ファイル名]` を作成しようとしています。

このドキュメントは以下のいずれかに該当しますか？
- [ ] プロジェクトの公式ドキュメント
- [ ] 要件定義・設計・タスク分解
- [ ] 永続的に必要な情報

一時的なメモの場合は、session-managerの「Notes for Next Session」を使用してください。

作成を続行しますか？
```

---

## MCPツール統合

このスキルは以下のMUSUBIX MCPツールと連携します：

### workflow-engine連携
- `workflow_get_status`: 現在のワークフローフェーズを取得
- `workflow_validate_transition`: フェーズ遷移の検証

### session-manager連携
- 状態保存の呼び出し
- Pre-compact snapshotの作成

MCPツールが利用可能な場合は、それらを優先的に使用してください。

---

## 設定オプション

| オプション | デフォルト | 説明 |
|-----------|-----------|------|
| `compactThreshold` | 50 | 圧縮提案のツール呼び出し閾値 |
| `reminderInterval` | 25 | リマインダー表示間隔 |
| `defaultMode` | `dev` | デフォルトのコンテキストモード |
| `enableDocBlocker` | true | Doc Blockerの有効/無効 |
| `enablePostToolUseHooks` | true | PostToolUse Hooksの有効/無効 |
| `enablePreToolUseHooks` | true | PreToolUse Hooksの有効/無効 |

---

## トラブルシューティング

### 圧縮提案が多すぎる

`compactThreshold`を増やすか、大きなタスクを小さく分割してください。

### モードが適用されない

モード名が正しいか確認してください（`dev`, `review`, `research`のいずれか）。

### PostToolUse Hooksが動作しない

対象ファイルの拡張子を確認してください。

---

## 関連スキル

- **session-manager**: セッション状態の保存・復元
- **verification-loop**: 継続的な検証
- **build-fix**: ビルドエラーの解決

---

## バージョン履歴

| バージョン | 日付 | 変更内容 |
|-----------|------|----------|
| 1.0.0 | 2026-01-25 | 初版リリース |

---

## 参考資料

- [REQ-CO-001〜006](../../storage/specs/REQ-v3.7.0-everything-claude-code-integration.md)
- [DES-v3.7.0 Section 5](../../storage/design/DES-v3.7.0-everything-claude-code-integration.md)
- [Agent Skills Open Standard](https://github.com/agentskills/agentskills)
