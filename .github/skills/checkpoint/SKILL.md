---
name: checkpoint
description: |
  チェックポイント管理スキル。セーフポイントの作成・復元・
  比較を行う。Gitと統合して状態を追跡する。
  保持数管理と自動クリーンアップをサポート。
license: MIT
---

# Checkpoint Skill

## 目的

開発作業の安全なセーフポイントを提供し、以下を実現する：
- 作業状態のスナップショット作成
- 過去の状態への安全な復元
- チェックポイント間の比較・検証
- 保持数管理による自動クリーンアップ

## トレーサビリティ

- REQ-CP-001: Checkpoint Creation
- REQ-CP-002: Checkpoint Verification
- REQ-CP-003: Checkpoint Listing
- REQ-CP-004: Checkpoint Restore
- REQ-CP-005: Checkpoint Retention & Location

---

## 1. チェックポイントの作成

`/checkpoint create <name>` コマンドが実行されたら、以下を実行してください：

### 作成手順

1. **現在状態の検証**
   ```bash
   # Quick検証を実行
   /verify quick
   ```
   - 検証に失敗した場合は警告を表示
   - ユーザーの確認を得てから続行

2. **Git操作**
   ```bash
   # 未コミット変更がある場合
   git stash push -m "checkpoint: <name>"
   
   # または、コミットとして作成
   git add -A
   git commit -m "checkpoint: <name>"
   ```

3. **チェックポイントログへの記録**
   ```
   ~/.musubix/checkpoints/checkpoints.log
   ```
   **形式**: `YYYY-MM-DD-HH:MM | <checkpoint_name> | <git_short_sha>`

### 作成時の出力例

```
📍 Creating checkpoint: feature-auth-complete

  1. Running quick verification...
     ✅ Types: PASS
     ✅ Tests: PASS (42/42)
     
  2. Creating Git commit...
     [main abc1234] checkpoint: feature-auth-complete
     3 files changed, 150 insertions(+), 30 deletions(-)
     
  3. Recording checkpoint...
     ✅ Logged to ~/.musubix/checkpoints/checkpoints.log

📍 Checkpoint created successfully!
   Name: feature-auth-complete
   SHA: abc1234
   Time: 2026-01-25 14:30
```

### チェックポイントの命名規則

**推奨フォーマット**:
- `feature-<name>-<state>`: 機能開発のマイルストーン
- `fix-<issue>-<state>`: バグ修正のマイルストーン
- `refactor-<target>-<state>`: リファクタリングのマイルストーン
- `before-<action>`: 危険な操作の前
- `after-<action>`: 大きな変更の後

**例**:
- `feature-auth-initial`
- `feature-auth-login-complete`
- `fix-123-before-patch`
- `refactor-db-complete`
- `before-migration`

---

## 2. チェックポイントの検証

`/checkpoint verify <name>` コマンドが実行されたら、以下を比較・報告してください：

### 比較項目

| 項目 | 説明 | 計算方法 |
|------|------|---------|
| **変更ファイル数** | チェックポイント以降に変更されたファイル | `git diff --stat <sha>..HEAD` |
| **テスト合格率** | テストの合格/不合格の変化 | 現在の結果 vs チェックポイント時 |
| **カバレッジ** | テストカバレッジの変化 | 現在 vs チェックポイント時 |
| **ビルド状態** | ビルドの成功/失敗 | 現在のビルド結果 |

### 検証レポート例

```
📊 Checkpoint Verification: feature-auth-complete

Checkpoint Info:
  Name: feature-auth-complete
  SHA: abc1234
  Created: 2026-01-25 14:30

Changes Since Checkpoint:
  Files changed: 5
  Lines added: +230
  Lines removed: -45

Quality Comparison:
  | Metric      | Checkpoint | Current | Change |
  |-------------|------------|---------|--------|
  | Tests       | 42/42      | 45/45   | +3 new |
  | Coverage    | 85%        | 87%     | +2%    |
  | Build       | PASS       | PASS    | -      |
  | Type errors | 0          | 0       | -      |

Status: ✅ Quality maintained or improved
```

### 品質低下時の警告

```
⚠️ Quality Degradation Detected

  | Metric   | Checkpoint | Current | Change |
  |----------|------------|---------|--------|
  | Tests    | 42/42      | 40/42   | -2 ❌  |
  | Coverage | 85%        | 78%     | -7% ❌ |

Recommendation:
  - Review the failing tests
  - Consider restoring to checkpoint
```

---

## 3. チェックポイント一覧

`/checkpoint list` コマンドが実行されたら、全チェックポイントを表示してください：

### 表示形式

```
📋 Checkpoints (showing 5 of 8)

  # │ Name                      │ SHA     │ Created           │ Status
 ───┼───────────────────────────┼─────────┼───────────────────┼─────────
  1 │ feature-auth-complete     │ abc1234 │ 2026-01-25 14:30 │ current
  2 │ feature-auth-login        │ def5678 │ 2026-01-25 12:00 │ behind
  3 │ feature-auth-initial      │ ghi9012 │ 2026-01-25 10:00 │ behind
  4 │ before-refactor           │ jkl3456 │ 2026-01-24 16:00 │ behind
  5 │ fix-123-complete          │ mno7890 │ 2026-01-24 14:00 │ behind

Commands:
  /checkpoint verify <name>  - Compare with checkpoint
  /checkpoint restore <name> - Restore to checkpoint
  /checkpoint delete <name>  - Delete checkpoint
```

### ステータスの説明

| ステータス | 説明 |
|-----------|------|
| `current` | HEADがこのチェックポイントにある |
| `behind` | HEADがこのチェックポイントより先にある |
| `ahead` | HEADがこのチェックポイントより後ろにある（リセット後） |
| `diverged` | ブランチが分岐している |

---

## 4. チェックポイントの復元

`/checkpoint restore <name>` コマンドが実行されたら、安全に復元してください：

### 復元前の安全確認

```
⚠️ Checkpoint Restore Warning

You are about to restore to: feature-auth-login (def5678)

Current changes will be affected:
  - 3 files modified
  - 2 files added
  - 150 lines of uncommitted changes

Options:
  1. Stash changes and restore
  2. Commit changes and restore
  3. Cancel restore

Select (1/2/3): 
```

### 復元手順

1. **未コミット変更の確認**
   ```bash
   git status --porcelain
   ```
   - 変更がある場合はユーザーに選択を促す

2. **変更の保護**（選択に応じて）
   ```bash
   # Option 1: Stash
   git stash push -m "before-restore-to-<name>"
   
   # Option 2: Commit
   git add -A
   git commit -m "WIP: before restore to <name>"
   ```

3. **復元実行**
   ```bash
   git checkout <sha>
   # または
   git reset --hard <sha>
   ```

4. **復元後の検証**
   ```
   /verify quick
   ```

### 復元完了メッセージ

```
✅ Checkpoint Restored Successfully

  Restored to: feature-auth-login (def5678)
  
  Your previous changes were:
    [x] Stashed as "before-restore-to-feature-auth-login"
    
  To recover stashed changes:
    git stash pop

  Running quick verification...
    ✅ Types: PASS
    ✅ Tests: PASS
```

---

## 5. 保持数管理

チェックポイントの数を管理し、古いものを自動クリーンアップします：

### デフォルト設定

| 設定項目 | デフォルト値 |
|---------|-------------|
| 保持数上限 | 10件 |
| 保存場所 | `~/.musubix/checkpoints/checkpoints.log` |
| 自動クリーンアップ | 有効 |

### クリーンアップルール

1. **FIFO（先入れ先出し）**: 最も古いチェックポイントから削除
2. **ブランチ考慮**: 現在のブランチのチェックポイントを優先保持
3. **手動ピン**: `pinned: true` マークされたものは削除対象外

### クリーンアップ時の通知

```
🧹 Checkpoint Cleanup

  Checkpoints exceeded limit (10)
  
  Removing oldest checkpoints:
    - fix-old-issue (2026-01-20)
    - temp-checkpoint (2026-01-19)
    
  Keeping:
    - 10 most recent checkpoints
    - 1 pinned checkpoint (release-v3.6.0)
```

### チェックポイントのピン留め

```
/checkpoint pin <name>     - ピン留め（削除対象外に）
/checkpoint unpin <name>   - ピン解除
```

---

## 6. チェックポイントファイル形式

### checkpoints.log

```
# MUSUBIX Checkpoints Log
# Format: timestamp | name | sha | branch | pinned
2026-01-25-14:30 | feature-auth-complete | abc1234 | main | false
2026-01-25-12:00 | feature-auth-login | def5678 | main | false
2026-01-25-10:00 | feature-auth-initial | ghi9012 | main | false
2026-01-24-16:00 | before-refactor | jkl3456 | main | false
2026-01-24-14:00 | release-v3.6.0 | mno7890 | main | true
```

---

## 7. コマンド一覧

| コマンド | 説明 |
|---------|------|
| `/checkpoint create <name>` | 新しいチェックポイントを作成 |
| `/checkpoint verify <name>` | チェックポイントと現在の状態を比較 |
| `/checkpoint list` | チェックポイント一覧を表示 |
| `/checkpoint restore <name>` | チェックポイントに復元 |
| `/checkpoint delete <name>` | チェックポイントを削除 |
| `/checkpoint pin <name>` | チェックポイントをピン留め |
| `/checkpoint unpin <name>` | ピン留めを解除 |
| `/checkpoint clean` | 手動でクリーンアップ実行 |

---

## 8. MCP ツール統合

このスキルはMUSUBIX MCPサーバーの以下のツールと連携します：

- `workflow_get_status`: ワークフロー状態取得（フェーズ確認）
- `knowledge_put_entity`: チェックポイント情報の知識グラフへの保存
- `knowledge_query`: 過去のチェックポイント情報の検索

---

## 9. ベストプラクティス

### チェックポイント作成のタイミング

1. **機能実装完了時**: `feature-<name>-complete`
2. **危険な操作の前**: `before-<action>`
3. **大きな変更の後**: `after-<action>`
4. **リリース前**: `release-<version>`
5. **1日の作業開始時**: `daily-<date>-start`

### 復元の注意点

- 復元前に必ず現在の変更を保護（stash/commit）
- 復元後は必ず `/verify quick` で確認
- チーム開発時はローカルチェックポイントとリモートの状態に注意

### 命名のベストプラクティス

- 説明的な名前を使用（`checkpoint-1` ではなく `feature-auth-complete`）
- ハイフン区切りで読みやすく
- 日付よりも内容を優先（ログに日付は記録される）

---

**Version**: 1.0.0  
**Last Updated**: 2026-01-25  
**Maintainer**: MUSUBIX Team
