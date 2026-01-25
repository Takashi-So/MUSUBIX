---
name: verification-loop
description: |
  6フェーズ検証ループスキル。Build→Type→Lint→Test→Security→Diffの
  総合的な検証を実行し、PRレディネスを判定する。
  quick/fullモードと Stop Hook監査をサポート。
license: MIT
---

# Verification Loop Skill

## 目的

コード変更の品質を総合的に検証し、以下を実現する：
- 6フェーズの段階的な検証によるPRレディネス判定
- quick/fullモードによる柔軟な検証粒度の選択
- 継続的検証による長時間セッションの品質維持
- Stop Hook監査によるセッション終了時のクリーンアップ確認

## トレーサビリティ

- REQ-VL-001: Multi-Phase Verification
- REQ-VL-002: Verification Report
- REQ-VL-003: Continuous Verification
- REQ-VL-004: Verification Modes (quick/full)
- REQ-VL-005: Stop Hook監査

---

## 1. 6フェーズ検証

`/verify` コマンドが実行されたら、以下のフェーズを順次実行してください：

### Phase 1: Build（ビルド検証）

```bash
npm run build
# または
pnpm build
```

**判定基準**:
- 終了コード 0 = PASS
- 終了コード non-0 = FAIL

**失敗時アクション**: 
- 即座に停止
- ビルドエラーの修正を最優先で実施

### Phase 2: Type Check（型チェック）

```bash
npx tsc --noEmit
# または
npx tsc --noEmit --project tsconfig.json
```

**判定基準**:
- エラー 0件 = PASS
- エラー 1件以上 = FAIL

**失敗時アクション**:
- 重大な型エラー（TS2322, TS2339等）は修正
- 警告レベルのエラーは報告のみ

### Phase 3: Lint（静的解析）

```bash
npm run lint
# または
npx eslint . --ext .ts,.tsx,.js,.jsx
```

**判定基準**:
- エラー 0件 = PASS
- 警告のみ = PASS (with warnings)
- エラー 1件以上 = FAIL

**失敗時アクション**:
- 自動修正可能なものは `--fix` で修正
- 手動修正が必要なものは報告

### Phase 4: Tests（テスト実行）

```bash
npm run test
# または
npx vitest run --reporter=verbose
```

**判定基準**:
- 全テスト合格 = PASS
- 1件以上失敗 = FAIL

**報告内容**:
- 合格/不合格のテスト数
- カバレッジ率（可能な場合）
- 失敗したテストの詳細

### Phase 5: Security（セキュリティスキャン）

```bash
npm audit
# または
npx snyk test
```

**判定基準**:
- critical/high 脆弱性 0件 = PASS
- critical/high 脆弱性 1件以上 = FAIL

**失敗時アクション**:
- 脆弱性の詳細を報告
- 修正方法を提案（npm audit fix --force の提案等）

### Phase 6: Diff Review（変更差分確認）

```bash
git diff --stat
git diff HEAD~1..HEAD
```

**報告内容**:
- 変更ファイル数
- 追加/削除行数
- 主要な変更箇所のサマリー

---

## 2. 検証レポート形式

検証が完了したら、以下の形式でレポートを生成してください：

```
╔════════════════════════════════════════════════════════════╗
║                   VERIFICATION REPORT                       ║
╠════════════════════════════════════════════════════════════╣
║                                                             ║
║  Build:     [PASS] ✅                                       ║
║  Types:     [PASS] ✅ (0 errors)                           ║
║  Lint:      [PASS] ⚠️  (3 warnings)                        ║
║  Tests:     [PASS] ✅ (42/42 passed, 85% coverage)         ║
║  Security:  [PASS] ✅ (0 critical, 0 high)                 ║
║  Diff:      [INFO] 📝 (5 files changed, +120 -45)          ║
║                                                             ║
╠════════════════════════════════════════════════════════════╣
║  Overall:   [READY] ✅  for PR                             ║
╚════════════════════════════════════════════════════════════╝
```

### 失敗時のレポート例

```
╔════════════════════════════════════════════════════════════╗
║                   VERIFICATION REPORT                       ║
╠════════════════════════════════════════════════════════════╣
║                                                             ║
║  Build:     [PASS] ✅                                       ║
║  Types:     [FAIL] ❌ (2 errors)                           ║
║  Lint:      [SKIP] ⏭️  (blocked by type errors)            ║
║  Tests:     [SKIP] ⏭️  (blocked by type errors)            ║
║  Security:  [SKIP] ⏭️  (blocked by type errors)            ║
║  Diff:      [INFO] 📝 (3 files changed)                    ║
║                                                             ║
╠════════════════════════════════════════════════════════════╣
║  Overall:   [NOT READY] ❌  for PR                         ║
╠════════════════════════════════════════════════════════════╣
║  Issues to Fix:                                            ║
║  1. src/user.ts:45 - TS2339: Property 'name' does not...  ║
║  2. src/user.ts:67 - TS2322: Type 'string' is not...      ║
╚════════════════════════════════════════════════════════════╝
```

---

## 3. 検証モード

### Quick Mode (`/verify quick`)

実行時間を優先した最小限の検証：

| フェーズ | 実行 | 説明 |
|---------|------|------|
| Build | ⏭️ SKIP | スキップ |
| Type Check | ✅ RUN | 型チェックのみ |
| Lint | ⏭️ SKIP | スキップ |
| Tests | ✅ RUN | 変更に関連するテストのみ |
| Security | ⏭️ SKIP | スキップ |
| Diff | ✅ RUN | 変更サマリー |

**所要時間目安**: 10-30秒

**使用シーン**:
- 開発中の頻繁な検証
- 小さな変更の確認
- デバッグ中の動作確認

### Full Mode (`/verify` or `/verify full`)

全フェーズを実行する完全な検証：

| フェーズ | 実行 | 説明 |
|---------|------|------|
| Build | ✅ RUN | フルビルド |
| Type Check | ✅ RUN | 全ファイルの型チェック |
| Lint | ✅ RUN | ESLint完全実行 |
| Tests | ✅ RUN | 全テスト + カバレッジ |
| Security | ✅ RUN | npm audit + snyk |
| Diff | ✅ RUN | 詳細な差分レビュー |

**所要時間目安**: 30-120秒

**使用シーン**:
- PR作成前の最終確認
- マージ前の品質保証
- リリース前の検証

---

## 4. 継続的検証

長時間セッションでは、以下のタイミングで自動検証を提案してください：

### 提案タイミング

1. **時間ベース**: 15分ごと
2. **変更ベース**: 大きな変更後（5ファイル以上の変更）
3. **マイルストーン**: 機能実装完了時

### 提案メッセージ例

```
💡 検証の提案

15分間の作業で以下の変更がありました：
- 3ファイルを編集
- 150行を追加
- 2つの関数を新規作成

品質を確認するために `/verify quick` を実行することを推奨します。
```

### 自動検証のスキップ条件

- ユーザーが明示的に無効化した場合
- 直前に検証を実行した場合（5分以内）
- 変更が軽微な場合（コメントのみ等）

---

## 5. Stop Hook 監査

セッション終了時に、以下の監査を実行してください：

### 5.1 console.log 残存チェック

```bash
grep -rn "console\.log" --include="*.ts" --include="*.tsx" --include="*.js" --include="*.jsx" src/
```

**検出時のアクション**:
```
⚠️ console.log が残っています:

  src/user.ts:45:   console.log('debug:', user);
  src/api.ts:23:    console.log(response);

本番コードには console.log を残さないでください。
削除しますか？ (y/n)
```

### 5.2 debugger 残存チェック

```bash
grep -rn "debugger" --include="*.ts" --include="*.tsx" --include="*.js" --include="*.jsx" src/
```

**検出時のアクション**:
```
⚠️ debugger ステートメントが残っています:

  src/handler.ts:89:   debugger;

本番コードには debugger を残さないでください。
削除しますか？ (y/n)
```

### 5.3 TODO/FIXME チェック

```bash
grep -rn "TODO\|FIXME" --include="*.ts" --include="*.tsx" --include="*.js" --include="*.jsx" src/
```

**検出時のアクション**:
```
📝 未完了の TODO/FIXME があります:

  src/user.ts:12:    // TODO: バリデーション追加
  src/api.ts:56:     // FIXME: エラーハンドリング改善
  src/db.ts:89:      // TODO: インデックス最適化

これらは次回のセッションで対応が必要です。
Notes for Next Session に記録しますか？ (y/n)
```

### 5.4 未コミット変更チェック

```bash
git status --porcelain
```

**検出時のアクション**:
```
📦 未コミットの変更があります:

  M  src/user.ts
  M  src/api.ts
  A  src/new-feature.ts

コミットしますか？
  1. コミットする
  2. スタッシュする
  3. このまま終了する

選択: 
```

---

## 6. 検証コマンド一覧

| コマンド | 説明 |
|---------|------|
| `/verify` | フル検証を実行 |
| `/verify quick` | クイック検証を実行 |
| `/verify full` | フル検証を実行（明示的） |
| `/verify build` | ビルドのみ検証 |
| `/verify types` | 型チェックのみ実行 |
| `/verify lint` | リントのみ実行 |
| `/verify tests` | テストのみ実行 |
| `/verify security` | セキュリティスキャンのみ |
| `/verify audit` | Stop Hook監査を手動実行 |

---

## 7. MCP ツール統合

このスキルはMUSUBIX MCPサーバーの以下のツールと連携します：

- `workflow_get_status`: ワークフロー状態取得（現在のフェーズ確認）
- `workflow_validate_transition`: フェーズ遷移の検証
- `sdd_validate_traceability`: トレーサビリティ検証

MCPツールが利用可能な場合は、それらを優先的に使用してください。

---

## 8. ベストプラクティス

### 検証の習慣化

- PR作成前には必ず `/verify full` を実行
- 大きな変更後は `/verify quick` で確認
- セッション終了前に Stop Hook監査を実行

### エラー対応の優先順位

1. **Build エラー**: 最優先で修正（他の検証をブロック）
2. **Type エラー**: 高優先度（ランタイムエラーの原因）
3. **Test 失敗**: 高優先度（機能の破損）
4. **Lint エラー**: 中優先度（コード品質）
5. **Security 脆弱性**: 中〜高優先度（重大度による）

### 検証結果の活用

- 検証レポートはPRの説明に含める
- 繰り返し発生するエラーはパターンとして学習
- カバレッジ低下時はテスト追加を検討

---

**Version**: 1.0.0  
**Last Updated**: 2026-01-25  
**Maintainer**: MUSUBIX Team
