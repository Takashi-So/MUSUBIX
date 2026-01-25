---
name: build-fix
description: |
  ビルドエラー解決スキル。ビルドエラーを分析し、段階的に修正する。
  TypeScript、ESLint、Webpack/Vite等のエラーに対応。
  反復的な修正戦略と詳細なレポート生成をサポート。
license: MIT
---

# Build Fix Skill

## 目的

ビルドエラーを効率的に解決し、以下を実現する：
- エラーの自動分類と優先度付け
- 反復的な修正戦略による段階的解決
- 修正結果の詳細なレポート生成
- 一般的なエラーパターンの学習と提案

## トレーサビリティ

- REQ-BF-001: Build Error Analysis
- REQ-BF-002: Iterative Fix Strategy
- REQ-BF-003: Fix Report

---

## 1. ビルドエラーの分析

ビルドエラーが発生したら、以下のカテゴリに分類してください：

### エラーカテゴリ

| カテゴリ | 例 | 優先度 | 影響範囲 |
|---------|-----|--------|---------|
| **Type Error** | TS2322, TS2339, TS2345 | 🔴 高 | 広い（型不整合は連鎖的） |
| **Import Error** | Module not found, Cannot resolve | 🔴 高 | 広い（依存関係の破損） |
| **Syntax Error** | Unexpected token, Missing semicolon | 🔴 高 | 局所的（構文エラー） |
| **Lint Error** | ESLint warnings/errors | 🟡 中 | 局所的（コードスタイル） |
| **Config Error** | tsconfig, webpack config | 🟡 中 | プロジェクト全体 |
| **Dependency Error** | Version mismatch, Peer dependency | 🟢 低 | 依存関係の範囲 |

### 分析出力例

```
🔍 Build Error Analysis

Total Errors: 8

By Category:
  🔴 Type Error:    4 (High Priority)
  🔴 Import Error:  2 (High Priority)
  🟡 Lint Error:    2 (Medium Priority)

By File:
  src/user.ts:       3 errors
  src/api.ts:        2 errors
  src/utils.ts:      2 errors
  src/index.ts:      1 error

Root Cause Analysis:
  1. Type 'User' is missing property 'email' (src/user.ts:45)
     → This causes 2 downstream type errors
  2. Module '@/utils' not found (src/api.ts:1)
     → Path alias may be misconfigured

Recommended Fix Order:
  1. src/user.ts:45 (Type Error) - Root cause
  2. src/api.ts:1 (Import Error) - Root cause
  3. Remaining errors may resolve automatically
```

### TypeScriptエラーコード参照

| コード | 説明 | 一般的な原因 |
|--------|------|-------------|
| TS2322 | Type is not assignable | 型の不一致 |
| TS2339 | Property does not exist | 未定義プロパティへのアクセス |
| TS2345 | Argument type mismatch | 関数引数の型不一致 |
| TS2304 | Cannot find name | 未インポートまたは未定義 |
| TS2307 | Cannot find module | モジュールが見つからない |
| TS2531 | Object is possibly null | null チェック不足 |
| TS2554 | Expected X arguments | 引数の数が不一致 |
| TS7006 | Parameter has implicit any | 型注釈の不足 |

---

## 2. 反復的な修正戦略

ビルドエラーの修正は、以下のループで実行してください：

### 修正ループ

```
┌─────────────────────────────────────────────────────┐
│                                                      │
│   1. エラーリストを取得                              │
│      npm run build 2>&1 | head -100                 │
│                              │                       │
│                              ▼                       │
│   2. 最も影響範囲の大きいエラーを特定               │
│      - Root cause を優先                            │
│      - 高優先度カテゴリを優先                       │
│                              │                       │
│                              ▼                       │
│   3. 修正を適用                                     │
│      - 1つのエラーに集中                            │
│      - 関連する変更も含める                         │
│                              │                       │
│                              ▼                       │
│   4. ビルドを再実行                                 │
│      npm run build                                  │
│                              │                       │
│                              ▼                       │
│   5. 結果を確認                                     │
│      - エラーが減少したか？                         │
│      - 新しいエラーが発生したか？                   │
│                              │                       │
│                              ▼                       │
│   6. エラーがあれば 1 に戻る                        │
│      ※ 最大10回まで                                 │
│                                                      │
└─────────────────────────────────────────────────────┘
```

### 修正戦略の優先順位

1. **Root Cause First**: 連鎖的なエラーの根本原因を最初に修正
2. **Import/Module First**: インポートエラーはコンパイル自体を妨げる
3. **Type Errors**: 型エラーは多くの下流エラーを引き起こす
4. **Syntax Errors**: 構文エラーは局所的だが致命的
5. **Lint Errors**: 最後に対応（品質向上）

### 反復中の進捗報告

```
🔧 Build Fix Progress

Iteration 1/10:
  Target: src/user.ts:45 - TS2339
  Action: Added 'email' property to User interface
  Result: 4 errors → 2 errors (2 resolved)

Iteration 2/10:
  Target: src/api.ts:1 - Module not found
  Action: Fixed path alias in tsconfig.json
  Result: 2 errors → 0 errors (2 resolved)

✅ Build successful after 2 iterations!
```

### 最大反復回数超過時

```
⚠️ Build Fix Limit Reached

  After 10 iterations:
    - Initial errors: 15
    - Remaining errors: 3
    - Resolved: 12

  Remaining Errors:
    1. src/complex.ts:123 - TS2322
       → This may require manual investigation
    2. src/legacy.ts:45 - TS2339
       → Consider refactoring this module
    3. src/external.ts:10 - TS2307
       → External dependency issue

  Recommendation:
    - Review remaining errors manually
    - Consider creating an issue for tracking
    - Some errors may be false positives
```

---

## 3. Fix Report（修正レポート）

ビルドエラーの修正が完了したら、以下の形式でレポートを生成してください：

### レポート形式

```markdown
# Build Fix Report

**Date**: 2026-01-25 14:30
**Duration**: 5 minutes
**Iterations**: 3

## Summary

| Metric | Value |
|--------|-------|
| Initial Errors | 8 |
| Final Errors | 0 |
| Errors Fixed | 8 |
| Files Modified | 4 |
| Lines Changed | +25 / -10 |

## Fixes Applied

### 1. src/user.ts - Type Error (TS2339)

**Problem**: Property 'email' does not exist on type 'User'

**Solution**: Added 'email' property to User interface

```diff
 interface User {
   id: string;
   name: string;
+  email: string;
 }
```

**Impact**: Resolved 3 downstream errors

---

### 2. src/api.ts - Import Error

**Problem**: Cannot find module '@/utils'

**Solution**: Updated tsconfig.json path alias

```diff
 "paths": {
-  "@/*": ["./src/*"]
+  "@/*": ["src/*"]
 }
```

**Impact**: Resolved 2 import errors

---

## Warnings

The following warnings remain (non-blocking):

- ESLint: 'console.log' is not allowed (src/debug.ts:15)
- ESLint: Prefer 'const' over 'let' (src/utils.ts:30)

## Recommendations

1. Consider adding stricter type checking in tsconfig.json
2. Set up pre-commit hooks to catch errors early
3. Review the 2 ESLint warnings when convenient
```

### 簡易レポート（コンソール出力）

```
╔════════════════════════════════════════════════════════════╗
║                    BUILD FIX REPORT                         ║
╠════════════════════════════════════════════════════════════╣
║                                                             ║
║  Status:      ✅ BUILD SUCCESSFUL                          ║
║  Duration:    5 minutes                                     ║
║  Iterations:  3                                             ║
║                                                             ║
║  Errors:      8 → 0 (all fixed)                            ║
║  Files:       4 modified                                    ║
║  Changes:     +25 / -10 lines                              ║
║                                                             ║
╠════════════════════════════════════════════════════════════╣
║  Key Fixes:                                                 ║
║  1. Added 'email' to User interface (resolved 3 errors)    ║
║  2. Fixed path alias in tsconfig.json (resolved 2 errors)  ║
║  3. Added missing import statements (resolved 3 errors)    ║
╚════════════════════════════════════════════════════════════╝
```

---

## 4. 一般的なエラーパターンと解決策

### 4.1 TypeScript エラー

#### TS2322: Type is not assignable

```typescript
// エラー
const user: User = { name: "John" }; // 'email' is missing

// 修正
const user: User = { name: "John", email: "john@example.com" };
// または
const user: Partial<User> = { name: "John" };
```

#### TS2339: Property does not exist

```typescript
// エラー
user.email // Property 'email' does not exist on type 'User'

// 修正 1: インターフェースを更新
interface User {
  email: string;
}

// 修正 2: 型ガードを使用
if ('email' in user) {
  console.log(user.email);
}
```

#### TS2307: Cannot find module

```typescript
// エラー
import { utils } from '@/utils'; // Cannot find module '@/utils'

// 修正: tsconfig.json の paths を確認
{
  "compilerOptions": {
    "paths": {
      "@/*": ["src/*"]
    }
  }
}
```

### 4.2 ESLint エラー

#### no-unused-vars

```typescript
// エラー
const unused = "value"; // 'unused' is declared but never used

// 修正
// eslint-disable-next-line @typescript-eslint/no-unused-vars
const _unused = "value";
// または削除
```

#### prefer-const

```typescript
// エラー
let value = 10; // 'value' is never reassigned

// 修正
const value = 10;
```

### 4.3 依存関係エラー

#### Peer dependency warning

```bash
# エラー
npm WARN peer dep missing: react@^18.0.0

# 修正
npm install react@^18.0.0
```

#### Version mismatch

```bash
# エラー
Module not found: Can't resolve 'lodash' in ...

# 修正
npm install lodash
# または
npm install --legacy-peer-deps
```

---

## 5. コマンド一覧

| コマンド | 説明 |
|---------|------|
| `/build-fix` | ビルドエラーを分析して自動修正を開始 |
| `/build-fix analyze` | エラーの分析のみ実行（修正なし） |
| `/build-fix --max-iterations N` | 最大反復回数を指定 |
| `/build-fix --dry-run` | 修正内容をプレビュー（適用なし） |
| `/build-fix --report` | 最後の修正レポートを表示 |

---

## 6. MCP ツール統合

このスキルはMUSUBIX MCPサーバーの以下のツールと連携します：

- `workflow_get_status`: 現在のフェーズ確認
- `knowledge_query`: 過去のエラーパターン検索
- `pattern_query`: 学習済み修正パターンの検索

---

## 7. ベストプラクティス

### エラー修正時

- **1つずつ修正**: 複数のエラーを一度に修正しない
- **Root Cause**: 根本原因を特定してから修正
- **テスト実行**: 修正後は必ずテストを実行
- **コミット**: 意味のある単位でコミット

### 予防策

- **Pre-commit hooks**: `husky` + `lint-staged` でコミット前チェック
- **CI/CD**: PR時に自動ビルドチェック
- **IDE設定**: TypeScript/ESLint のリアルタイムチェック
- **型の厳格化**: `strict: true` in tsconfig.json

### 学習と改善

- 繰り返し発生するエラーパターンを記録
- チームで共有すべきエラーは `learning-hooks` で学習
- 設定改善の提案を検討

---

**Version**: 1.0.0  
**Last Updated**: 2026-01-25  
**Maintainer**: MUSUBIX Team
