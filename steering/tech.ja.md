# Technology Stack

**Project**: MUSUBIX
**Last Updated**: 2026-01-03
**Version**: 1.0.10
**Status**: Production Ready

---

## Overview

MUSUBIXはニューロシンボリックAIコーディングシステムであり、LLM（Large Language Model）とシンボリック推論（知識グラフ）を統合しています。

## Core Technologies

| カテゴリ | 技術 | バージョン | 状態 |
|---------|------|-----------|------|
| 言語 | TypeScript | 5.3+ | ✅ 採用 |
| ランタイム | Node.js | 20.0.0+ | ✅ 採用 |
| パッケージマネージャ | npm | 10.0.0+ | ✅ 採用 |
| ビルドシステム | tsc | 5.3+ | ✅ 採用 |
| テストフレームワーク | Vitest | 4.0+ | ✅ 採用 |
| リンター | ESLint | 9.0+ | ✅ 採用 |

## Architecture

### パッケージ構成（モノレポ）

```
packages/
├── core/           # @nahisaho/musubix-core (v1.0.9)
├── mcp-server/     # @nahisaho/musubix-mcp-server (v1.0.3)
└── yata-client/    # @nahisaho/musubix-yata-client (v1.0.3)
```

### Core Package モジュール

| モジュール | 役割 | 主要機能 |
|-----------|------|---------|
| `auth/` | 認証・認可 | JWT/OAuth管理 |
| `cli/` | CLIインターフェース | コマンドライン処理 |
| `codegen/` | コード生成・解析 | テンプレート生成、静的解析、セキュリティスキャン |
| `design/` | 設計 | パターン検出、C4モデル、ADR生成 |
| `error/` | エラーハンドリング | 構造化エラー、リカバリー |
| `explanation/` | 説明生成 | 推論グラフ、可視化 |
| `requirements/` | 要件分析 | EARS検証、オントロジーマッピング |
| `traceability/` | トレーサビリティ | アーティファクト追跡、カバレッジ分析 |
| `validators/` | 検証 | EARS検証器 |

## Key Features

### 1. EARS検証器（Symbolic Reasoning）

5つのEARSパターンをサポート：

| パターン | 構文 | 信頼度ボーナス |
|---------|------|---------------|
| Event-driven | `WHEN <trigger>, THE <system> SHALL <action>` | +0.25 |
| State-driven | `WHILE <state>, THE <system> SHALL <action>` | +0.25 |
| Unwanted | `THE <system> SHALL NOT <behavior>` | +0.20 |
| Optional | `WHERE <feature>, THE <system> SHALL <action>` | +0.20 |
| Ubiquitous | `THE <system> SHALL <action>` | +0.00 |

**最適化機能**:
- 早期終了（高信頼度≥0.85で即座にマッチ）
- 事前チェック（"shall"キーワードの存在確認）

### 2. トレーサビリティ管理

**カバレッジ計算（重み付け平均）**:
- 要件: 30%
- 設計: 20%
- コード: 30%
- テスト: 20%

**最適化機能**:
- リンクインデックス（O(1)検索）
- アーティファクト型インデックス

### 3. アーティファクトステータス

```typescript
type ArtifactStatus =
  | 'draft'       // 初期作成状態
  | 'active'      // アクティブ開発中
  | 'approved'    // レビュー承認済み
  | 'implemented' // コード実装完了
  | 'verified'    // テスト・検証完了
  | 'deprecated'  // 非推奨
  | 'deleted';    // 削除予定
```

### 4. ニューロシンボリック統合ルール（REQ-INT-002）

| シンボリック結果 | ニューラル信頼度 | 最終決定 |
|-----------------|-----------------|---------|
| invalid | - | ニューラル結果を棄却 |
| valid | ≥0.8 | ニューラル結果を採用 |
| valid | <0.8 | シンボリック結果を優先 |

## Development Commands

```bash
# 依存関係インストール
npm install

# 全パッケージビルド
npm run build

# テスト実行
npm run test

# コード品質
npm run lint
npm run typecheck

# クリーンアップ
npm run clean
```

## Performance Benchmarks

| 機能 | 処理速度 | 備考 |
|------|---------|------|
| EARS検証（単一要件） | <1ms | 早期終了最適化 |
| パターンマッチング | <5ms | 信頼度計算含む |
| トレーサビリティリンク検索 | O(1) | インデックス利用 |
| C4モデル生成 | <10ms | 11要素、6関係 |
| 全テスト（262件） | ~750ms | Vitest実行 |

---

*Last Updated: 2026-01-03 by MUSUBIX v1.0.10*
