# Technology Stack

**Project**: MUSUBIX
**Last Updated**: 2026-01-04
**Version**: 1.1.10
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
├── core/           # @nahisaho/musubix-core (v1.1.9)
├── mcp-server/     # @nahisaho/musubix-mcp-server (v1.1.9)
└── yata-client/    # @nahisaho/musubix-yata-client (v1.1.9)
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
| `learning/` | 自己学習 | フィードバック収集、パターン抽出 |
| `requirements/` | 要件分析 | EARS検証、オントロジーマッピング |
| `traceability/` | トレーサビリティ | アーティファクト追跡、カバレッジ分析 |
| `validators/` | 検証 | EARS検証器 |

## Domain Support

| カテゴリ | ドメイン数 | コンポーネント数 |
|---------|-----------|-----------------|
| 合計 | 60 | ~390 |

### 対応ドメイン一覧

- **汎用**: general
- **業種特化**: healthcare, banking, insurance, realestate, hotel, restaurant, retail, ecommerce, logistics, manufacturing, construction, agriculture, agritech
- **専門サービス**: legal, accounting, hr, recruitment, marketing, crm
- **教育・学習**: education, elearning, library
- **エンターテイメント**: game, music, media, cinema, museum, streaming, podcast, news
- **交通・物流**: travel, aviation, railway, shipping, vehicle, parking
- **通信・IT**: telecom, iot, security
- **医療・福祉**: pharmacy, veterinary, caregiving, childcare
- **イベント・冠婚葬祭**: event, ticketing, wedding, funeral
- **その他**: fitness, sports, beauty, petcare, rental, laundry, subscription, crowdfunding, auction, charity, government, election, survey, energy, environment, archive, social, property, warehouse

## Key Features

### 1. EARS検証器（Symbolic Reasoning）

5つのEARSパターンをサポート（**Markdownブロッククォート形式対応** v1.1.9+）：

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
| 全テスト（459件） | ~1.0s | Vitest実行 |

## Self-Learning System (v1.1.10)

### ベストプラクティスCLI

```bash
# 一覧表示
npx musubix learn bp-list

# 詳細表示（コード例付き）
npx musubix learn bp-show BP-CODE-001

# カテゴリ別フィルタ
npx musubix learn best-practices --category code
```

### 学習済みパターン（17件）

| ID | 名称 | 信頼度 | ソース |
|----|------|--------|--------|
| BP-CODE-001 | Entity Input DTO | 95% | P07-08 |
| BP-CODE-002 | Date-based ID Format | 90% | P07-08 |
| BP-CODE-003 | Value Objects | 90% | P08 |
| BP-CODE-004 | Function-based Value Objects | 95% | P13-14 |
| BP-CODE-005 | Result Type | 95% | P13-14 |
| BP-DESIGN-001 | Status Transition Map | 95% | P08, P13-14 |
| BP-DESIGN-002 | Repository Async Pattern | 85% | P08 |
| BP-DESIGN-003 | Service Layer with DI | 90% | P07-08 |
| BP-DESIGN-004 | Optimistic Locking | 90% | P10 |
| BP-DESIGN-005 | AuditService | 85% | P09-10 |
| BP-DESIGN-006 | Entity Counter Reset | 95% | P13-14 |
| BP-DESIGN-007 | Expiry Time Logic | 90% | P14 |
| BP-TEST-001 | Test Counter Reset | 95% | P07 |
| BP-TEST-002 | Verify API Before Test | 80% | P08 |
| BP-TEST-003 | Vitest ESM Configuration | 85% | P07 |
| BP-TEST-004 | Result Type Test Pattern | 95% | P13-14 |
| BP-TEST-005 | Status Transition Testing | 90% | P14 |

### コード生成テンプレート（12タイプ）

| タイプ | 説明 | 追加バージョン |
|--------|------|----------------|
| class | クラス定義 | v1.0.0 |
| interface | インターフェース | v1.0.0 |
| function | 関数 | v1.0.0 |
| module | モジュール | v1.0.0 |
| test | テストファイル | v1.0.0 |
| api-endpoint | APIエンドポイント | v1.0.0 |
| model | データモデル | v1.0.0 |
| repository | リポジトリ | v1.0.0 |
| service | サービス層 | v1.0.0 |
| controller | コントローラ | v1.0.0 |
| value-object | Value Object (function-based) | v1.1.10 |
| entity | エンティティ (status transition, counter reset) | v1.1.10 |

---

*Last Updated: 2026-01-04 by MUSUBIX v1.1.10*
