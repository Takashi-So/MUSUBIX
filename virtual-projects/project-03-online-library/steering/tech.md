# Online Library Management System - Technology Stack

## 言語・ランタイム

| 項目 | 選択 | バージョン |
|-----|------|-----------|
| 言語 | TypeScript | ^5.3.0 |
| ランタイム | Node.js | ^20.0.0 |
| パッケージマネージャ | npm | ^10.0.0 |

## フレームワーク・ライブラリ

| カテゴリ | 選択 | 用途 |
|---------|------|------|
| Webフレームワーク | Hono | REST API |
| ORM | Prisma | データベースアクセス |
| バリデーション | Zod | スキーマ検証 |
| テスト | Vitest | ユニット・統合テスト |
| ロギング | Pino | 構造化ログ |

## データベース

| 用途 | 選択 | 理由 |
|-----|------|------|
| メインDB | PostgreSQL | リレーショナルデータ |
| キャッシュ | Redis | セッション・予約キュー |
| 全文検索 | Elasticsearch | 書籍検索 |

## インフラ（想定）

| 項目 | 選択 |
|-----|------|
| コンテナ | Docker |
| オーケストレーション | Kubernetes |
| CI/CD | GitHub Actions |

## コーディング規約

- ESLint + Prettier
- Conventional Commits
- 関数は単一責任
- エラーは型安全に（Result型）

---

**生成日**: 2026-01-04
