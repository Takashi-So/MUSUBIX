# Online Library Management System - AI Agent Guide

> **AI Coding Agent向け**: このファイルはAIエージェントがプロジェクトを理解するためのガイドです。

## 🎯 プロジェクト概要

**Online Library Management System**は、図書館の蔵書・会員・貸出管理を効率化するシステムです。

| 項目 | 詳細 |
|------|------|
| **バージョン** | 1.0.0 |
| **ドメイン** | library |
| **言語** | TypeScript |
| **フレームワーク** | Node.js + Hono |

## 📁 ディレクトリ構造

```
project-03-online-library/
├── steering/           # プロジェクトメモリ
│   ├── product.md      # プロダクトコンテキスト
│   ├── structure.md    # アーキテクチャ
│   ├── tech.md         # 技術スタック
│   └── rules/          # 憲法条項
├── storage/
│   ├── specs/          # 要件定義書
│   ├── design/         # 設計書
│   └── tasks/          # タスク
├── src/                # ソースコード
└── __tests__/          # テスト
```

## 🛠️ SDDワークフロー

1. **要件定義**: storage/specs/REQ-*.md（EARS形式）
2. **設計**: storage/design/DES-*.md（C4モデル）
3. **タスク**: storage/tasks/TSK-*.md
4. **実装**: src/（テスト先行）
5. **検証**: トレーサビリティマトリクス

## 📋 憲法条項

9つの憲法条項（MUSUBIX Constitution）に従う。

## 🔑 主要エンティティ

- **Book**: 書籍情報
- **BookCopy**: 書籍の物理的コピー
- **Member**: 会員
- **Loan**: 貸出
- **Reservation**: 予約

---

**生成日**: 2026-01-04
