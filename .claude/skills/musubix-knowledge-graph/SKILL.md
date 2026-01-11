# MUSUBIX Knowledge Graph スキル

このスキルを使用して、`@musubix/knowledge` パッケージによるGit-Native知識グラフを操作します。

## 概要

MUSUBIX v3.0の知識グラフシステムは、要件（REQ）、設計（DES）、タスク（TSK）、コードなどのエンティティとその関係をJSONファイルで管理します。

## 基本的な使い方

### 知識グラフの初期化

```typescript
import { createKnowledgeStore } from '@musubix/knowledge';

const store = createKnowledgeStore('.knowledge');
```

### エンティティの作成

```typescript
// 要件エンティティ
await store.putEntity({
  id: 'REQ-001',
  type: 'requirement',
  name: 'ユーザー認証',
  description: 'ユーザーがログインできること',
  properties: {
    ears: 'WHEN user submits credentials, THE system SHALL authenticate the user',
    priority: 'P0',
  },
  tags: ['security', 'auth'],
});

// 設計エンティティ
await store.putEntity({
  id: 'DES-001',
  type: 'design',
  name: 'JWT認証設計',
  description: 'JWTトークンベースの認証フロー',
  properties: {
    pattern: 'Token-Based Authentication',
    c4Level: 'component',
  },
  tags: ['security', 'jwt'],
});

// タスクエンティティ
await store.putEntity({
  id: 'TSK-001',
  type: 'task',
  name: 'AuthService実装',
  properties: { estimate: '4h' },
  tags: ['implementation'],
});
```

### リレーションの作成

```typescript
// 設計が要件を実装
await store.addRelation({
  source: 'DES-001',
  target: 'REQ-001',
  type: 'implements',
});

// タスクが設計を実現
await store.addRelation({
  source: 'TSK-001',
  target: 'DES-001',
  type: 'realizes',
});

// 永続化
await store.save();
```

### 検索

```typescript
// タイプで検索
const requirements = await store.query({ type: 'requirement' });

// タグで検索
const securityItems = await store.query({ tags: ['security'] });

// テキスト検索
const authRelated = await store.query({ text: '認証' });
```

### グラフ走査（トレーサビリティ）

```typescript
// REQ-001から辿れるすべてのエンティティ
const chain = await store.traverse('REQ-001', {
  direction: 'incoming',
  maxDepth: 5,
});
console.log(chain.map(e => e.id));
// => ['REQ-001', 'DES-001', 'TSK-001']
```

## ストレージ構造

```
.knowledge/
└── graph.json    # 全エンティティとリレーション
```

## エンティティタイプ

| タイプ | 説明 | ID形式 |
|--------|------|--------|
| `requirement` | 要件 | `REQ-XXX-NNN` |
| `design` | 設計 | `DES-XXX-NNN` |
| `task` | タスク | `TSK-XXX-NNN` |
| `code` | コード | `CODE-XXX-NNN` |
| `test` | テスト | `TEST-XXX-NNN` |
| `pattern` | パターン | `PAT-XXX-NNN` |

## リレーションタイプ

| タイプ | 説明 |
|--------|------|
| `implements` | 設計が要件を実装 |
| `realizes` | タスクが設計を実現 |
| `fulfills` | コードがタスクを達成 |
| `tests` | テストがコードを検証 |
| `depends_on` | 依存関係 |
| `supersedes` | 置き換え |

## 関連パッケージ

- `@musubix/policy` - 9憲法条項の自動検証
- `@musubix/decisions` - Architecture Decision Records管理

## 参照

- [ユーザーガイド](docs/MUSUBIX-v3.0-User-Guide.md)
- [knowledge.md](docs/packages/knowledge.md)
