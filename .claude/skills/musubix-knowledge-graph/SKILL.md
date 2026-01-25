# MUSUBIX Knowledge Graph スキル

> Git-Native知識グラフの操作

## WHEN/DO トリガー

| WHEN | DO |
|------|-----|
| 新規エンティティ登録 | `store.putEntity(entity)` |
| 関係性の定義 | `store.addRelation(relation)` |
| エンティティ検索 | `store.query(criteria)` |
| トレーサビリティ確認 | `store.traverse(id, options)` |

## クイック使用法

```typescript
import { createKnowledgeStore } from '@musubix/knowledge';

const store = createKnowledgeStore('.knowledge');

// エンティティ作成
await store.putEntity({
  id: 'REQ-001',
  type: 'requirement',
  name: 'ユーザー認証',
  properties: { ears: 'WHEN user submits...', priority: 'P0' },
  tags: ['security', 'auth'],
});

// リレーション作成
await store.addRelation({
  source: 'DES-001',
  target: 'REQ-001',
  type: 'implements',
});

// 検索
const results = await store.query({ type: 'requirement', tags: ['security'] });

// トレーサビリティ
const chain = await store.traverse('REQ-001', { direction: 'incoming', maxDepth: 5 });
await store.save();
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

## ストレージ

```
.knowledge/
└── graph.json    # 全エンティティとリレーション
```

## 出力フォーマット

```
┌─────────────────────────────────────────┐
│ Knowledge Graph Traversal               │
├─────────────────────────────────────────┤
│ REQ-001 (requirement)                   │
│   └─implements─→ DES-001 (design)       │
│       └─realizes─→ TSK-001 (task)       │
│           └─fulfills─→ CODE-001 (code)  │
├─────────────────────────────────────────┤
│ Entities: 4 | Relations: 3 | Depth: 3   │
└─────────────────────────────────────────┘
```
