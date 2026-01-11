# MUSUBIX Knowledge パッケージ

**パッケージ名**: `@musubix/knowledge`  
**バージョン**: 3.0.1  
**最終更新**: 2026-01-12

---

## 1. 概要

`@musubix/knowledge` は、MUSUBIX v3.0で導入されたGit-Native知識グラフシステムです。要件（REQ）、設計（DES）、タスク（TSK）、コードなどのエンティティとその関係をJSONファイルで管理し、Gitワークフローにネイティブに統合されます。

### 1.1 特徴

| 特徴 | 説明 |
|------|------|
| **サーバーレス** | データベース不要、JSONファイルで完結 |
| **Git-friendly** | diff/merge/PR対応、バージョン管理可能 |
| **軽量** | ゼロ依存（外部ライブラリ不要） |
| **階層型ID** | `requirement:REQ-001`、`design:DES-001` |
| **型安全** | TypeScriptによる完全な型定義 |

### 1.2 ストレージ構造

```
.knowledge/
└── graph.json      # 全エンティティ・リレーション
```

---

## 2. インストール

```bash
# 単体インストール
npm install @musubix/knowledge

# または musubix パッケージ経由
npm install musubix
```

---

## 3. 基本的な使い方

### 3.1 知識ストアの初期化

```typescript
import { createKnowledgeStore } from '@musubix/knowledge';

// .knowledge/graph.json を使用
const store = createKnowledgeStore('.knowledge');

// 既存データがあれば読み込み
await store.load();
```

### 3.2 エンティティの作成

```typescript
// 要件エンティティ
await store.putEntity({
  id: 'requirement:REQ-001',
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
  id: 'design:DES-001',
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
  id: 'task:TSK-001',
  type: 'task',
  name: 'AuthService実装',
  properties: { 
    estimate: '4h',
    status: 'not-started',
  },
  tags: ['implementation'],
});
```

### 3.3 エンティティの取得

```typescript
const entity = await store.getEntity('requirement:REQ-001');

if (entity) {
  console.log(entity.name);        // => 'ユーザー認証'
  console.log(entity.type);        // => 'requirement'
  console.log(entity.properties);  // => { ears: '...', priority: 'P0' }
}
```

### 3.4 エンティティの削除

```typescript
const deleted = await store.deleteEntity('task:TSK-001');
console.log(deleted); // => true
```

---

## 4. リレーション管理

### 4.1 リレーションの追加

```typescript
// 要件 → 設計 のトレーサビリティ
await store.addRelation({
  source: 'requirement:REQ-001',
  target: 'design:DES-001',
  type: 'tracesTo',
  properties: {
    confidence: 0.95,
    createdAt: new Date().toISOString(),
  },
});

// 設計 → タスク の実装関係
await store.addRelation({
  source: 'design:DES-001',
  target: 'task:TSK-001',
  type: 'implementedBy',
});
```

### 4.2 リレーションの取得

```typescript
// 出ていくリレーション
const outgoing = await store.getRelationsFrom('requirement:REQ-001');
// => [{ source: 'requirement:REQ-001', target: 'design:DES-001', type: 'tracesTo', ... }]

// 入ってくるリレーション
const incoming = await store.getRelationsTo('design:DES-001');
// => [{ source: 'requirement:REQ-001', target: 'design:DES-001', type: 'tracesTo', ... }]
```

### 4.3 リレーションの削除

```typescript
await store.removeRelation(
  'requirement:REQ-001',
  'design:DES-001',
  'tracesTo'
);
```

---

## 5. グラフクエリ

### 5.1 タイプでフィルタリング

```typescript
// すべての要件を取得
const requirements = await store.query({ type: 'requirement' });

// すべての設計を取得
const designs = await store.query({ type: 'design' });
```

### 5.2 タグでフィルタリング

```typescript
// セキュリティ関連のエンティティ
const securityEntities = await store.query({ 
  tags: ['security'] 
});

// 複数タグ（AND条件）
const authEntities = await store.query({ 
  tags: ['security', 'auth'] 
});
```

### 5.3 複合クエリ

```typescript
// セキュリティ関連の要件のみ
const securityRequirements = await store.query({
  type: 'requirement',
  tags: ['security'],
});
```

---

## 6. グラフ走査

### 6.1 関連エンティティの探索

```typescript
// 要件から関連する設計・タスクを探索
const related = await store.traverse('requirement:REQ-001', {
  direction: 'outgoing',      // 'outgoing' | 'incoming' | 'both'
  relationTypes: ['tracesTo', 'implementedBy'],
  maxDepth: 2,
});

for (const entity of related) {
  console.log(`${entity.type}: ${entity.name}`);
}
```

### 6.2 サブグラフの取得

```typescript
// 特定エンティティを中心としたサブグラフ
const subgraph = await store.getSubgraph('requirement:REQ-001', {
  depth: 3,
});

console.log('エンティティ数:', subgraph.entities.length);
console.log('リレーション数:', subgraph.relations.length);
```

---

## 7. 永続化

### 7.1 保存

```typescript
// すべての変更を保存
await store.save();
```

### 7.2 再読み込み

```typescript
// ファイルから再読み込み
await store.load();
```

### 7.3 JSON形式

`.knowledge/graph.json` の形式:

```json
{
  "entities": {
    "requirement:REQ-001": {
      "id": "requirement:REQ-001",
      "type": "requirement",
      "name": "ユーザー認証",
      "description": "ユーザーがログインできること",
      "properties": {
        "ears": "WHEN user submits credentials...",
        "priority": "P0"
      },
      "tags": ["security", "auth"],
      "createdAt": "2026-01-12T00:00:00.000Z",
      "updatedAt": "2026-01-12T00:00:00.000Z"
    }
  },
  "relations": [
    {
      "source": "requirement:REQ-001",
      "target": "design:DES-001",
      "type": "tracesTo",
      "properties": { "confidence": 0.95 }
    }
  ]
}
```

---

## 8. API リファレンス

### 8.1 KnowledgeStore インターフェース

```typescript
interface KnowledgeStore {
  // エンティティ操作
  putEntity(entity: Entity): Promise<Entity>;
  getEntity(id: string): Promise<Entity | null>;
  deleteEntity(id: string): Promise<boolean>;
  
  // リレーション操作
  addRelation(relation: Relation): Promise<Relation>;
  removeRelation(source: string, target: string, type: string): Promise<boolean>;
  getRelationsFrom(entityId: string): Promise<Relation[]>;
  getRelationsTo(entityId: string): Promise<Relation[]>;
  
  // クエリ
  query(filter: QueryFilter): Promise<Entity[]>;
  traverse(startId: string, options: TraverseOptions): Promise<Entity[]>;
  getSubgraph(centerId: string, options: SubgraphOptions): Promise<Subgraph>;
  
  // 永続化
  load(): Promise<void>;
  save(): Promise<void>;
}
```

### 8.2 Entity インターフェース

```typescript
interface Entity {
  id: string;              // 例: 'requirement:REQ-001'
  type: string;            // 例: 'requirement', 'design', 'task'
  name: string;            // 表示名
  description?: string;    // 説明
  properties?: Record<string, unknown>;  // カスタムプロパティ
  tags?: string[];         // タグ
  createdAt?: string;      // 作成日時
  updatedAt?: string;      // 更新日時
}
```

### 8.3 Relation インターフェース

```typescript
interface Relation {
  source: string;          // 元エンティティID
  target: string;          // 先エンティティID
  type: string;            // リレーションタイプ
  properties?: Record<string, unknown>;  // カスタムプロパティ
}
```

---

## 9. ユースケース

### 9.1 トレーサビリティマトリクスの構築

```typescript
import { createKnowledgeStore } from '@musubix/knowledge';

const store = createKnowledgeStore('.knowledge');
await store.load();

// すべての要件を取得
const requirements = await store.query({ type: 'requirement' });

// 各要件に対する設計・タスク・テストを追跡
for (const req of requirements) {
  const related = await store.traverse(req.id, {
    direction: 'outgoing',
    maxDepth: 3,
  });
  
  const designs = related.filter(e => e.type === 'design');
  const tasks = related.filter(e => e.type === 'task');
  const tests = related.filter(e => e.type === 'test');
  
  console.log(`${req.id}:`);
  console.log(`  設計: ${designs.length}`);
  console.log(`  タスク: ${tasks.length}`);
  console.log(`  テスト: ${tests.length}`);
}
```

### 9.2 影響分析

```typescript
// 要件変更時の影響範囲を特定
async function analyzeImpact(requirementId: string) {
  const affected = await store.traverse(requirementId, {
    direction: 'outgoing',
    maxDepth: 5,
  });
  
  return {
    designs: affected.filter(e => e.type === 'design'),
    tasks: affected.filter(e => e.type === 'task'),
    code: affected.filter(e => e.type === 'code'),
    tests: affected.filter(e => e.type === 'test'),
  };
}
```

---

## 10. 関連パッケージ

| パッケージ | 説明 |
|------------|------|
| `@musubix/policy` | 9憲法条項に基づくポリシー検証 |
| `@musubix/decisions` | Architecture Decision Records管理 |
| `musubix` | 3パッケージを含むメインパッケージ |

---

## 11. 参照

- [MUSUBIX v3.0 User Guide](../MUSUBIX-v3.0-User-Guide.md)
- [Migration Guide from YATA](../MIGRATION-v3.0.md)
- [GitHub Repository](https://github.com/nahisaho/MUSUBIX)
- [npm Package](https://www.npmjs.com/package/@musubix/knowledge)
