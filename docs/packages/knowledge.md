# @musubix/knowledge マニュアル

> Git-Native Knowledge Store - ファイルベースの知識グラフ管理

| 項目 | 内容 |
|------|------|
| **パッケージ名** | `@musubix/knowledge` |
| **バージョン** | 3.0.0 |
| **導入バージョン** | MUSUBIX v3.0.0 |
| **ストレージ形式** | JSON (`.knowledge/graph.json`) |

---

## 概要

`@musubix/knowledge` は、MUSUBIX v3.0.0で導入されたGit-Nativeな知識グラフ管理パッケージです。要件（REQ）、設計（DES）、タスク（TSK）、コード、決定事項などのエンティティとその関係を、Gitで管理可能なJSONファイルとして保存します。

### 特徴

- **Git-Friendly**: JSON形式で差分管理が容易
- **軽量**: 外部データベース不要、ファイルシステムのみで動作
- **型安全**: TypeScriptで完全な型定義
- **トレーサビリティ**: REQ→DES→TSK→Codeの追跡が可能

---

## インストール

```bash
npm install @musubix/knowledge
```

---

## クイックスタート

```typescript
import { createKnowledgeStore } from '@musubix/knowledge';

// 1. Knowledge Store を作成
const store = createKnowledgeStore('.knowledge');

// 2. エンティティを追加
await store.putEntity({
  id: 'REQ-001',
  type: 'requirement',
  name: 'ユーザー認証',
  description: 'ユーザーがログインできること',
  properties: { priority: 'P0' },
  tags: ['security', 'auth'],
});

await store.putEntity({
  id: 'DES-001',
  type: 'design',
  name: '認証設計',
  description: 'JWT認証を使用',
  properties: { pattern: 'Token-Based Auth' },
  tags: ['security'],
});

// 3. リレーションを作成
await store.addRelation({
  id: 'rel-001',
  source: 'DES-001',
  target: 'REQ-001',
  type: 'implements',
});

// 4. 保存（永続化）
await store.save();

// 5. 取得
const req = await store.getEntity('REQ-001');
console.log(req?.name); // => 'ユーザー認証'

// 6. クエリ
const requirements = await store.query({ type: 'requirement' });
console.log(requirements.length); // => 1

// 7. グラフ走査
const chain = await store.traverse('REQ-001', { depth: 2 });
console.log(chain.map(e => e.id)); // => ['REQ-001', 'DES-001']
```

---

## API リファレンス

### `createKnowledgeStore(basePath: string): KnowledgeStore`

Knowledge Store のファクトリ関数。

| パラメータ | 型 | 説明 |
|-----------|---|------|
| `basePath` | `string` | ストレージディレクトリのパス（例: `.knowledge`） |

```typescript
const store = createKnowledgeStore('.knowledge');
```

---

## エンティティ操作

### `putEntity(entity: Entity): Promise<void>`

エンティティを追加または更新します。

```typescript
await store.putEntity({
  id: 'REQ-001',
  type: 'requirement',
  name: 'ユーザー認証',
  description: 'ユーザーがログインできること',
  properties: { priority: 'P0', stakeholder: 'セキュリティチーム' },
  tags: ['security', 'auth', 'P0'],
});
```

#### Entity インターフェース

| フィールド | 型 | 必須 | 説明 |
|-----------|---|------|------|
| `id` | `string` | ✅ | 一意識別子（例: `REQ-001`, `DES-001`） |
| `type` | `EntityType` | ✅ | エンティティタイプ |
| `name` | `string` | ✅ | 表示名 |
| `description` | `string` | - | 説明文 |
| `properties` | `Record<string, unknown>` | ✅ | カスタムプロパティ（空オブジェクト可） |
| `tags` | `string[]` | ✅ | タグ配列（空配列可） |
| `createdAt` | `string` | 自動 | 作成日時（ISO 8601） |
| `updatedAt` | `string` | 自動 | 更新日時（ISO 8601） |

#### EntityType

| 値 | 説明 | 例 |
|---|------|---|
| `requirement` | 要件 | `REQ-001` |
| `design` | 設計 | `DES-001` |
| `task` | タスク | `TSK-001` |
| `code` | コード | `func:UserService.login` |
| `decision` | 決定事項 | `ADR-001` |
| `pattern` | パターン | `pattern:Repository` |
| `constraint` | 制約 | `const:MaxUsers` |

---

### `getEntity(id: string): Promise<Entity | undefined>`

IDでエンティティを取得します。

```typescript
const entity = await store.getEntity('REQ-001');
if (entity) {
  console.log(entity.name);
}
```

---

### `deleteEntity(id: string): Promise<boolean>`

エンティティを削除します。関連するリレーションも自動的に削除されます。

```typescript
const deleted = await store.deleteEntity('REQ-001');
console.log(deleted); // => true
```

---

## リレーション操作

### `addRelation(relation: Relation): Promise<void>`

エンティティ間のリレーションを追加します。

```typescript
await store.addRelation({
  id: 'rel-001',
  source: 'DES-001',  // 設計
  target: 'REQ-001',  // 要件
  type: 'implements',
  properties: { coverage: '100%' },
});
```

#### Relation インターフェース

| フィールド | 型 | 必須 | 説明 |
|-----------|---|------|------|
| `id` | `string` | ✅ | 一意識別子 |
| `source` | `string` | ✅ | ソースエンティティID |
| `target` | `string` | ✅ | ターゲットエンティティID |
| `type` | `RelationType` | ✅ | リレーションタイプ |
| `properties` | `Record<string, unknown>` | - | カスタムプロパティ |

#### RelationType

| 値 | 説明 | 例 |
|---|------|---|
| `implements` | 実装する | DES → REQ |
| `depends_on` | 依存する | TSK → TSK |
| `traces_to` | 追跡する | Code → REQ |
| `related_to` | 関連する | 汎用 |
| `derives_from` | 派生する | REQ → REQ |
| `conflicts_with` | 競合する | REQ ↔ REQ |

---

### `getRelations(entityId: string, direction?: 'in' | 'out' | 'both'): Promise<Relation[]>`

エンティティに関連するリレーションを取得します。

```typescript
// すべてのリレーション（デフォルト）
const allRels = await store.getRelations('REQ-001');

// 出ていくリレーションのみ（source = REQ-001）
const outRels = await store.getRelations('REQ-001', 'out');

// 入ってくるリレーションのみ（target = REQ-001）
const inRels = await store.getRelations('REQ-001', 'in');
```

---

### `removeRelation(id: string): Promise<boolean>`

リレーションを削除します。

```typescript
const removed = await store.removeRelation('rel-001');
console.log(removed); // => true
```

---

## クエリ操作

### `query(filter: QueryFilter): Promise<Entity[]>`

フィルタ条件でエンティティを検索します。

```typescript
// タイプでフィルタ
const requirements = await store.query({ type: 'requirement' });

// 複数タイプでフィルタ
const reqAndDes = await store.query({ type: ['requirement', 'design'] });

// タグでフィルタ（AND条件）
const securityItems = await store.query({ tags: ['security'] });

// テキスト検索（name, descriptionで部分一致）
const authItems = await store.query({ text: '認証' });

// ページネーション
const page1 = await store.query({ type: 'requirement', limit: 10, offset: 0 });
const page2 = await store.query({ type: 'requirement', limit: 10, offset: 10 });
```

#### QueryFilter インターフェース

| フィールド | 型 | 説明 |
|-----------|---|------|
| `type` | `EntityType \| EntityType[]` | タイプフィルタ |
| `tags` | `string[]` | タグフィルタ（AND条件） |
| `text` | `string` | テキスト検索（name, description） |
| `limit` | `number` | 最大件数 |
| `offset` | `number` | オフセット |

---

### `search(text: string, options?: SearchOptions): Promise<Entity[]>`

テキストでエンティティを検索します。

```typescript
// 基本検索（name, description, tagsを検索）
const results = await store.search('認証');

// 特定フィールドのみ検索
const nameOnly = await store.search('認証', { fields: ['name'] });

// 大文字小文字を区別
const caseSensitive = await store.search('AUTH', { caseSensitive: true });

// 結果数を制限
const limited = await store.search('認証', { limit: 5 });
```

---

## グラフ操作

### `traverse(startId: string, options?: TraverseOptions): Promise<Entity[]>`

指定したエンティティから関連エンティティを走査します。

```typescript
// 基本走査（深さ3、双方向）
const chain = await store.traverse('REQ-001');

// 深さ指定
const shallow = await store.traverse('REQ-001', { depth: 1 });

// 特定のリレーションタイプのみ
const implements = await store.traverse('REQ-001', { 
  relationTypes: ['implements'] 
});

// 方向指定
const downstream = await store.traverse('REQ-001', { direction: 'out' });
const upstream = await store.traverse('DES-001', { direction: 'in' });
```

#### TraverseOptions インターフェース

| フィールド | 型 | デフォルト | 説明 |
|-----------|---|----------|------|
| `depth` | `number` | `3` | 最大深さ |
| `relationTypes` | `RelationType[]` | すべて | 走査するリレーションタイプ |
| `direction` | `'in' \| 'out' \| 'both'` | `'both'` | 走査方向 |

---

### `getSubgraph(rootId: string, depth: number): Promise<KnowledgeGraph>`

指定したエンティティを中心としたサブグラフを取得します。

```typescript
const subgraph = await store.getSubgraph('REQ-001', 2);
console.log(subgraph.metadata.entityCount);
console.log(subgraph.metadata.relationCount);
```

---

## 永続化

### `save(): Promise<void>`

現在のグラフを `.knowledge/graph.json` に保存します。

```typescript
await store.putEntity({ /* ... */ });
await store.addRelation({ /* ... */ });
await store.save(); // 必ず呼び出す
```

### `load(): Promise<void>`

`.knowledge/graph.json` からグラフを読み込みます。通常は自動的に呼び出されます。

```typescript
await store.load(); // 明示的に再読み込み
```

---

## 統計

### `getStats(): Stats`

グラフの統計情報を取得します。

```typescript
const stats = store.getStats();
console.log(stats.entityCount);     // => 10
console.log(stats.relationCount);   // => 15
console.log(stats.types.requirement); // => 5
console.log(stats.types.design);      // => 3
```

---

## ストレージ形式

### ディレクトリ構造

```
.knowledge/
└── graph.json    # メインのナレッジグラフ
```

### graph.json スキーマ

```json
{
  "version": "1.0.0",
  "metadata": {
    "lastModified": "2026-01-11T12:00:00.000Z",
    "entityCount": 10,
    "relationCount": 15
  },
  "entities": {
    "REQ-001": {
      "id": "REQ-001",
      "type": "requirement",
      "name": "ユーザー認証",
      "description": "ユーザーがログインできること",
      "properties": { "priority": "P0" },
      "tags": ["security", "auth"],
      "createdAt": "2026-01-11T10:00:00.000Z",
      "updatedAt": "2026-01-11T12:00:00.000Z"
    }
  },
  "relations": [
    {
      "id": "rel-001",
      "source": "DES-001",
      "target": "REQ-001",
      "type": "implements"
    }
  ]
}
```

---

## トレーサビリティの例

MUSUBIX SDDワークフローにおけるトレーサビリティチェーンの例：

```typescript
// 要件 → 設計 → タスク → コード のチェーンを作成

// 1. 要件
await store.putEntity({
  id: 'REQ-AUTH-001',
  type: 'requirement',
  name: 'ユーザーログイン',
  properties: { priority: 'P0' },
  tags: ['auth'],
});

// 2. 設計
await store.putEntity({
  id: 'DES-AUTH-001',
  type: 'design',
  name: 'JWT認証設計',
  properties: { pattern: 'Token-Based' },
  tags: ['auth'],
});

await store.addRelation({
  id: 'rel-des-req',
  source: 'DES-AUTH-001',
  target: 'REQ-AUTH-001',
  type: 'implements',
});

// 3. タスク
await store.putEntity({
  id: 'TSK-AUTH-001',
  type: 'task',
  name: 'AuthService実装',
  properties: { estimate: '4h' },
  tags: ['auth'],
});

await store.addRelation({
  id: 'rel-tsk-des',
  source: 'TSK-AUTH-001',
  target: 'DES-AUTH-001',
  type: 'implements',
});

// 4. コード
await store.putEntity({
  id: 'code:AuthService.login',
  type: 'code',
  name: 'AuthService.login()',
  properties: { file: 'src/auth/AuthService.ts', line: 42 },
  tags: ['auth'],
});

await store.addRelation({
  id: 'rel-code-tsk',
  source: 'code:AuthService.login',
  target: 'TSK-AUTH-001',
  type: 'implements',
});

await store.save();

// トレーサビリティチェーンを確認
const chain = await store.traverse('REQ-AUTH-001', { 
  direction: 'in',  // 要件に向かって来るもの
  depth: 10 
});

console.log('トレーサビリティチェーン:');
chain.forEach(e => console.log(`  ${e.type}: ${e.id}`));
// => requirement: REQ-AUTH-001
// => design: DES-AUTH-001
// => task: TSK-AUTH-001
// => code: code:AuthService.login
```

---

## MCP ツール連携

`@musubix/knowledge` は以下のMCPツールから利用されます：

| ツール名 | 説明 |
|---------|------|
| `knowledge_put_entity` | エンティティ作成/更新 |
| `knowledge_get_entity` | エンティティ取得 |
| `knowledge_delete_entity` | エンティティ削除 |
| `knowledge_add_relation` | リレーション追加 |
| `knowledge_query` | クエリ実行 |
| `knowledge_traverse` | グラフ走査 |

---

## CLI コマンド連携

```bash
# エンティティ追加
npx musubix knowledge put REQ-001 requirement "ユーザー認証"

# エンティティ取得
npx musubix knowledge get REQ-001

# エンティティ削除
npx musubix knowledge delete REQ-001

# リレーション追加
npx musubix knowledge link DES-001 REQ-001 implements

# クエリ
npx musubix knowledge query --type requirement

# グラフ走査
npx musubix knowledge traverse REQ-001 --depth 3
```

---

## ベストプラクティス

### 1. ID命名規則

```typescript
// ✅ 推奨: プレフィックス + 連番
'REQ-001', 'DES-001', 'TSK-001'

// ✅ 推奨: コードは関数パス形式
'code:UserService.create'
'code:auth/login.ts:42'

// ❌ 非推奨: 意味のないID
'entity1', 'xyz123'
```

### 2. 定期的な save() 呼び出し

```typescript
// ✅ 推奨: 操作後にsave
await store.putEntity({ /* ... */ });
await store.save();

// ✅ 推奨: バッチ操作後にsave
for (const entity of entities) {
  await store.putEntity(entity);
}
await store.save(); // まとめてsave
```

### 3. タグの活用

```typescript
// ✅ 推奨: 意味のあるタグ
tags: ['security', 'auth', 'P0', 'sprint-1']

// ❌ 非推奨: 曖昧なタグ
tags: ['important', 'todo']
```

---

## 関連ドキュメント

- [MIGRATION-v3.0.md](../MIGRATION-v3.0.md) - v2.x からの移行ガイド
- [@musubix/policy マニュアル](./policy.md) - ポリシーエンジン
- [@musubix/decisions マニュアル](./decisions.md) - ADR管理

---

**作成日**: 2026-01-11  
**バージョン**: 3.0.0
