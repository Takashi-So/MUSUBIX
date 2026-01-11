# YATA Local ユーザーガイド

> **YATA Local** - SQLiteベースのローカル知識グラフストレージ

## 📖 概要

YATA Local (`@nahisaho/yata-local`) は、AIコーディングアシスタント向けのローカル知識グラフストレージです。SQLiteをバックエンドとし、コード構造、関係性、パターンを効率的に管理します。

### 主な特徴

| 機能 | 説明 |
|------|------|
| **エンティティ管理** | クラス、関数、インターフェースなどのコード要素を格納 |
| **関係性追跡** | 継承、呼び出し、依存関係などを記録 |
| **推論エンジン** | ルールベースの推論と制約検証 |
| **クエリエンジン** | パターンマッチ、パス探索、サブグラフ抽出 |
| **インポート/エクスポート** | JSON、RDF、GraphML形式に対応 |
| **KGPR** | Knowledge Graph Pull Request（知識共有） |
| **Wake-Sleep学習** | パターン学習と統合 |

---

## 🚀 インストール

```bash
npm install @nahisaho/yata-local
```

### 前提条件

- Node.js >= 20.0.0
- npm >= 10.0.0

---

## 📘 基本的な使い方

### 初期化と接続

```typescript
import { createYataLocal } from '@nahisaho/yata-local';

// インスタンス作成
const yata = createYataLocal({
  path: './.yata/knowledge.db',  // データベースファイルパス
  walMode: true,                  // WALモード（推奨）
  cacheSize: 64 * 1024,          // キャッシュサイズ（KB）
});

// データベースを開く
await yata.open();

// ... 操作 ...

// 終了時にクローズ
await yata.close();
```

### 設定オプション

```typescript
interface DatabaseConfig {
  path: string;           // データベースファイルパス（デフォルト: '.yata/knowledge.db'）
  walMode: boolean;       // WALモード有効化（デフォルト: true）
  mmapSize: number;       // メモリマッピングサイズ（デフォルト: 256MB）
  cacheSize: number;      // キャッシュサイズ（デフォルト: 64MB）
  foreignKeys: boolean;   // 外部キー制約（デフォルト: true）
  encryption?: {          // 暗号化設定（オプション）
    enabled: boolean;
    key: string;
  };
}
```

---

## 📦 エンティティ操作

### エンティティの追加

```typescript
// 単一エンティティの追加
const entityId = await yata.addEntity({
  type: 'class',
  name: 'UserService',
  namespace: 'app.services',
  filePath: 'src/services/user.ts',
  line: 10,
  description: 'ユーザー管理サービス',
  metadata: {
    entityKind: 'service',
    isExported: true,
  },
});

console.log('Created entity:', entityId);
// => Created entity: 550e8400-e29b-41d4-a716-446655440000
```

### バッチ追加

```typescript
// 複数エンティティの一括追加
const ids = await yata.addEntities([
  {
    type: 'interface',
    name: 'IUserRepository',
    namespace: 'app.repositories',
    filePath: 'src/repositories/user.ts',
  },
  {
    type: 'function',
    name: 'createUser',
    namespace: 'app.services.user',
    filePath: 'src/services/user.ts',
  },
]);

console.log('Created entities:', ids);
```

### エンティティの取得

```typescript
// IDで取得
const entity = await yata.getEntity(entityId);

// 名前で取得
const userService = await yata.getEntityByName('UserService', 'app.services');

// タイプで取得
const classes = await yata.getEntitiesByType('class');

// 名前空間で取得
const serviceEntities = await yata.getEntitiesByNamespace('app.services');

// メタデータのentityKindで取得
const services = await yata.getEntitiesByKind('service');
```

### エンティティの更新

```typescript
// 更新
await yata.updateEntity(entityId, {
  description: '更新された説明',
  metadata: { version: '2.0.0' },
});

// アップサート（存在すれば更新、なければ追加）
const result = await yata.upsertEntity({
  type: 'class',
  name: 'UserService',
  namespace: 'app.services',
  filePath: 'src/services/user.ts',
  metadata: { version: '3.0.0' },
}, 'name-namespace');  // マッチ条件: name + namespace

console.log(result);
// => { id: '...', created: false }  // 更新された場合
// => { id: '...', created: true }   // 新規作成された場合
```

### エンティティの削除

```typescript
// IDで削除
await yata.deleteEntity(entityId);

// ファイルパスで一括削除
const deletedCount = await yata.deleteEntitiesByFile('src/services/user.ts');
console.log(`Deleted ${deletedCount} entities`);
```

---

## 🔗 関係性操作

### エンティティタイプ

```typescript
type EntityType =
  | 'class'      // クラス
  | 'interface'  // インターフェース
  | 'function'   // 関数
  | 'method'     // メソッド
  | 'variable'   // 変数
  | 'constant'   // 定数
  | 'type'       // 型定義
  | 'enum'       // 列挙型
  | 'module'     // モジュール
  | 'package'    // パッケージ
  | 'file'       // ファイル
  | 'parameter'  // パラメータ
  | 'property'   // プロパティ
  | 'import'     // インポート
  | 'export'     // エクスポート
  | 'unknown';   // 不明
```

### 関係性タイプ

```typescript
type RelationType =
  | 'calls'              // 呼び出し
  | 'imports'            // インポート
  | 'exports'            // エクスポート
  | 'extends'            // 継承
  | 'inherits'           // 継承
  | 'implements'         // 実装
  | 'contains'           // 包含
  | 'uses'               // 使用
  | 'defines'            // 定義
  | 'references'         // 参照
  | 'depends-on'         // 依存
  | 'transitively-depends-on'  // 推移的依存
  | 'type-compatible'    // 型互換
  | 'has-method'         // メソッド保持
  | 'overrides'          // オーバーライド
  | 'returns'            // 戻り値
  | 'parameter_of'       // パラメータ
  | 'member_of'          // メンバー
  | 'related-to'         // 関連
  | 'defined-in-same-file'  // 同一ファイル内定義
  | 'unknown';           // 不明
```

### 関係性の追加と取得

```typescript
// 関係性の追加
const relId = await yata.addRelationship(
  classId,        // ソースエンティティID
  interfaceId,    // ターゲットエンティティID
  'implements',   // 関係タイプ
  { isRequired: true }  // メタデータ
);

// 関係性の取得
const outgoing = await yata.getRelationships(classId, 'out');   // 出力方向
const incoming = await yata.getRelationships(classId, 'in');    // 入力方向
const all = await yata.getRelationships(classId, 'both');       // 両方向

// 関係性の削除
await yata.deleteRelationship(relId);
```

---

## 🔍 クエリ操作

### 基本クエリ

```typescript
const result = await yata.query({
  entityFilters: {
    types: ['class', 'interface'],
    namespaces: ['app.services'],
  },
  textSearch: 'User',
  relationshipFilters: {
    types: ['implements', 'extends'],
  },
}, {
  limit: 100,
  offset: 0,
  sortBy: 'name',
  sortOrder: 'asc',
});

console.log(`Found ${result.entities.length} entities`);
```

### 全文検索

```typescript
const entities = await yata.search('UserService', 50);
```

### パス探索

```typescript
// 2つのエンティティ間のパスを探索
const path = await yata.findPath(startId, endId, {
  maxDepth: 5,
  relationshipTypes: ['calls', 'imports'],
  direction: 'forward',
});

if (path) {
  console.log('Path found:', path.entities.map(e => e.name).join(' -> '));
}
```

### サブグラフ抽出

```typescript
// エンティティ周辺のサブグラフを抽出
const subgraph = await yata.extractSubgraph(rootId, {
  depth: 3,
  entityTypes: ['class', 'interface', 'function'],
  relationshipTypes: ['calls', 'implements'],
  direction: 'both',
});

console.log(`Subgraph: ${subgraph.entities.length} entities, ${subgraph.relationships.length} relationships`);
```

### パターンマッチ

```typescript
// グラフパターンのマッチング
const matches = await yata.matchPattern({
  nodes: [
    { id: 'service', type: 'class', namePattern: /.*Service$/ },
    { id: 'repository', type: 'interface', namePattern: /.*Repository$/ },
  ],
  edges: [
    { sourceId: 'service', targetId: 'repository', type: 'uses' },
  ],
});

for (const match of matches) {
  console.log('Match:', match.bindings);
}
```

### トラバーサル

```typescript
// 関係性に沿ってトラバース
const reachable = await yata.traverse(
  startId,
  ['calls', 'imports'],  // 関係タイプ
  'forward',              // 方向
  10                      // 最大ホップ数
);
```

### 近傍取得

```typescript
// エンティティの近傍を取得
const neighbors = await yata.getNeighbors(entityId, {
  direction: 'both',
  relationshipTypes: ['calls'],
  entityTypes: ['function', 'method'],
});

for (const { entity, relationship } of neighbors) {
  console.log(`${relationship.type} -> ${entity.name}`);
}
```

---

## 💬 自然言語クエリ（v2.4.1 NEW!）

YATA Localは、日本語と英語の自然言語によるクエリをサポートしています。コード構造について自然な言葉で質問できます。

### 基本的な使い方

```typescript
// ask() メソッドを使用
const result = await yata.ask('UserServiceを呼び出している関数は？');

console.log('Intent:', result.parsedQuery.intent);
// => Intent: find_callers

console.log('Results:');
for (const entity of result.entities) {
  console.log(`  - ${entity.name} (${entity.type})`);
}

console.log('Explanation:', result.explanation);
// => 「UserService」を呼び出している3件の関数が見つかりました
```

### 自然言語 → API コマンド対応表

自然言語クエリは内部で適切なAPIメソッドに変換されます。

#### 呼び出し元を探す（find_callers）

| 自然言語クエリ | 等価なAPIコマンド |
|--------------|------------------|
| `UserServiceを呼び出している関数は？` | `yata.getRelationships(userServiceId, 'in', { types: ['calls'] })` |
| `What functions call UserService?` | `yata.query({ relationshipFilters: { types: ['calls'], targetId: userServiceId } })` |
| `loginの呼び出し元を表示` | `yata.traverse(loginId, ['calls'], 'backward', 1)` |

```typescript
// 自然言語
const result = await yata.ask('UserServiceを呼び出している関数は？');

// 等価なAPI呼び出し
const entity = await yata.getEntityByName('UserService');
const callers = await yata.getRelationships(entity.id, 'in');
const callerEntities = callers
  .filter(r => r.type === 'calls')
  .map(r => yata.getEntity(r.sourceId));
```

#### 呼び出し先を探す（find_callees）

| 自然言語クエリ | 等価なAPIコマンド |
|--------------|------------------|
| `UserServiceは何を呼び出していますか？` | `yata.getRelationships(userServiceId, 'out', { types: ['calls'] })` |
| `What does UserService call?` | `yata.traverse(userServiceId, ['calls'], 'forward', 1)` |
| `processOrderの呼び出し先` | `yata.getNeighbors(processOrderId, { direction: 'out', relationshipTypes: ['calls'] })` |

```typescript
// 自然言語
const result = await yata.ask('UserServiceは何を呼び出していますか？');

// 等価なAPI呼び出し
const entity = await yata.getEntityByName('UserService');
const callees = await yata.getRelationships(entity.id, 'out');
const calleeEntities = callees
  .filter(r => r.type === 'calls')
  .map(r => yata.getEntity(r.targetId));
```

#### 実装を探す（find_implementations）

| 自然言語クエリ | 等価なAPIコマンド |
|--------------|------------------|
| `Repositoryの実装を表示` | `yata.getRelationships(repositoryId, 'in', { types: ['implements'] })` |
| `What implements UserInterface?` | `yata.query({ relationshipFilters: { types: ['implements'], targetId: interfaceId } })` |
| `UserInterfaceを実装しているクラス` | `yata.matchPattern({ edges: [{ targetId: 'interface', type: 'implements' }] })` |

```typescript
// 自然言語
const result = await yata.ask('Repositoryの実装を表示');

// 等価なAPI呼び出し
const iface = await yata.getEntityByName('Repository');
const implementations = await yata.getRelationships(iface.id, 'in');
const implEntities = implementations
  .filter(r => r.type === 'implements')
  .map(r => yata.getEntity(r.sourceId));
```

#### 依存関係を探す（find_dependencies）

| 自然言語クエリ | 等価なAPIコマンド |
|--------------|------------------|
| `UserServiceの依存関係を表示` | `yata.getRelationships(userServiceId, 'out', { types: ['depends-on', 'imports', 'uses'] })` |
| `What does UserService depend on?` | `yata.traverse(userServiceId, ['depends-on', 'imports'], 'forward', 1)` |
| `OrderProcessorは何に依存していますか？` | `yata.extractSubgraph(processorId, { depth: 1, relationshipTypes: ['depends-on'] })` |

```typescript
// 自然言語
const result = await yata.ask('UserServiceの依存関係を表示');

// 等価なAPI呼び出し
const entity = await yata.getEntityByName('UserService');
const deps = await yata.getRelationships(entity.id, 'out');
const dependencies = deps
  .filter(r => ['depends-on', 'imports', 'uses'].includes(r.type))
  .map(r => yata.getEntity(r.targetId));
```

#### エンティティを探す（find_entity）

| 自然言語クエリ | 等価なAPIコマンド |
|--------------|------------------|
| `UserServiceを探して` | `yata.search('UserService')` |
| `Find UserService` | `yata.getEntityByName('UserService')` |
| `ConfigManagerはどこにありますか？` | `yata.query({ textSearch: 'ConfigManager' })` |
| `Where is ConfigManager defined?` | `yata.search('ConfigManager', 10)` |

```typescript
// 自然言語
const result = await yata.ask('UserServiceを探して');

// 等価なAPI呼び出し
const entities = await yata.search('UserService', 10);
// または
const entity = await yata.getEntityByName('UserService');
```

#### 名前空間で探す（find_by_namespace）

| 自然言語クエリ | 等価なAPIコマンド |
|--------------|------------------|
| `app.servicesの全てのクラス` | `yata.query({ entityFilters: { namespaces: ['app.services'], types: ['class'] } })` |
| `Classes in app.services` | `yata.getEntitiesByNamespace('app.services')` |
| `utilsネームスペースの関数一覧` | `yata.query({ entityFilters: { namespaces: ['utils'], types: ['function'] } })` |

```typescript
// 自然言語
const result = await yata.ask('app.servicesの全てのクラス');

// 等価なAPI呼び出し
const queryResult = await yata.query({
  entityFilters: {
    namespaces: ['app.services'],
    types: ['class'],
  },
});
```

#### 関連エンティティを探す（find_related）

| 自然言語クエリ | 等価なAPIコマンド |
|--------------|------------------|
| `UserServiceに関連するもの` | `yata.getNeighbors(userServiceId, { direction: 'both' })` |
| `Related to UserService` | `yata.extractSubgraph(userServiceId, { depth: 1 })` |

```typescript
// 自然言語
const result = await yata.ask('UserServiceに関連するもの');

// 等価なAPI呼び出し
const entity = await yata.getEntityByName('UserService');
const neighbors = await yata.getNeighbors(entity.id, { direction: 'both' });
```

#### 関係性の説明（explain_relationship）

| 自然言語クエリ | 等価なAPIコマンド |
|--------------|------------------|
| `UserServiceとRepositoryの関係は？` | `yata.findPath(userServiceId, repositoryId)` |
| `How is A related to B?` | `yata.findPath(aId, bId, { direction: 'both' })` |

```typescript
// 自然言語
const result = await yata.ask('UserServiceとRepositoryの関係は？');

// 等価なAPI呼び出し
const entityA = await yata.getEntityByName('UserService');
const entityB = await yata.getEntityByName('Repository');
const path = await yata.findPath(entityA.id, entityB.id, {
  maxDepth: 5,
  direction: 'both',
});
```

### 高度な使い方

```typescript
// 設定オプション付きのクエリ
const result = await yata.ask('UserServiceの依存関係', {
  language: 'ja',              // 言語を明示指定
  fuzzyMatching: true,         // ファジーマッチング有効
  minConfidence: 0.7,          // 最小信頼度
  maxResults: 50,              // 最大結果数
  includeInferred: true,       // 推論結果を含む
});

// 結果の詳細
console.log('Query:', result.parsedQuery.originalQuery);
console.log('Intent:', result.parsedQuery.intent);
console.log('Subject:', result.parsedQuery.subject);
console.log('Confidence:', result.parsedQuery.confidence);
console.log('Entities:', result.entities.length);
console.log('Execution time:', result.executionTimeMs, 'ms');
```

### MCP ツールとの連携

MCPサーバーを通じて自然言語クエリを使用することもできます：

```json
// MCP経由でのクエリ（sdd_ask_knowledge ツール）
// 入力：
{
  "question": "UserServiceを呼び出している関数は？",
  "maxResults": 20
}
```

### 対応インテント一覧

| インテント | 説明 | 自然言語例 | 内部API |
|-----------|------|-----------|---------|
| `find_entity` | エンティティ検索 | 「UserServiceを探して」 | `search()`, `getEntityByName()` |
| `find_callers` | 呼び出し元検索 | 「〜を呼び出している関数」 | `getRelationships(id, 'in')` |
| `find_callees` | 呼び出し先検索 | 「〜は何を呼び出していますか」 | `getRelationships(id, 'out')` |
| `find_implementations` | 実装検索 | 「〜の実装を表示」 | `getRelationships(id, 'in', {types: ['implements']})` |
| `find_dependencies` | 依存関係検索 | 「〜の依存関係」 | `traverse(id, ['depends-on'], 'forward')` |
| `find_dependents` | 依存元検索 | 「〜に依存しているもの」 | `traverse(id, ['depends-on'], 'backward')` |
| `find_related` | 関連検索 | 「〜に関連するもの」 | `getNeighbors(id, {direction: 'both'})` |
| `find_by_type` | 型別検索 | 「すべてのクラス」 | `query({entityFilters: {types: [...]}})` |
| `find_by_namespace` | 名前空間検索 | 「app.services内のクラス」 | `query({entityFilters: {namespaces: [...]}})` |
| `explain_relationship` | 関係性の説明 | 「〜と〜の関係は？」 | `findPath(idA, idB)` |
| `general_search` | 一般検索 | パターン未マッチ時 | `search(keywords)` |

---

## 🧠 推論エンジン

### 推論の実行

```typescript
// 推論ルールを適用
const inferenceResult = await yata.infer({
  rules: ['transitivity', 'type-compatibility'],
  maxIterations: 100,
});

console.log(`Inferred ${inferenceResult.inferredRelationships.length} new relationships`);
```

### カスタム推論ルール

```typescript
// カスタムルールの追加
yata.addInferenceRule({
  id: 'service-uses-repository',
  name: 'Service Uses Repository',
  description: 'Services typically use repositories',
  condition: (source, target) => 
    source.type === 'class' && 
    source.name.endsWith('Service') &&
    target.type === 'interface' &&
    target.name.endsWith('Repository'),
  consequent: {
    type: 'uses',
    weight: 0.8,
  },
});
```

### 制約検証

```typescript
// グラフの制約を検証
const validation = await yata.validate({
  constraints: ['no-circular-dependencies', 'single-inheritance'],
});

if (!validation.isValid) {
  console.log('Violations:', validation.violations);
}
```

### 信頼度計算

```typescript
// 関係性の信頼度を計算
const confidence = await yata.computeConfidence(
  sourceId,
  targetId,
  'depends-on'
);

console.log(`Confidence: ${(confidence * 100).toFixed(1)}%`);
```

### 関係性提案

```typescript
// 関係性の提案を取得
const suggestions = await yata.suggestRelationships(entityId, {
  maxSuggestions: 10,
  minConfidence: 0.7,
});

for (const suggestion of suggestions) {
  console.log(`Suggest: ${suggestion.type} -> ${suggestion.targetId} (${(suggestion.confidence * 100).toFixed(1)}%)`);
  console.log(`  Reason: ${suggestion.reason}`);
}
```

---

## 📤 インポート/エクスポート

### JSON形式

```typescript
// エクスポート
const jsonExport = await yata.exportJson('./backup.json');
console.log(`Exported ${jsonExport.entities.length} entities`);

// インポート
const mergeResult = await yata.importJson('./backup.json', {
  merge: true,   // 既存データとマージ
  dryRun: false, // 実際に適用
});

console.log(`Imported: ${mergeResult.entitiesAdded} added, ${mergeResult.entitiesUpdated} updated`);
```

### RDF形式

```typescript
// RDFエクスポート
const rdfContent = await yata.exportRdf('./knowledge.ttl', {
  format: 'turtle',
  baseUri: 'http://example.org/knowledge/',
});
```

### ユニファイドエクスポート API

```typescript
// 複数フォーマット対応のエクスポート
const exportResult = await yata.export({
  format: 'json',  // 'json' | 'rdf' | 'graphml'
  namespace: 'app.services',  // フィルタ
  outputPath: './export/services.json',
});

// 増分エクスポート（変更分のみ）
const incrementalExport = await yata.exportIncremental(
  new Date('2024-01-01'),  // この日時以降の変更
  { format: 'json' }
);
```

### デルタ計算と適用

```typescript
// 2つの状態間のデルタを計算
const oldState = await yata.exportJson();
// ... 変更操作 ...
const newState = await yata.exportJson();

const delta = yata.computeDelta(oldState, newState);
console.log(`Delta: +${delta.added.length}, ~${delta.updated.length}, -${delta.deleted.length}`);

// デルタを別のインスタンスに適用
await otherYata.applyDelta(delta, { dryRun: false });
```

---

## 📊 統計情報

```typescript
const stats = await yata.getStats();

console.log('Graph Statistics:');
console.log(`  Total entities: ${stats.totalEntities}`);
console.log(`  Total relationships: ${stats.totalRelationships}`);
console.log(`  Entities by type:`, stats.entitiesByType);
console.log(`  Relationships by type:`, stats.relationshipsByType);
```

---

## 🔄 KGPR (Knowledge Graph Pull Request)

KGPRは、ローカル知識グラフの変更をYATA Globalに共有するためのワークフローです。

### KGPR マネージャーの作成

```typescript
import { createLocalKGPRManager } from '@nahisaho/yata-local';

const kgprManager = createLocalKGPRManager(yata.getDb());
```

### KGPR の作成

```typescript
const kgpr = await kgprManager.createKGPR({
  title: 'UserService パターンの共有',
  description: 'ユーザー認証フローから学習したパターン',
  namespace: 'app.services',
  entityTypes: ['class', 'interface'],
  privacyLevel: 'strict',  // 'strict' | 'moderate' | 'none'
  author: 'developer@example.com',
});

console.log('KGPR created:', kgpr.id);
// => KGPR created: KGPR-1704067200000-a1b2c3d4
```

### プライバシーレベル

| レベル | 説明 |
|--------|------|
| `strict` | ファイルパス、行番号、機密メタデータを除去 |
| `moderate` | ファイルパスを相対化、機密メタデータを除去 |
| `none` | フィルタリングなし |

### KGPR の操作

```typescript
// 差分プレビュー
const diff = await kgprManager.previewDiff(kgpr.id);
console.log(`Changes: +${diff.stats.entitiesAdded}, ~${diff.stats.entitiesUpdated}`);

// KGPR一覧
const kgprs = await kgprManager.listKGPRs({
  status: 'draft',
  namespace: 'app.services',
  limit: 10,
});

// ステータス更新
await kgprManager.updateKGPRStatus(kgpr.id, 'submitted');
```

---

## 🌙 Wake-Sleep 学習

Wake-Sleepは、コードからパターンを学習し統合する継続的学習サイクルです。

### Wake-Sleep サイクルの作成

```typescript
import { createLocalWakeSleepCycle } from '@nahisaho/yata-local';

const wakeSleep = createLocalWakeSleepCycle(yata.getDb(), {
  wakeObserveLimit: 1000,
  sleepMinClusterSize: 3,
  sleepSimilarityThreshold: 0.7,
  compressMinOccurrences: 5,
});
```

### 学習サイクルの実行

```typescript
// Wakeフェーズ: コードを観察しパターンを抽出
const wakeResult = await wakeSleep.wake({
  namespace: 'app.services',
  entityTypes: ['class', 'function'],
});
console.log(`Wake: Found ${wakeResult.patterns.length} patterns`);

// Sleepフェーズ: パターンを統合・圧縮
const sleepResult = await wakeSleep.sleep();
console.log(`Sleep: Consolidated ${sleepResult.consolidatedPatterns.length} patterns`);

// 完全サイクル
const cycleResult = await wakeSleep.runCycle({
  namespace: 'app',
});
console.log(`Cycle complete: ${cycleResult.status}`);
```

---

## 📈 インデックス最適化

```typescript
import { IndexOptimizer } from '@nahisaho/yata-local';

const optimizer = new IndexOptimizer(yata.getDb());

// 現在のインデックス分析
const analysis = await optimizer.analyze({
  includeQueryStats: true,
  recommendationLimit: 10,
});

console.log('Current indexes:', analysis.existingIndexes);
console.log('Recommendations:', analysis.recommendations);

// 推奨インデックスの作成
for (const rec of analysis.recommendations) {
  if (rec.priority === 'high') {
    await optimizer.createIndex(rec);
  }
}
```

---

## 🌐 グローバル同期

```typescript
import { createGlobalSyncManager } from '@nahisaho/yata-local';

const syncManager = createGlobalSyncManager(yata.getDb(), {
  serverUrl: 'http://localhost:3000',
  autoSync: true,
  syncInterval: 60000,  // 1分ごと
});

// 手動同期
const syncResult = await syncManager.sync();
console.log(`Synced: ${syncResult.pushed} pushed, ${syncResult.pulled} pulled`);

// 同期状態の確認
const status = syncManager.getStatus();
console.log('Last sync:', status.lastSyncAt);
```

---

## 🛠️ コード解析との統合

### KnowledgeGraphUpdater

```typescript
import { createKnowledgeGraphUpdater } from '@nahisaho/yata-local';

const updater = createKnowledgeGraphUpdater(yata);

// コード解析結果を知識グラフに反映
const updateResult = await updater.updateFromAnalysis({
  entities: [
    {
      type: 'class',
      name: 'OrderService',
      namespace: 'app.services',
      filePath: 'src/services/order.ts',
      methods: ['createOrder', 'cancelOrder'],
    },
  ],
  relationships: [
    {
      sourceType: 'class',
      sourceName: 'OrderService',
      targetType: 'interface',
      targetName: 'IOrderRepository',
      type: 'uses',
    },
  ],
});

console.log(`Updated: ${updateResult.entitiesCreated} entities, ${updateResult.relationshipsCreated} relationships`);
```

### YATA Bridge (MCP統合)

```typescript
import { createYataBridge } from '@nahisaho/yata-local';

const bridge = createYataBridge({
  yataLocal: yata,
  namespace: 'project.name',
});

// MCPツールからの呼び出しを処理
const entities = await bridge.queryEntities({
  types: ['class'],
  namePattern: '.*Service',
});
```

---

## 🔧 高度な使用例

### 生SQLクエリ

```typescript
// 高度なユースケース向けの生SQLクエリ
const results = await yata.rawQuery<{ name: string; count: number }>(
  `SELECT type as name, COUNT(*) as count 
   FROM entities 
   GROUP BY type 
   ORDER BY count DESC`,
  []
);
```

### 変更追跡

```typescript
// 特定時刻以降の変更を取得
const changes = await yata.getChangesSince(new Date('2024-01-01'));

console.log('Added entities:', changes.entities.added.length);
console.log('Updated entities:', changes.entities.updated.length);
console.log('Deleted entities:', changes.entities.deleted.length);
```

---

## 📚 関連ドキュメント

- [YATA Global ユーザーガイド](./YATA-GLOBAL-GUIDE.ja.md)
- [API リファレンス](./API-REFERENCE.md)
- [MUSUBIX ユーザーガイド](./USER-GUIDE.ja.md)

---

## 📝 バージョン履歴

| バージョン | 主な変更 |
|-----------|---------|
| v1.7.0 | インデックス最適化、グローバル同期、エクスポートAPI強化 |
| v1.6.5 | KGPR、Wake-Sleep学習モジュール追加 |
| v1.5.0 | 推論エンジン強化、パターンマッチング |
| v1.0.0 | 初期リリース |

---

**最終更新**: 2026-01-11
**パッケージ**: `@nahisaho/yata-local`
