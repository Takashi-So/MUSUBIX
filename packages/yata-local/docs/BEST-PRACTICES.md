# YATA Local ベストプラクティス

## EntityType の使用ガイドライン

YATA LocalのEntityTypeは、コード解析に最適化された固定の16種類です。
SDDワークフローの成果物（要件、設計、タスク等）を格納する場合は、以下のパターンを推奨します。

### EntityType一覧

```typescript
type EntityType = 
  | 'class'      // クラス
  | 'interface'  // インターフェース
  | 'function'   // 関数（タスク、エクスポート関数）
  | 'method'     // メソッド
  | 'variable'   // 変数
  | 'constant'   // 定数
  | 'type'       // 型（要件、型エクスポート）
  | 'enum'       // 列挙型
  | 'module'     // モジュール（ドキュメント）
  | 'package'    // パッケージ
  | 'file'       // ファイル（ソースコード）
  | 'parameter'  // パラメータ
  | 'property'   // プロパティ
  | 'import'     // インポート
  | 'export'     // エクスポート
  | 'unknown';   // 不明・カスタム
```

### SDD成果物のマッピング推奨

| SDD成果物 | 推奨EntityType | metadata.entityKind |
|-----------|---------------|---------------------|
| 要件定義書 | `module` | `RequirementsDocument` |
| 設計書 | `module` | `DesignDocument` |
| タスク分解書 | `module` | `TaskDocument` |
| 個別要件 | `type` | `Requirement` |
| 設計コンポーネント | `class` | `Component` |
| 実装タスク | `function` | `Task` |
| ソースファイル | `file` | `SourceFile` |
| 型エクスポート | `type` | `type` |
| 関数エクスポート | `function` | `function` |
| 定数エクスポート | `constant` | `const` |

### コード例

```typescript
import { createYataLocal } from '@nahisaho/yata-local';

const yata = createYataLocal({ path: './.yata-local.db' });
await yata.open();

// 要件ドキュメントの登録
const docId = await yata.addEntity({
  name: 'REQ-PM-001',
  type: 'module',  // ドキュメントはmodule
  namespace: 'project-management',
  metadata: {
    entityKind: 'RequirementsDocument',  // 詳細種類をmetadataに
    filePath: 'requirements/REQ-PM-001.md',
    validatedAt: new Date().toISOString(),
  },
});

// 個別要件の登録
const reqId = await yata.addEntity({
  name: 'REQ-PM-PRJ-001',
  type: 'type',  // 要件はtype
  namespace: 'project-management',
  metadata: {
    entityKind: 'Requirement',
    earsPattern: 'ubiquitous',
    text: 'THE system SHALL...',
    parentDocument: 'REQ-PM-001',
  },
});

// 要件とドキュメントの関連付け
await yata.addRelationship(reqId, docId, 'contains', {
  relationKind: 'BELONGS_TO',
});

// entityKindでクエリ
const requirements = await yata.getEntitiesByKind('Requirement');
console.log(`Found ${requirements.length} requirements`);

// upsertで重複を防止
const { id, created } = await yata.upsertEntity({
  name: 'REQ-PM-PRJ-001',
  type: 'type',
  namespace: 'project-management',
  metadata: { entityKind: 'Requirement', text: 'Updated text...' },
});
console.log(created ? 'Created new' : 'Updated existing');
```

### 高レベルAPI（v0.1.1+）

```typescript
// タイプでフィルタ
const modules = await yata.getEntitiesByType('module');

// Namespaceでフィルタ
const projectEntities = await yata.getEntitiesByNamespace('project-management');

// entityKindでフィルタ（metadata内）
const tasks = await yata.getEntitiesByKind('Task');

// 名前で検索
const entity = await yata.getEntityByName('REQ-PM-001', 'project-management');

// Upsert（追加または更新）
const result = await yata.upsertEntity(entityData, 'name-namespace');

// Raw SQLクエリ
const custom = await yata.rawQuery<{ count: number }>(
  'SELECT COUNT(*) as count FROM entities WHERE type = ?',
  ['function']
);
```

### RelationType一覧

```typescript
type RelationType =
  | 'calls'       // 呼び出し
  | 'imports'     // インポート
  | 'exports'     // エクスポート
  | 'extends'     // 継承（クラス）
  | 'inherits'    // 継承（インターフェース）
  | 'implements'  // 実装
  | 'contains'    // 包含（推奨：ドキュメント→要件）
  | 'uses'        // 使用
  | 'defines'     // 定義
  | 'references'  // 参照
  | 'depends-on'  // 依存
  | 'tested-by'   // テスト
  | 'documents'   // 文書化
  | 'overrides'   // オーバーライド
  | 'returns'     // 戻り値
  | 'accepts';    // 引数
```

### SDD成果物の関連付け推奨

| 関連 | 推奨RelationType | metadata.relationKind |
|------|-----------------|----------------------|
| 要件 → ドキュメント | `contains` | `BELONGS_TO` |
| コンポーネント → 設計書 | `contains` | `DEFINED_IN` |
| タスク → タスク分解書 | `contains` | `DEFINED_IN` |
| コード → タスク | `implements` | `IMPLEMENTS_TASK` |
| テスト → コード | `tested-by` | `TESTS` |
