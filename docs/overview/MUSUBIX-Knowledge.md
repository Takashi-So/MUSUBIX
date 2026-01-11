# MUSUBIX Knowledge パッケージ

**パッケージ名**: `@musubix/knowledge`  
**バージョン**: 3.0.1  
**最終更新**: 2026-01-12

---

## 1. 概要

`@musubix/knowledge` は、MUSUBIX v3.0で導入されたGit-Native知識グラフシステムです。**会社・開発グループで共有すべき知識**（ベストプラクティス、技術選定基準、ドメイン知識、コーディング規約など）をJSONファイルで管理し、Gitワークフローにネイティブに統合されます。

> **📌 重要**: 個別プロジェクトの要件（REQ-*）、設計（DES-*）、タスク（TSK-*）は `storage/specs/` ディレクトリで管理されます。`@musubix/knowledge` はプロジェクト横断で共有すべき**組織知識**のためのパッケージです。

### 1.1 MUSUBIXにおける役割分担

| 対象 | 保存場所 | 用途 |
|------|---------|------|
| **プロジェクト固有** | `storage/specs/` | 要件(REQ-*)、設計(DES-*)、タスク(TSK-*) |
| **組織共有知識** | `.knowledge/` | ベストプラクティス、技術基準、ドメイン知識 |

### 1.2 適切な使用例

| ✅ 適切 | ❌ 不適切 |
|--------|----------|
| 「React vs Vue の選定基準」 | 「REQ-001: ユーザー認証」 |
| 「API設計のベストプラクティス」 | 「DES-001: JWT認証設計」 |
| 「ECサイトのドメイン用語集」 | 「TSK-001: AuthService実装」 |
| 「セキュリティコーディング規約」 | 個別プロジェクトの実装詳細 |
| 「パフォーマンス最適化パターン」 | 特定機能の仕様書 |

### 1.3 特徴

| 特徴 | 説明 |
|------|------|
| **サーバーレス** | データベース不要、JSONファイルで完結 |
| **Git-friendly** | diff/merge/PR対応、バージョン管理可能 |
| **軽量** | ゼロ依存（外部ライブラリ不要） |
| **階層型ID** | `pattern:BP-CODE-001`、`guideline:SEC-001` |
| **型安全** | TypeScriptによる完全な型定義 |

### 1.4 ストレージ構造

```
.knowledge/
└── graph.json      # 組織共有知識のエンティティ・リレーション
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

#### ベストプラクティスの登録

```typescript
// コーディングパターン
await store.putEntity({
  id: 'pattern:BP-CODE-001',
  type: 'best-practice',
  name: 'Entity Input DTO',
  description: 'エンティティ作成時はInput DTOオブジェクトを使用する',
  properties: {
    category: 'code',
    confidence: 0.95,
    example: `
interface CreateUserInput {
  name: string;
  email: string;
}
function createUser(input: CreateUserInput): User { ... }
    `,
    rationale: '引数が増えても呼び出し側の変更が最小限で済む',
  },
  tags: ['typescript', 'design-pattern', 'dto'],
});

// 設計パターン
await store.putEntity({
  id: 'pattern:BP-DESIGN-001',
  type: 'best-practice',
  name: 'Status Transition Map',
  description: '有効なステータス遷移をMapで定義する',
  properties: {
    category: 'design',
    confidence: 0.95,
    example: `
const validTransitions: Record<Status, Status[]> = {
  draft: ['active', 'cancelled'],
  active: ['completed', 'cancelled'],
  completed: [],
  cancelled: [],
};
    `,
  },
  tags: ['state-machine', 'design-pattern'],
});
```

#### 技術選定基準の登録

```typescript
await store.putEntity({
  id: 'guideline:TECH-001',
  type: 'tech-guideline',
  name: 'フロントエンドフレームワーク選定基準',
  description: 'フロントエンドフレームワーク選定の判断基準',
  properties: {
    criteria: [
      { name: 'チームスキル', weight: 0.3 },
      { name: 'エコシステム成熟度', weight: 0.25 },
      { name: 'パフォーマンス', weight: 0.2 },
      { name: '学習コスト', weight: 0.15 },
      { name: 'コミュニティサポート', weight: 0.1 },
    ],
    recommendations: {
      'enterprise': 'React + TypeScript',
      'rapid-prototype': 'Vue.js',
      'performance-critical': 'Svelte',
    },
  },
  tags: ['frontend', 'tech-selection', 'framework'],
});
```

#### ドメイン知識の登録

```typescript
// ECサイトのドメイン用語
await store.putEntity({
  id: 'domain:EC-TERM-001',
  type: 'domain-term',
  name: 'SKU (Stock Keeping Unit)',
  description: '在庫管理単位。商品の色・サイズなどの組み合わせごとに付与される一意のコード',
  properties: {
    domain: 'e-commerce',
    examples: ['SHIRT-RED-M', 'SHIRT-RED-L', 'SHIRT-BLUE-M'],
    relatedTerms: ['JAN', 'UPC', '商品コード'],
  },
  tags: ['e-commerce', 'inventory', 'terminology'],
});

// ビジネスルール
await store.putEntity({
  id: 'domain:EC-RULE-001',
  type: 'business-rule',
  name: '在庫引当ルール',
  description: '注文確定時の在庫引当に関するビジネスルール',
  properties: {
    domain: 'e-commerce',
    rules: [
      '在庫は注文確定時に即座に引き当てる',
      '30分以内に決済完了しない場合は引当解除',
      '複数倉庫の場合は最寄り倉庫から優先',
    ],
  },
  tags: ['e-commerce', 'inventory', 'business-rule'],
});
```

#### セキュリティガイドラインの登録

```typescript
await store.putEntity({
  id: 'guideline:SEC-001',
  type: 'security-guideline',
  name: 'パスワードハッシュ化ガイドライン',
  description: 'パスワード保存時のハッシュ化に関するガイドライン',
  properties: {
    algorithm: 'bcrypt',
    minCost: 12,
    prohibited: ['MD5', 'SHA1', 'SHA256（単独使用）'],
    example: `
import bcrypt from 'bcrypt';
const hash = await bcrypt.hash(password, 12);
    `,
  },
  tags: ['security', 'authentication', 'password'],
});
```

### 3.3 エンティティの取得

```typescript
const pattern = await store.getEntity('pattern:BP-CODE-001');

if (pattern) {
  console.log(pattern.name);        // => 'Entity Input DTO'
  console.log(pattern.type);        // => 'best-practice'
  console.log(pattern.properties);  // => { category: 'code', confidence: 0.95, ... }
}
```

### 3.4 エンティティの削除

```typescript
const deleted = await store.deleteEntity('pattern:BP-CODE-001');
console.log(deleted); // => true
```

---

## 4. リレーション管理

### 4.1 リレーションの追加

```typescript
// パターン間の関連
await store.addRelation({
  source: 'pattern:BP-CODE-001',
  target: 'pattern:BP-TEST-004',
  type: 'relatedTo',
  properties: {
    description: 'Input DTOパターンを使う場合のテストパターン',
  },
});

// ガイドライン → パターン の参照関係
await store.addRelation({
  source: 'guideline:SEC-001',
  target: 'pattern:BP-CODE-005',
  type: 'references',
  properties: {
    context: 'セキュリティガイドラインでResult型の使用を推奨',
  },
});

// ドメイン用語間の関連
await store.addRelation({
  source: 'domain:EC-TERM-001',
  target: 'domain:EC-RULE-001',
  type: 'usedIn',
});
```

### 4.2 リレーションの取得

```typescript
// 出ていくリレーション
const outgoing = await store.getRelationsFrom('guideline:SEC-001');

// 入ってくるリレーション
const incoming = await store.getRelationsTo('pattern:BP-CODE-005');
```

### 4.3 リレーションの削除

```typescript
await store.removeRelation(
  'pattern:BP-CODE-001',
  'pattern:BP-TEST-004',
  'relatedTo'
);
```

---

## 5. グラフクエリ

### 5.1 タイプでフィルタリング

```typescript
// すべてのベストプラクティスを取得
const patterns = await store.query({ type: 'best-practice' });

// すべてのドメイン用語を取得
const terms = await store.query({ type: 'domain-term' });

// すべてのガイドラインを取得
const guidelines = await store.query({ type: 'security-guideline' });
```

### 5.2 タグでフィルタリング

```typescript
// TypeScript関連のパターン
const tsPatterns = await store.query({ 
  tags: ['typescript'] 
});

// セキュリティ関連すべて
const securityKnowledge = await store.query({ 
  tags: ['security'] 
});

// ECサイトドメインの知識
const ecKnowledge = await store.query({ 
  tags: ['e-commerce'] 
});
```

### 5.3 複合クエリ

```typescript
// コード系のベストプラクティスのみ
const codePatterns = await store.query({
  type: 'best-practice',
  tags: ['design-pattern'],
});
```

---

## 6. グラフ走査

### 6.1 関連知識の探索

```typescript
// セキュリティガイドラインから関連パターンを探索
const related = await store.traverse('guideline:SEC-001', {
  direction: 'outgoing',
  relationTypes: ['references', 'relatedTo'],
  maxDepth: 2,
});

for (const entity of related) {
  console.log(`${entity.type}: ${entity.name}`);
}
```

### 6.2 サブグラフの取得

```typescript
// 特定知識を中心としたサブグラフ
const subgraph = await store.getSubgraph('domain:EC-TERM-001', {
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
    "pattern:BP-CODE-001": {
      "id": "pattern:BP-CODE-001",
      "type": "best-practice",
      "name": "Entity Input DTO",
      "description": "エンティティ作成時はInput DTOオブジェクトを使用する",
      "properties": {
        "category": "code",
        "confidence": 0.95,
        "example": "..."
      },
      "tags": ["typescript", "design-pattern", "dto"],
      "createdAt": "2026-01-12T00:00:00.000Z",
      "updatedAt": "2026-01-12T00:00:00.000Z"
    }
  },
  "relations": [
    {
      "source": "pattern:BP-CODE-001",
      "target": "pattern:BP-TEST-004",
      "type": "relatedTo",
      "properties": { "description": "..." }
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
  id: string;              // 例: 'pattern:BP-CODE-001'
  type: string;            // 例: 'best-practice', 'domain-term', 'guideline'
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

### 9.1 組織のベストプラクティス管理

```typescript
import { createKnowledgeStore } from '@musubix/knowledge';

const store = createKnowledgeStore('.knowledge');
await store.load();

// プロジェクトから学習したパターンを登録
await store.putEntity({
  id: 'pattern:BP-CODE-010',
  type: 'best-practice',
  name: 'Optimistic Locking',
  description: '同時編集検出のためのversion管理パターン',
  properties: {
    category: 'design',
    confidence: 0.90,
    learnedFrom: 'Project-14',
    example: `
interface Entity {
  id: string;
  version: number;
  // ...
}

function update(entity: Entity, currentVersion: number): Result<Entity, ConcurrencyError> {
  if (entity.version !== currentVersion) {
    return err(new ConcurrencyError('Entity was modified'));
  }
  return ok({ ...entity, version: entity.version + 1 });
}
    `,
  },
  tags: ['concurrency', 'design-pattern', 'database'],
});

await store.save();
```

### 9.2 ドメイン知識の蓄積

```typescript
// 医療系ドメインの用語集を構築
const medicalTerms = [
  {
    id: 'domain:MED-TERM-001',
    type: 'domain-term',
    name: 'SOAP記録',
    description: '医療記録の標準形式（Subjective, Objective, Assessment, Plan）',
    properties: {
      domain: 'healthcare',
      components: {
        S: '主観的情報（患者の訴え）',
        O: '客観的情報（検査結果など）',
        A: '評価・診断',
        P: '治療計画',
      },
    },
    tags: ['healthcare', 'documentation', 'terminology'],
  },
  // ... more terms
];

for (const term of medicalTerms) {
  await store.putEntity(term);
}

await store.save();
```

### 9.3 技術選定の知識ベース

```typescript
// 新規プロジェクトでの技術選定時に参照
async function getTechRecommendation(criteria: {
  projectType: string;
  teamSize: number;
  priority: 'speed' | 'quality' | 'maintainability';
}) {
  const guidelines = await store.query({ type: 'tech-guideline' });
  
  // criteria に基づいてフィルタリング・ランキング
  const relevant = guidelines.filter(g => 
    g.tags?.includes(criteria.projectType)
  );
  
  return relevant;
}
```

---

## 10. 自然言語での利用（MCP / AI Agent）

`@musubix/knowledge` は、MCP（Model Context Protocol）サーバー経由でAIエージェント（GitHub Copilot、Claude、ChatGPT等）から自然言語で操作できます。

### 10.1 MCP設定

Claude Desktop または VS Code に以下の設定を追加:

```json
{
  "mcpServers": {
    "musubix": {
      "command": "npx",
      "args": ["@nahisaho/musubix-mcp-server"]
    }
  }
}
```

### 10.2 自然言語での操作例

#### ベストプラクティスの登録

```
「Optimistic Locking」というパターンを知識ベースに登録して。
同時編集検出のためのversion管理パターンで、信頼度は90%、
タグはconcurrency, design-pattern, databaseで。
```

AIエージェントが `knowledge_put_entity` ツールを呼び出します。

#### 知識の検索

```
TypeScript関連のベストプラクティスを全部見せて
```

AIエージェントが `knowledge_query` ツールを呼び出し、`tags: ['typescript']` でフィルタリングします。

#### ドメイン知識の参照

```
ECサイトの在庫管理に関するドメイン知識を教えて
```

AIエージェントが `knowledge_query` ツールを呼び出し、ECサイト関連の知識を検索します。

#### 関連知識の探索

```
セキュリティガイドラインに関連するパターンは何がある？
```

AIエージェントが `knowledge_traverse` ツールを呼び出し、関連するエンティティを探索します。

### 10.3 MCPツール一覧

| ツール名 | 説明 | 自然言語例 |
|---------|------|-----------|
| `knowledge_put_entity` | 知識の登録/更新 | 「〜を知識ベースに登録して」 |
| `knowledge_get_entity` | 知識の取得 | 「BP-CODE-001の詳細を見せて」 |
| `knowledge_delete_entity` | 知識の削除 | 「古いパターンを削除して」 |
| `knowledge_add_relation` | 関連付け追加 | 「このパターンとあのガイドラインを関連付けて」 |
| `knowledge_query` | 検索 | 「セキュリティ関連の知識一覧」 |
| `knowledge_traverse` | 関連探索 | 「〜に関連する知識は？」 |

### 10.4 実践的な会話例

#### シナリオ: プロジェクトで学んだパターンの組織知識化

```
👤 ユーザー:
Project-14で使った「Status Transition Map」パターンを
組織の知識ベースに登録しておきたい。
有効なステータス遷移をMapで定義するパターンで、
信頼度95%、タグはstate-machine, design-patternで。

🤖 AIエージェント:
ベストプラクティスとして登録しました:
- ID: pattern:BP-DESIGN-001
- 名前: Status Transition Map
- カテゴリ: design
- 信頼度: 95%
- タグ: state-machine, design-pattern

👤 ユーザー:
このパターンのコード例も追加して

🤖 AIエージェント:
コード例を追加しました:
```typescript
const validTransitions: Record<Status, Status[]> = {
  draft: ['active', 'cancelled'],
  active: ['completed', 'cancelled'],
  completed: [],
  cancelled: [],
};
```

👤 ユーザー:
設計系のベストプラクティスを全部見せて

🤖 AIエージェント:
設計系ベストプラクティス:
1. pattern:BP-DESIGN-001 - Status Transition Map (95%)
2. pattern:BP-DESIGN-002 - Repository Async Pattern (85%)
3. pattern:BP-DESIGN-003 - Service Layer with DI (90%)

👤 ユーザー:
新人向けにセキュリティガイドラインと関連パターンをまとめて教えて

🤖 AIエージェント:
セキュリティ関連の組織知識:

**ガイドライン:**
- guideline:SEC-001 - パスワードハッシュ化ガイドライン
- guideline:SEC-002 - API認証ガイドライン

**関連パターン:**
- pattern:BP-CODE-005 - Result Type（エラーハンドリング）
- pattern:BP-DESIGN-005 - AuditService（監査ログ）

これらは新人オンボーディングで重点的に学習することを推奨します。
```

### 10.5 GitHub Copilot / Claude Code での利用

MCPを設定しなくても、AGENTS.md や Claude Code Skills 経由で利用可能:

```
👤 ユーザー:
@musubix/knowledge を使って、うちのチームの
コーディング規約とベストプラクティスを管理するコードを書いて

🤖 AIエージェント:
// AGENTS.md / Skills から学習した知識に基づいてコード生成
import { createKnowledgeStore } from '@musubix/knowledge';

const store = createKnowledgeStore('.knowledge');
// チームの知識を登録・管理...
```

---

## 11. 個別プロジェクトの要件・設計管理について

個別プロジェクトの要件（REQ-*）、設計（DES-*）、タスク（TSK-*）は `@musubix/knowledge` ではなく、以下の仕組みで管理します:

### 11.1 storage/specs/ ディレクトリ

```
storage/
└── specs/
    ├── REQ-001.md      # 要件ドキュメント（EARS形式）
    ├── DES-001.md      # 設計ドキュメント（C4モデル）
    └── TSK-001.md      # タスクドキュメント
```

### 11.2 MUSUBIX CLIでの操作

```bash
# 要件の作成・検証
npx musubix requirements analyze requirements.txt
npx musubix requirements validate storage/specs/REQ-001.md

# 設計の生成
npx musubix design generate storage/specs/REQ-001.md

# トレーサビリティマトリクス
npx musubix trace matrix
```

### 11.3 MCP SDDツールでの操作

| ツール名 | 説明 |
|---------|------|
| `sdd_create_requirements` | 要件ドキュメント作成 |
| `sdd_validate_requirements` | 要件の検証 |
| `sdd_create_design` | 設計ドキュメント作成 |
| `sdd_create_tasks` | タスク生成 |

---

## 12. 関連パッケージ

| パッケージ | 説明 |
|------------|------|
| `@musubix/policy` | 9憲法条項に基づくポリシー検証 |
| `@musubix/decisions` | Architecture Decision Records管理 |
| `musubix` | 3パッケージを含むメインパッケージ |

---

## 13. 参照

- [MUSUBIX v3.0 User Guide](../MUSUBIX-v3.0-User-Guide.md)
- [Migration Guide from YATA](../MIGRATION-v3.0.md)
- [GitHub Repository](https://github.com/nahisaho/MUSUBIX)
- [npm Package](https://www.npmjs.com/package/@musubix/knowledge)
