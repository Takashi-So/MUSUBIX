# MUSUBIX v3.0 Git-Native Knowledge System ユーザーガイド

> 完全ガイド: @musubix/knowledge, @musubix/policy, @musubix/decisions

| 項目 | 内容 |
|------|------|
| **バージョン** | 3.0.0 |
| **最終更新** | 2026-01-12 |
| **前提条件** | Node.js >= 20.0.0, TypeScript >= 5.0 |

---

## 目次

1. [はじめに](#はじめに)
2. [インストール](#インストール)
3. [@musubix/knowledge - 知識グラフストア](#musubixknowledge---知識グラフストア)
4. [@musubix/policy - ポリシーエンジン](#musubixpolicy---ポリシーエンジン)
5. [@musubix/decisions - ADRマネージャー](#musubixdecisions---adrマネージャー)
6. [統合ユースケース](#統合ユースケース)
7. [CLI統合](#cli統合)
8. [トラブルシューティング](#トラブルシューティング)

---

## はじめに

MUSUBIX v3.0では、従来のYATA（Yet Another Typed Architecture）に代わり、**Git-Native Knowledge System**を導入しました。この新システムは以下の3つのパッケージで構成されています：

| パッケージ | 役割 | ストレージ |
|-----------|------|-----------|
| `@musubix/knowledge` | 知識グラフ（エンティティ・リレーション） | `.knowledge/graph.json` |
| `@musubix/policy` | 9憲法条項の自動検証 | メモリ（設定ファイル任意） |
| `@musubix/decisions` | Architecture Decision Records | `docs/decisions/*.md` |

### 主な特徴

- **サーバーレス**: 外部データベース不要
- **Git-friendly**: JSON/Markdown形式で差分管理が容易
- **軽量**: 外部依存ゼロ
- **型安全**: TypeScriptで完全な型定義

---

## インストール

### 全パッケージ一括インストール（推奨）

```bash
npm install musubix
```

これで `@musubix/knowledge`, `@musubix/policy`, `@musubix/decisions` がすべてインストールされます。

### 個別インストール

```bash
# 知識グラフのみ
npm install @musubix/knowledge

# ポリシーエンジンのみ
npm install @musubix/policy

# ADRマネージャーのみ
npm install @musubix/decisions
```

### インポート方法

```typescript
// musubixパッケージから（推奨）
import { knowledge, policy, decisions } from 'musubix';

const store = knowledge.createKnowledgeStore('.knowledge');
const engine = policy.createPolicyEngine();
const manager = decisions.createDecisionManager('docs/decisions');

// 個別パッケージから
import { createKnowledgeStore } from '@musubix/knowledge';
import { createPolicyEngine } from '@musubix/policy';
import { createDecisionManager } from '@musubix/decisions';
```

---

## @musubix/knowledge - 知識グラフストア

### 概要

要件（REQ）、設計（DES）、タスク（TSK）、コードなどのエンティティとその関係を管理する軽量な知識グラフです。

### ストレージ構造

```
.knowledge/
└── graph.json    # 全エンティティとリレーション
```

### クイックスタート

```typescript
import { createKnowledgeStore } from '@musubix/knowledge';

const store = createKnowledgeStore('.knowledge');

// エンティティを追加
await store.putEntity({
  id: 'REQ-001',
  type: 'requirement',
  name: 'ユーザー認証',
  description: 'ユーザーがログインできること',
  properties: { priority: 'P0', ears: 'THE system SHALL authenticate users' },
  tags: ['security', 'auth'],
});

// 保存（自動的に .knowledge/graph.json に書き込み）
await store.save();
```

### API リファレンス

#### `createKnowledgeStore(basePath: string): KnowledgeStore`

Knowledge Store を作成します。

```typescript
const store = createKnowledgeStore('.knowledge');
```

#### `putEntity(entity: Entity): Promise<void>`

エンティティを作成または更新します。

```typescript
interface Entity {
  id: string;           // 一意のID（例: 'REQ-001', 'DES-001'）
  type: string;         // タイプ（例: 'requirement', 'design', 'task', 'code'）
  name: string;         // 表示名
  description?: string; // 説明
  properties?: Record<string, unknown>; // カスタムプロパティ
  tags?: string[];      // タグ
}

await store.putEntity({
  id: 'DES-001',
  type: 'design',
  name: 'JWT認証設計',
  description: 'JWTトークンを使用した認証フロー',
  properties: {
    pattern: 'Token-Based Authentication',
    components: ['AuthService', 'TokenValidator'],
  },
  tags: ['security', 'jwt'],
});
```

#### `getEntity(id: string): Promise<Entity | undefined>`

IDでエンティティを取得します。

```typescript
const req = await store.getEntity('REQ-001');
if (req) {
  console.log(req.name); // => 'ユーザー認証'
}
```

#### `deleteEntity(id: string): Promise<boolean>`

エンティティを削除します。

```typescript
const deleted = await store.deleteEntity('REQ-999');
console.log(deleted); // => false（存在しない場合）
```

#### `addRelation(relation: Relation): Promise<void>`

エンティティ間のリレーションを追加します。

```typescript
interface Relation {
  id?: string;          // リレーションID（省略可能）
  source: string;       // ソースエンティティID
  target: string;       // ターゲットエンティティID
  type: string;         // リレーションタイプ
  properties?: Record<string, unknown>; // カスタムプロパティ
}

// 設計が要件を実装
await store.addRelation({
  source: 'DES-001',
  target: 'REQ-001',
  type: 'implements',
  properties: { confidence: 0.95 },
});

// タスクが設計を実現
await store.addRelation({
  source: 'TSK-001',
  target: 'DES-001',
  type: 'realizes',
});
```

#### `getRelations(entityId: string): Promise<Relation[]>`

エンティティに関連するすべてのリレーションを取得します。

```typescript
const relations = await store.getRelations('DES-001');
for (const rel of relations) {
  console.log(`${rel.source} --${rel.type}--> ${rel.target}`);
}
```

#### `query(filter: QueryFilter): Promise<Entity[]>`

フィルタ条件でエンティティを検索します。

```typescript
interface QueryFilter {
  type?: string;        // タイプでフィルタ
  tags?: string[];      // タグでフィルタ（AND条件）
  text?: string;        // 名前・説明のテキスト検索
}

// タイプで検索
const requirements = await store.query({ type: 'requirement' });

// タグで検索
const securityItems = await store.query({ tags: ['security'] });

// 複合条件
const securityReqs = await store.query({
  type: 'requirement',
  tags: ['security'],
});

// テキスト検索
const authRelated = await store.query({ text: '認証' });
```

#### `traverse(startId: string, options?: TraverseOptions): Promise<Entity[]>`

グラフを走査して関連エンティティを取得します。

```typescript
interface TraverseOptions {
  direction?: 'outgoing' | 'incoming' | 'both';  // 走査方向
  relationTypes?: string[];  // リレーションタイプでフィルタ
  maxDepth?: number;         // 最大深度（デフォルト: 3）
}

// REQ-001から出ていくリレーションを辿る
const downstream = await store.traverse('REQ-001', {
  direction: 'incoming',  // REQ-001をtargetとするリレーション
  maxDepth: 2,
});

// implementsリレーションのみ
const implementations = await store.traverse('REQ-001', {
  direction: 'incoming',
  relationTypes: ['implements'],
});
```

#### `save(): Promise<void>`

変更を永続化します。

```typescript
await store.save();
// .knowledge/graph.json に保存
```

#### `load(): Promise<void>`

ディスクから読み込みます（通常は自動で呼ばれます）。

```typescript
await store.load();
```

### トレーサビリティの構築

```typescript
// 完全なトレーサビリティチェーン
// REQ → DES → TSK → Code

// 1. 要件
await store.putEntity({
  id: 'REQ-AUTH-001',
  type: 'requirement',
  name: 'ユーザー認証',
  properties: { ears: 'WHEN user submits credentials, THE system SHALL verify and authenticate' },
  tags: ['security'],
});

// 2. 設計
await store.putEntity({
  id: 'DES-AUTH-001',
  type: 'design',
  name: 'JWT認証フロー',
  properties: { pattern: 'Token-Based Auth' },
  tags: ['security'],
});

// 3. タスク
await store.putEntity({
  id: 'TSK-AUTH-001',
  type: 'task',
  name: 'AuthService実装',
  properties: { estimate: '4h' },
  tags: ['implementation'],
});

// 4. コード
await store.putEntity({
  id: 'CODE-AUTH-001',
  type: 'code',
  name: 'AuthService.ts',
  properties: { path: 'src/services/AuthService.ts' },
  tags: ['service'],
});

// リレーション構築
await store.addRelation({ source: 'DES-AUTH-001', target: 'REQ-AUTH-001', type: 'implements' });
await store.addRelation({ source: 'TSK-AUTH-001', target: 'DES-AUTH-001', type: 'realizes' });
await store.addRelation({ source: 'CODE-AUTH-001', target: 'TSK-AUTH-001', type: 'fulfills' });

await store.save();

// トレーサビリティ確認
const chain = await store.traverse('REQ-AUTH-001', {
  direction: 'incoming',
  maxDepth: 10,
});
console.log('トレーサビリティチェーン:', chain.map(e => e.id));
// => ['REQ-AUTH-001', 'DES-AUTH-001', 'TSK-AUTH-001', 'CODE-AUTH-001']
```

---

## @musubix/policy - ポリシーエンジン

### 概要

MUSUBIX 9憲法条項を自動検証するポリシーエンジンです。プロジェクトが憲法に準拠しているかをチェックします。

### 9憲法条項

| ID | 条項 | 検証内容 | 重要度 |
|----|------|----------|--------|
| CONST-001 | Library-First | `packages/` ディレクトリの存在 | error |
| CONST-002 | CLI Interface | `bin/` または package.json の bin フィールド | error |
| CONST-003 | Test-First | テストファイルの存在 | error |
| CONST-004 | EARS Format | 要件ファイルのEARS形式 | error |
| CONST-005 | Traceability | `storage/traceability/` の存在 | error |
| CONST-006 | Project Memory | `steering/` ディレクトリの存在 | warning |
| CONST-007 | Design Patterns | `storage/design/` の存在 | warning |
| CONST-008 | Decision Records | `docs/decisions/` の存在 | warning |
| CONST-009 | Quality Gates | CI設定またはテスト設定の存在 | error |

### クイックスタート

```typescript
import { createPolicyEngine } from '@musubix/policy';

const engine = createPolicyEngine();

// プロジェクト全体を検証
const report = await engine.validateProject('/path/to/project');

console.log('合格:', report.passed);
console.log('違反:', report.violations.length);

for (const v of report.violations) {
  console.log(`[${v.severity}] ${v.policyId}: ${v.message}`);
}
```

### API リファレンス

#### `createPolicyEngine(options?: PolicyEngineOptions): IPolicyEngine`

ポリシーエンジンを作成します。

```typescript
interface PolicyEngineOptions {
  config?: PolicyConfig;
}

interface PolicyConfig {
  enabled?: string[];   // 有効にするポリシーID
  disabled?: string[];  // 無効にするポリシーID
  severity?: Record<string, Severity>; // 重要度のオーバーライド
}

// デフォルト（全憲法条項が有効）
const engine = createPolicyEngine();

// 特定のポリシーを無効化
const engine = createPolicyEngine({
  config: {
    disabled: ['CONST-006', 'CONST-007'],
  },
});
```

#### `listPolicies(category?: PolicyCategory): Policy[]`

登録済みポリシーの一覧を取得します。

```typescript
type PolicyCategory = 'constitution' | 'naming' | 'security' | 'quality' | 'custom';

// 全ポリシー
const all = engine.listPolicies();

// 憲法条項のみ
const constitution = engine.listPolicies('constitution');

for (const p of constitution) {
  console.log(`${p.id}: ${p.name} - ${p.description}`);
}
```

#### `getPolicy(id: string): Policy | undefined`

IDでポリシーを取得します。

```typescript
const policy = engine.getPolicy('CONST-001');
if (policy) {
  console.log(policy.description);
  // => "Article I: Features must start as independent libraries"
}
```

#### `validate(context: ValidationContext, policyIds?: string[]): Promise<ValidationReport>`

コンテキストを検証します。

```typescript
interface ValidationContext {
  filePath?: string;    // ファイルパス
  content?: string;     // ファイル内容
  projectPath?: string; // プロジェクトパス
  config?: PolicyConfig;
}

interface ValidationReport {
  passed: boolean;
  totalPolicies: number;
  passedPolicies: number;
  failedPolicies: number;
  violations: Violation[];
  timestamp: string;
}

// 特定のポリシーのみ検証
const report = await engine.validate(
  { projectPath: '/path/to/project' },
  ['CONST-001', 'CONST-003']
);
```

#### `validateFile(filePath: string, policyIds?: string[]): Promise<ValidationReport>`

単一ファイルを検証します。

```typescript
const report = await engine.validateFile('storage/specs/REQ-001.md');
if (!report.passed) {
  console.log('EARS形式に準拠していません');
}
```

#### `validateProject(projectPath: string, policyIds?: string[]): Promise<ValidationReport>`

プロジェクト全体を検証します。

```typescript
const report = await engine.validateProject('.');

if (report.passed) {
  console.log('✅ すべての憲法条項に準拠しています');
} else {
  console.log(`❌ ${report.failedPolicies} 件の違反があります:`);
  
  for (const v of report.violations) {
    const icon = v.severity === 'error' ? '🚫' : '⚠️';
    console.log(`${icon} [${v.policyId}] ${v.message}`);
  }
}
```

#### `registerPolicy(policy: Policy): void`

カスタムポリシーを登録します。

```typescript
interface Policy {
  id: string;
  name: string;
  description: string;
  severity: 'error' | 'warning' | 'info';
  category: PolicyCategory;
  validate(context: ValidationContext): Promise<PolicyResult>;
  fix?(context: ValidationContext): Promise<FixResult>;  // オプション
}

engine.registerPolicy({
  id: 'CUSTOM-001',
  name: 'No Console Logs',
  description: 'Production code must not contain console.log',
  severity: 'warning',
  category: 'quality',
  async validate(ctx) {
    if (ctx.content?.includes('console.log')) {
      return {
        passed: false,
        violations: [{
          policyId: 'CUSTOM-001',
          message: 'console.log found in production code',
          severity: 'warning',
          location: { file: ctx.filePath },
        }],
      };
    }
    return { passed: true, violations: [] };
  },
});
```

#### `loadPolicies(dir: string): Promise<void>`

ディレクトリからカスタムポリシーを読み込みます。

```typescript
// policies/my-policy.ts をエクスポートするとロードされる
await engine.loadPolicies('./policies');
```

### 検証レポートの活用

```typescript
const report = await engine.validateProject('.');

// サマリー出力
console.log(`
=== Policy Validation Report ===
Timestamp: ${report.timestamp}
Status: ${report.passed ? '✅ PASSED' : '❌ FAILED'}
Policies: ${report.passedPolicies}/${report.totalPolicies} passed
`);

// 違反の詳細
if (report.violations.length > 0) {
  console.log('Violations:');
  
  const byCategory = new Map<string, Violation[]>();
  for (const v of report.violations) {
    const policy = engine.getPolicy(v.policyId);
    const cat = policy?.category ?? 'unknown';
    if (!byCategory.has(cat)) byCategory.set(cat, []);
    byCategory.get(cat)!.push(v);
  }
  
  for (const [category, violations] of byCategory) {
    console.log(`\n[${category}]`);
    for (const v of violations) {
      console.log(`  - ${v.policyId}: ${v.message}`);
    }
  }
}
```

---

## @musubix/decisions - ADRマネージャー

### 概要

Architecture Decision Records（ADR）を管理するパッケージです。プロジェクトのアーキテクチャ決定を記録・追跡します。

### ストレージ構造

```
docs/decisions/
├── index.md              # ADRインデックス（自動生成）
├── 0001-use-jwt-auth.md  # ADR #1
├── 0002-adopt-ddd.md     # ADR #2
└── ...
```

### ADRステータス

| ステータス | 説明 |
|-----------|------|
| `proposed` | 提案中（レビュー待ち） |
| `accepted` | 承認済み（有効） |
| `deprecated` | 非推奨（使用しないことを推奨） |
| `superseded` | 置き換え済み（別のADRに置き換わった） |

### クイックスタート

```typescript
import { createDecisionManager } from '@musubix/decisions';

const manager = createDecisionManager('docs/decisions');

// 新しいADRを作成
const adr = await manager.create({
  title: 'JWT認証の採用',
  context: 'ユーザー認証の仕組みが必要。セッション管理のオーバーヘッドを避けたい。',
  decision: 'JWTトークンベースの認証を採用する。',
  rationale: 'ステートレスでスケーラブル。マイクロサービス間でも利用可能。',
  alternatives: ['セッションベース認証', 'OAuth2のみ'],
  consequences: ['トークン失効の仕組みが必要', 'トークンサイズに注意'],
  relatedRequirements: ['REQ-AUTH-001'],
  decider: 'John Doe',
});

console.log(`ADR-${adr.id} created: ${adr.title}`);
// => ADR-0001 created: JWT認証の採用
```

### API リファレンス

#### `createDecisionManager(basePath: string): IDecisionManager`

Decision Manager を作成します。

```typescript
const manager = createDecisionManager('docs/decisions');
```

#### `create(draft: ADRDraft): Promise<ADR>`

新しいADRを作成します。

```typescript
interface ADRDraft {
  title: string;              // タイトル
  context: string;            // コンテキスト・背景
  decision: string;           // 決定内容
  rationale?: string;         // 理由
  alternatives?: string[];    // 検討した代替案
  consequences?: string[];    // 影響・結果
  relatedRequirements?: string[]; // 関連する要件ID
  decider?: string;           // 決定者
}

const adr = await manager.create({
  title: 'DDDの採用',
  context: 'ドメインロジックが複雑化している。',
  decision: 'Domain-Driven Designを採用し、ドメインモデルを中心に設計する。',
  rationale: 'ビジネスロジックの整理とテスタビリティの向上。',
  alternatives: ['トランザクションスクリプト', 'CRUDベース'],
  consequences: [
    '学習コストが発生',
    'エンティティとValue Objectの明確な区別が必要',
  ],
  relatedRequirements: ['REQ-ARCH-001'],
  decider: 'Tech Lead',
});
```

#### `get(id: string): Promise<ADR | undefined>`

IDでADRを取得します。

```typescript
const adr = await manager.get('0001');
if (adr) {
  console.log(adr.title);    // => 'JWT認証の採用'
  console.log(adr.status);   // => 'proposed'
}
```

#### `list(filter?: ADRFilter): Promise<ADR[]>`

ADR一覧を取得します。

```typescript
interface ADRFilter {
  status?: ADRStatus;  // ステータスでフィルタ
  keyword?: string;    // キーワード検索
}

// 全ADR
const all = await manager.list();

// 承認済みのみ
const accepted = await manager.list({ status: 'accepted' });

// キーワード検索
const authRelated = await manager.list({ keyword: '認証' });
```

#### `update(id: string, updates: Partial<ADR>): Promise<ADR>`

ADRを更新します。

```typescript
await manager.update('0001', {
  rationale: '追加の理由: セキュリティ監査でも推奨された。',
});
```

#### `accept(id: string): Promise<ADR>`

ADRを承認します（proposed → accepted）。

```typescript
const adr = await manager.accept('0001');
console.log(adr.status); // => 'accepted'
```

#### `deprecate(id: string, supersededBy?: string): Promise<ADR>`

ADRを非推奨にします。

```typescript
// 単純な非推奨
await manager.deprecate('0001');

// 別のADRに置き換え
await manager.deprecate('0001', '0005');
// 0001のステータスは 'superseded' になり、0005がリンクされる
```

#### `search(query: string): Promise<ADR[]>`

キーワードでADRを検索します。

```typescript
const results = await manager.search('認証');
```

#### `findByRequirement(reqId: string): Promise<ADR[]>`

要件IDに関連するADRを検索します。

```typescript
const adrs = await manager.findByRequirement('REQ-AUTH-001');
for (const adr of adrs) {
  console.log(`ADR-${adr.id}: ${adr.title}`);
}
```

#### `generateIndex(): Promise<void>`

ADRインデックス（index.md）を生成します。

```typescript
await manager.generateIndex();
// docs/decisions/index.md が生成される
```

### ADRテンプレート

`@musubix/decisions` には標準テンプレートがエクスポートされています：

```typescript
import { ADR_TEMPLATE } from '@musubix/decisions';

console.log(ADR_TEMPLATE);
// 標準ADRテンプレートが出力される
```

---

## 統合ユースケース

### ユースケース1: プロジェクト初期化

```typescript
import { knowledge, policy, decisions } from 'musubix';

async function initializeProject(projectPath: string) {
  // 1. Knowledge Store 初期化
  const store = knowledge.createKnowledgeStore(`${projectPath}/.knowledge`);
  
  // 2. 初期エンティティを作成
  await store.putEntity({
    id: 'PROJECT-META',
    type: 'project',
    name: 'My Project',
    properties: { createdAt: new Date().toISOString() },
    tags: ['root'],
  });
  await store.save();
  
  // 3. ポリシー検証
  const engine = policy.createPolicyEngine();
  const report = await engine.validateProject(projectPath);
  
  if (!report.passed) {
    console.log('⚠️ プロジェクト構造を調整してください:');
    for (const v of report.violations) {
      console.log(`  - ${v.message}`);
    }
  }
  
  // 4. ADRディレクトリ初期化
  const manager = decisions.createDecisionManager(`${projectPath}/docs/decisions`);
  await manager.generateIndex();
  
  console.log('✅ プロジェクト初期化完了');
}
```

### ユースケース2: 要件-設計-タスクのトレーサビリティ管理

```typescript
import { knowledge } from 'musubix';

async function createTraceableFeature(store: knowledge.KnowledgeStore) {
  // 要件
  const req = {
    id: 'REQ-PAY-001',
    type: 'requirement',
    name: '支払い機能',
    properties: {
      ears: 'WHEN user confirms order, THE system SHALL process payment',
      priority: 'P0',
    },
    tags: ['payment', 'core'],
  };
  
  // 設計
  const design = {
    id: 'DES-PAY-001',
    type: 'design',
    name: '支払いフロー設計',
    properties: {
      c4Level: 'component',
      patterns: ['Strategy', 'Adapter'],
    },
    tags: ['payment'],
  };
  
  // タスク群
  const tasks = [
    { id: 'TSK-PAY-001', name: 'PaymentService実装', estimate: '4h' },
    { id: 'TSK-PAY-002', name: 'StripeAdapter実装', estimate: '3h' },
    { id: 'TSK-PAY-003', name: 'テスト作成', estimate: '2h' },
  ];
  
  // エンティティ追加
  await store.putEntity(req);
  await store.putEntity(design);
  for (const task of tasks) {
    await store.putEntity({
      id: task.id,
      type: 'task',
      name: task.name,
      properties: { estimate: task.estimate },
      tags: ['payment', 'implementation'],
    });
  }
  
  // リレーション構築
  await store.addRelation({ source: 'DES-PAY-001', target: 'REQ-PAY-001', type: 'implements' });
  for (const task of tasks) {
    await store.addRelation({ source: task.id, target: 'DES-PAY-001', type: 'realizes' });
  }
  
  await store.save();
  
  // トレーサビリティ確認
  const trace = await store.traverse('REQ-PAY-001', { direction: 'incoming', maxDepth: 5 });
  console.log('トレーサビリティ:', trace.map(e => `${e.type}:${e.id}`).join(' → '));
}
```

### ユースケース3: アーキテクチャ決定の記録とポリシー検証

```typescript
import { policy, decisions } from 'musubix';

async function recordArchitectureDecision(
  projectPath: string,
  draft: decisions.ADRDraft
) {
  // 1. ADR作成
  const manager = decisions.createDecisionManager(`${projectPath}/docs/decisions`);
  const adr = await manager.create(draft);
  console.log(`📝 ADR-${adr.id} created: ${adr.title}`);
  
  // 2. インデックス更新
  await manager.generateIndex();
  
  // 3. ポリシー再検証（CONST-008: Decision Records）
  const engine = policy.createPolicyEngine();
  const report = await engine.validateProject(projectPath, ['CONST-008']);
  
  if (report.passed) {
    console.log('✅ CONST-008 (Decision Records) に準拠');
  }
  
  return adr;
}

// 使用例
await recordArchitectureDecision('.', {
  title: 'TypeScript採用',
  context: '型安全性とDXの向上が必要',
  decision: 'TypeScript 5.x を採用',
  rationale: '静的型付けによるバグ削減とIDEサポートの向上',
  alternatives: ['JavaScript + JSDoc', 'Flow'],
  consequences: ['ビルドステップが必要', '学習コスト'],
  decider: 'Tech Lead',
});
```

---

## CLI統合

### musubix CLIからの使用

```bash
# トレーサビリティマトリクス
npx musubix trace matrix

# 要件検証（EARS形式チェック）
npx musubix requirements validate storage/specs/REQ-001.md

# 設計検証
npx musubix design validate storage/design/DES-001.md
```

### プログラムからのCLI相当処理

```typescript
import { knowledge, policy } from 'musubix';

// トレーサビリティマトリクス相当
async function generateTraceMatrix(store: knowledge.KnowledgeStore) {
  const requirements = await store.query({ type: 'requirement' });
  
  console.log('| 要件ID | 設計ID | タスクID | ステータス |');
  console.log('|--------|--------|----------|-----------|');
  
  for (const req of requirements) {
    const designs = await store.traverse(req.id, {
      direction: 'incoming',
      relationTypes: ['implements'],
      maxDepth: 1,
    });
    
    for (const des of designs.filter(e => e.type === 'design')) {
      const tasks = await store.traverse(des.id, {
        direction: 'incoming',
        relationTypes: ['realizes'],
        maxDepth: 1,
      });
      
      console.log(`| ${req.id} | ${des.id} | ${tasks.map(t => t.id).join(', ')} | ✅ |`);
    }
  }
}
```

---

## トラブルシューティング

### Q: `graph.json` がGitで競合した

**A:** JSON形式なのでマージツールで解決できます。エンティティは `id` で一意なので、両方のエンティティを保持するマージが安全です。

```bash
# 競合解決後
git add .knowledge/graph.json
git commit -m "Merge knowledge graph"
```

### Q: ポリシー検証で常にエラーになる

**A:** プロジェクト構造が9憲法条項に準拠していない可能性があります：

```bash
# 必要なディレクトリ構造
mkdir -p packages bin storage/traceability storage/design steering docs/decisions
touch vitest.config.ts
```

### Q: ADRのIDが飛んでいる

**A:** ADR削除後にIDは再利用されません。これは意図的な設計で、過去の参照を壊さないためです。

### Q: traverse() が空配列を返す

**A:** リレーションの方向を確認してください：
- `outgoing`: 指定エンティティが `source` のリレーション
- `incoming`: 指定エンティティが `target` のリレーション

```typescript
// DES-001 → REQ-001 のリレーションがある場合
// REQ-001から辿るには incoming を指定
const result = await store.traverse('REQ-001', { direction: 'incoming' });
```

---

## 自然言語による操作（MCP統合）

MUSUBIX v3.0は、MCP（Model Context Protocol）サーバーを通じてAIエージェント（GitHub Copilot、Claude、Cursor等）から**自然言語で操作**できます。

### セットアップ

#### VS Code / GitHub Copilot での設定

`.vscode/mcp.json` を作成:

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

#### Claude Desktop での設定

`claude_desktop_config.json` に追加:

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

---

### Knowledge Store（知識グラフ）の自然言語操作

#### 利用可能なMCPツール

| ツール | 説明 |
|--------|------|
| `knowledge_put_entity` | エンティティの作成・更新 |
| `knowledge_get_entity` | エンティティの取得 |
| `knowledge_delete_entity` | エンティティの削除 |
| `knowledge_add_relation` | リレーションの追加 |
| `knowledge_query` | フィルタ検索 |
| `knowledge_traverse` | グラフ走査 |

#### 自然言語での使用例

**エンティティを作成したい場合:**

```
「ユーザー認証」という要件を知識グラフに追加して。
IDはREQ-AUTH-001、タグはsecurityとauthで。
EARS形式は「WHEN user submits credentials, THE system SHALL authenticate the user」
```

AIエージェントは `knowledge_put_entity` ツールを使用して：
```json
{
  "id": "REQ-AUTH-001",
  "type": "requirement",
  "name": "ユーザー認証",
  "properties": {
    "ears": "WHEN user submits credentials, THE system SHALL authenticate the user"
  },
  "tags": ["security", "auth"]
}
```

**リレーションを作成したい場合:**

```
DES-AUTH-001がREQ-AUTH-001を実装していることを記録して
```

AIエージェントは `knowledge_add_relation` ツールを使用して：
```json
{
  "source": "DES-AUTH-001",
  "target": "REQ-AUTH-001",
  "type": "implements"
}
```

**検索したい場合:**

```
securityタグが付いた要件を全部見せて
```

AIエージェントは `knowledge_query` ツールを使用して：
```json
{
  "type": "requirement",
  "tags": ["security"]
}
```

**トレーサビリティを確認したい場合:**

```
REQ-AUTH-001から辿れる設計とタスクを全部表示して
```

AIエージェントは `knowledge_traverse` ツールを使用して：
```json
{
  "startId": "REQ-AUTH-001",
  "direction": "in",
  "depth": 5
}
```

---

### Policy Engine（ポリシー検証）の自然言語操作

#### 利用可能なMCPツール

| ツール | 説明 |
|--------|------|
| `policy_validate` | プロジェクト全体の検証 |
| `policy_list` | ポリシー一覧取得 |
| `policy_get` | ポリシー詳細取得 |
| `policy_check_file` | 単一ファイル検証 |

#### 自然言語での使用例

**プロジェクトを検証したい場合:**

```
このプロジェクトが9憲法条項に準拠しているかチェックして
```

AIエージェントは `policy_validate` ツールを使用して：
```json
{
  "projectPath": "."
}
```

**特定のポリシーを確認したい場合:**

```
Library-Firstポリシー（CONST-001）の詳細を教えて
```

AIエージェントは `policy_get` ツールを使用して：
```json
{
  "id": "CONST-001"
}
```

**要件ファイルを検証したい場合:**

```
storage/specs/REQ-001.mdがEARS形式になっているか確認して
```

AIエージェントは `policy_check_file` ツールを使用して：
```json
{
  "filePath": "storage/specs/REQ-001.md"
}
```

**全ポリシーを確認したい場合:**

```
登録されているポリシーを一覧で見せて
```

AIエージェントは `policy_list` ツールを使用して：
```json
{
  "category": "constitution"
}
```

---

### Decision Records（ADR管理）の自然言語操作

#### 利用可能なMCPツール

| ツール | 説明 |
|--------|------|
| `decision_create` | ADRの作成 |
| `decision_list` | ADR一覧取得 |
| `decision_get` | ADR詳細取得 |
| `decision_accept` | ADRの承認 |
| `decision_deprecate` | ADRの非推奨化 |
| `decision_search` | キーワード検索 |
| `decision_find_by_requirement` | 要件からADR検索 |
| `decision_generate_index` | インデックス生成 |

#### 自然言語での使用例

**ADRを作成したい場合:**

```
「JWT認証の採用」というADRを作成して。

コンテキスト: ユーザー認証の仕組みが必要。セッション管理のオーバーヘッドを避けたい。
決定: JWTトークンベースの認証を採用する。
理由: ステートレスでスケーラブル。マイクロサービス間でも利用可能。
代替案: セッションベース認証、OAuth2のみ
影響: トークン失効の仕組みが必要、トークンサイズに注意
関連要件: REQ-AUTH-001
決定者: Tech Lead
```

AIエージェントは `decision_create` ツールを使用して：
```json
{
  "title": "JWT認証の採用",
  "context": "ユーザー認証の仕組みが必要。セッション管理のオーバーヘッドを避けたい。",
  "decision": "JWTトークンベースの認証を採用する。",
  "rationale": "ステートレスでスケーラブル。マイクロサービス間でも利用可能。",
  "alternatives": ["セッションベース認証", "OAuth2のみ"],
  "consequences": ["トークン失効の仕組みが必要", "トークンサイズに注意"],
  "relatedRequirements": ["REQ-AUTH-001"],
  "decider": "Tech Lead"
}
```

**ADRを承認したい場合:**

```
ADR-0001を承認して
```

AIエージェントは `decision_accept` ツールを使用して：
```json
{
  "id": "0001"
}
```

**ADRを検索したい場合:**

```
認証に関するADRを探して
```

AIエージェントは `decision_search` ツールを使用して：
```json
{
  "query": "認証"
}
```

**要件に関連するADRを探したい場合:**

```
REQ-AUTH-001に関連するアーキテクチャ決定を見せて
```

AIエージェントは `decision_find_by_requirement` ツールを使用して：
```json
{
  "requirementId": "REQ-AUTH-001"
}
```

**インデックスを更新したい場合:**

```
ADRのインデックスを再生成して
```

AIエージェントは `decision_generate_index` ツールを使用して：
```json
{}
```

---

### 統合的な自然言語ワークフロー

#### 例1: 要件からタスクまでの一連の作業

```
1. 「支払い機能」の要件を追加して（REQ-PAY-001）
2. その設計を作成して（DES-PAY-001、Strategyパターンを使用）
3. 設計から実装タスクを3つ作成して
4. それぞれのトレーサビリティを設定して
5. 最後にトレーサビリティチェーンを確認して
```

#### 例2: アーキテクチャ決定の記録と検証

```
1. TypeScript採用についてADRを作成して
2. 作成したADRを承認して
3. プロジェクトがCONST-008（Decision Records）に準拠しているか確認して
```

#### 例3: コードレビュー前のチェック

```
1. 9憲法条項への準拠をチェックして
2. 違反があれば詳細を教えて
3. 修正が必要な箇所を提案して
```

---

### プロンプトテンプレート

MUSUBIX MCPサーバーには以下のプロンプトテンプレートも用意されています：

| プロンプト名 | 説明 |
|-------------|------|
| `sdd_requirements_analysis` | 機能説明からEARS形式要件を生成 |
| `sdd_requirements_review` | 要件の完全性・憲法準拠レビュー |
| `sdd_design_generation` | 要件からC4モデル設計を生成 |
| `synthesis_guidance` | プログラム合成のガイダンス |
| `synthesis_explain_pattern` | パターンの説明生成 |

#### プロンプトの使用例

```
sdd_requirements_analysisプロンプトを使って、
「ユーザーがショッピングカートに商品を追加できる」
という機能の要件を分析して
```

---

## 参考リンク

- [MUSUBIX GitHub](https://github.com/nahisaho/MUSUBIX)
- [@musubix/knowledge 詳細マニュアル](./packages/knowledge.md)
- [MUSUBIX 9憲法条項](../steering/rules/constitution.md)
- [マイグレーションガイド (YATA → Knowledge)](./MIGRATION-v3.0.md)

---

**Document Version**: 3.0.0  
**Last Updated**: 2026-01-12
