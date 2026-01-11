# DES-KNW-001: Git-Native Knowledge System 設計書

| 項目 | 内容 |
|------|------|
| **設計ID** | DES-KNW-001 |
| **バージョン** | 1.0.0 |
| **作成日** | 2026-01-11 |
| **ステータス** | Draft |
| **トレーサビリティ** | REQ-KNW-001〜007, REQ-POL-001〜007, REQ-ADR-001〜004 |

---

## 1. 概要

### 1.1 目的

YATA（SQLite/分散型ナレッジグラフ）を廃止し、**Git-Native**なファイルベースの知識管理システムを構築する。これにより：

- **シンプルさ**: 追加インフラ不要、Gitリポジトリのみで完結
- **透明性**: すべての知識がテキストファイルとしてレビュー可能
- **バージョン管理**: Gitの履歴機能で変更追跡が自然に実現
- **コラボレーション**: 通常のPRワークフローで知識共有

### 1.2 スコープ

| 対象 | 内容 |
|------|------|
| **Knowledge Store** | `.knowledge/graph.json` - ファイルベース知識グラフ |
| **Policy Engine** | `.policies/*.ts` - 実行可能なTypeScriptポリシー |
| **Decision Records** | `docs/decisions/*.md` - ADR形式の意思決定記録 |

---

## 2. C4 コンテキスト図

```
┌─────────────────────────────────────────────────────────────────┐
│                        Git Repository                            │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────┐   │
│  │  .knowledge/ │  │  .policies/  │  │  docs/decisions/     │   │
│  │  graph.json  │  │  *.ts        │  │  *.md                │   │
│  └──────┬───────┘  └──────┬───────┘  └──────────┬───────────┘   │
│         │                 │                      │               │
│         └────────────┬────┴──────────────────────┘               │
│                      │                                           │
│              ┌───────▼───────┐                                   │
│              │  MUSUBIX CLI  │                                   │
│              │  MCP Server   │                                   │
│              └───────┬───────┘                                   │
│                      │                                           │
└──────────────────────┼───────────────────────────────────────────┘
                       │
              ┌────────▼────────┐
              │   AI Agent      │
              │ (Copilot/Claude)│
              └─────────────────┘
```

---

## 3. コンポーネント設計

### 3.1 Knowledge Store (`@musubix/knowledge`)

#### 3.1.1 ストレージ構造

```
.knowledge/
├── graph.json          # メイングラフ（エンティティ・リレーション）
├── index/              # 検索インデックス（オプション）
│   ├── by-type.json    # タイプ別インデックス
│   └── by-tag.json     # タグ別インデックス
└── schema.json         # スキーマ定義（オプション）
```

#### 3.1.2 graph.json スキーマ

```typescript
interface KnowledgeGraph {
  version: '1.0.0';
  metadata: {
    lastModified: string;  // ISO 8601
    entityCount: number;
    relationCount: number;
  };
  entities: Record<string, Entity>;
  relations: Relation[];
}

interface Entity {
  id: string;           // 例: "REQ-001", "DES-001", "func:UserService.create"
  type: EntityType;     // 'requirement' | 'design' | 'task' | 'code' | 'decision'
  name: string;
  description?: string;
  properties: Record<string, unknown>;
  tags: string[];
  createdAt: string;
  updatedAt: string;
}

interface Relation {
  id: string;
  source: string;       // Entity ID
  target: string;       // Entity ID
  type: RelationType;   // 'implements' | 'depends_on' | 'traces_to' | 'related_to'
  properties?: Record<string, unknown>;
}

type EntityType = 'requirement' | 'design' | 'task' | 'code' | 'decision' | 'pattern' | 'constraint';
type RelationType = 'implements' | 'depends_on' | 'traces_to' | 'related_to' | 'derives_from' | 'conflicts_with';
```

#### 3.1.3 API設計

```typescript
// packages/knowledge/src/index.ts
export interface KnowledgeStore {
  // CRUD操作
  getEntity(id: string): Promise<Entity | undefined>;
  putEntity(entity: Entity): Promise<void>;
  deleteEntity(id: string): Promise<boolean>;
  
  // リレーション操作
  addRelation(relation: Relation): Promise<void>;
  getRelations(entityId: string, direction?: 'in' | 'out' | 'both'): Promise<Relation[]>;
  
  // クエリ
  query(filter: QueryFilter): Promise<Entity[]>;
  search(text: string, options?: SearchOptions): Promise<Entity[]>;
  
  // グラフ操作
  getSubgraph(rootId: string, depth: number): Promise<KnowledgeGraph>;
  traverse(startId: string, relationTypes: RelationType[]): Promise<Entity[]>;
  
  // 永続化
  save(): Promise<void>;
  load(): Promise<void>;
}

export function createKnowledgeStore(basePath: string): KnowledgeStore;
```

---

### 3.2 Policy Engine (`@musubix/policy`)

#### 3.2.1 ストレージ構造

```
.policies/
├── constitution.ts     # 9憲法条項の検証ロジック
├── naming.ts           # 命名規則ポリシー
├── security.ts         # セキュリティポリシー
├── quality.ts          # 品質ゲートポリシー
└── custom/             # プロジェクト固有ポリシー
    └── *.ts
```

#### 3.2.2 ポリシー定義インターフェース

```typescript
// packages/policy/src/types.ts
export interface Policy {
  id: string;
  name: string;
  description: string;
  severity: 'error' | 'warning' | 'info';
  category: PolicyCategory;
  
  // 検証関数
  validate(context: ValidationContext): Promise<PolicyResult>;
  
  // 自動修正（オプション）
  fix?(context: ValidationContext): Promise<FixResult>;
}

export interface ValidationContext {
  filePath?: string;
  content?: string;
  ast?: unknown;
  knowledge: KnowledgeStore;
  config: PolicyConfig;
}

export interface PolicyResult {
  passed: boolean;
  violations: Violation[];
  suggestions?: string[];
}

export interface Violation {
  policyId: string;
  message: string;
  location?: Location;
  severity: 'error' | 'warning' | 'info';
}

type PolicyCategory = 'constitution' | 'naming' | 'security' | 'quality' | 'custom';
```

#### 3.2.3 組み込みポリシー

| ポリシーID | カテゴリ | 説明 |
|-----------|---------|------|
| `CONST-001` | constitution | Article I: Library-First |
| `CONST-002` | constitution | Article II: CLI Interface |
| `CONST-003` | constitution | Article III: Test-First |
| `CONST-004` | constitution | Article IV: EARS Format |
| `CONST-005` | constitution | Article V: Traceability |
| `CONST-006` | constitution | Article VI: Project Memory |
| `CONST-007` | constitution | Article VII: Design Patterns |
| `CONST-008` | constitution | Article VIII: Decision Records |
| `CONST-009` | constitution | Article IX: Quality Gates |
| `SEC-001` | security | No hardcoded secrets |
| `SEC-002` | security | Input validation required |
| `QUAL-001` | quality | Test coverage threshold |
| `QUAL-002` | quality | Complexity threshold |

#### 3.2.4 API設計

```typescript
// packages/policy/src/index.ts
export interface PolicyEngine {
  // ポリシー管理
  registerPolicy(policy: Policy): void;
  loadPolicies(dir: string): Promise<void>;
  getPolicy(id: string): Policy | undefined;
  listPolicies(category?: PolicyCategory): Policy[];
  
  // 検証
  validate(context: ValidationContext, policyIds?: string[]): Promise<ValidationReport>;
  validateFile(filePath: string): Promise<ValidationReport>;
  validateProject(projectPath: string): Promise<ValidationReport>;
  
  // 自動修正
  fix(context: ValidationContext, policyIds?: string[]): Promise<FixReport>;
}

export function createPolicyEngine(options?: PolicyEngineOptions): PolicyEngine;
```

---

### 3.3 Decision Records (`@musubix/decisions`)

#### 3.3.1 ストレージ構造

```
docs/decisions/
├── 0001-use-git-native-knowledge.md
├── 0002-adopt-ears-format.md
├── 0003-implement-policy-engine.md
├── template.md
└── index.md           # 自動生成インデックス
```

#### 3.3.2 ADRテンプレート

```markdown
# ADR-NNNN: タイトル

| 項目 | 内容 |
|------|------|
| **ステータス** | Proposed / Accepted / Deprecated / Superseded |
| **日付** | YYYY-MM-DD |
| **決定者** | 名前 |
| **関連要件** | REQ-XXX-NNN |

## コンテキスト

[決定が必要になった背景・問題]

## 決定

[採用した解決策]

## 理由

[なぜこの決定に至ったか]

## 代替案

[検討したが採用しなかった案]

## 影響

[この決定による影響・トレードオフ]

## 関連

- [関連ADR](./NNNN-title.md)
- [関連要件](../specs/REQ-XXX.md)
```

#### 3.3.3 API設計

```typescript
// packages/decisions/src/index.ts
export interface DecisionManager {
  // ADR管理
  create(draft: ADRDraft): Promise<ADR>;
  get(id: string): Promise<ADR | undefined>;
  list(filter?: ADRFilter): Promise<ADR[]>;
  update(id: string, updates: Partial<ADR>): Promise<ADR>;
  
  // ステータス管理
  accept(id: string): Promise<ADR>;
  deprecate(id: string, supersededBy?: string): Promise<ADR>;
  
  // インデックス
  generateIndex(): Promise<void>;
  
  // 検索
  search(query: string): Promise<ADR[]>;
  findByRequirement(reqId: string): Promise<ADR[]>;
}

export interface ADR {
  id: string;           // "0001"
  title: string;
  status: ADRStatus;
  date: string;
  decider: string;
  context: string;
  decision: string;
  rationale: string;
  alternatives: string[];
  consequences: string[];
  relatedRequirements: string[];
  relatedADRs: string[];
}

export function createDecisionManager(basePath: string): DecisionManager;
```

---

## 4. シーケンス図

### 4.1 知識グラフ更新フロー

```
┌─────────┐     ┌─────────────┐     ┌──────────────┐     ┌─────────┐
│AI Agent │     │ MCP Server  │     │KnowledgeStore│     │  Git    │
└────┬────┘     └──────┬──────┘     └──────┬───────┘     └────┬────┘
     │                 │                   │                  │
     │ knowledge_put   │                   │                  │
     │────────────────>│                   │                  │
     │                 │ putEntity()       │                  │
     │                 │──────────────────>│                  │
     │                 │                   │ validate schema  │
     │                 │                   │─────────────────>│
     │                 │                   │                  │
     │                 │                   │ update graph.json│
     │                 │                   │─────────────────>│
     │                 │                   │                  │
     │                 │      ok           │                  │
     │                 │<──────────────────│                  │
     │    success      │                   │                  │
     │<────────────────│                   │                  │
     │                 │                   │                  │
```

### 4.2 ポリシー検証フロー

```
┌─────────┐     ┌─────────────┐     ┌─────────────┐     ┌──────────────┐
│AI Agent │     │ MCP Server  │     │PolicyEngine │     │ .policies/   │
└────┬────┘     └──────┬──────┘     └──────┬──────┘     └──────┬───────┘
     │                 │                   │                   │
     │ policy_validate │                   │                   │
     │────────────────>│                   │                   │
     │                 │ loadPolicies()    │                   │
     │                 │──────────────────>│                   │
     │                 │                   │ import *.ts       │
     │                 │                   │──────────────────>│
     │                 │                   │                   │
     │                 │ validate()        │                   │
     │                 │──────────────────>│                   │
     │                 │                   │ run each policy   │
     │                 │                   │──────────────────>│
     │                 │                   │                   │
     │                 │ ValidationReport  │                   │
     │                 │<──────────────────│                   │
     │  violations[]   │                   │                   │
     │<────────────────│                   │                   │
     │                 │                   │                   │
```

---

## 5. MCP ツール設計

### 5.1 Knowledge ツール（6ツール）

| ツール名 | 説明 | 入力 |
|---------|------|------|
| `knowledge_get` | エンティティ取得 | `id: string` |
| `knowledge_put` | エンティティ追加/更新 | `entity: Entity` |
| `knowledge_delete` | エンティティ削除 | `id: string` |
| `knowledge_query` | クエリ実行 | `filter: QueryFilter` |
| `knowledge_relate` | リレーション追加 | `source, target, type` |
| `knowledge_traverse` | グラフ探索 | `startId, depth, types` |

### 5.2 Policy ツール（4ツール）

| ツール名 | 説明 | 入力 |
|---------|------|------|
| `policy_validate` | ポリシー検証 | `filePath?, policyIds?` |
| `policy_list` | ポリシー一覧 | `category?` |
| `policy_fix` | 自動修正 | `filePath, policyIds?` |
| `policy_check_constitution` | 憲法準拠チェック | `projectPath` |

### 5.3 Decision ツール（4ツール）

| ツール名 | 説明 | 入力 |
|---------|------|------|
| `decision_create` | ADR作成 | `draft: ADRDraft` |
| `decision_list` | ADR一覧 | `status?, keyword?` |
| `decision_get` | ADR取得 | `id: string` |
| `decision_accept` | ADR承認 | `id: string` |

---

## 6. 非機能要件対応

### 6.1 パフォーマンス（REQ-NFR-001）

| 操作 | 目標 | 実現方法 |
|------|------|----------|
| エンティティ取得 | <10ms | インメモリキャッシュ |
| クエリ（1000件） | <100ms | インデックス活用 |
| グラフ保存 | <500ms | 差分書き込み |

### 6.2 スケーラビリティ（REQ-NFR-002）

- **エンティティ上限**: 100,000件
- **グラフサイズ**: 〜50MB
- **大規模対応**: 分割ファイル（将来拡張）

### 6.3 互換性（REQ-NFR-003）

- Node.js 20+
- ESM/CommonJS両対応
- TypeScript 5.3+

---

## 7. マイグレーション計画

### 7.1 YATA→Git-Native移行

```
Phase 1: 新パッケージ作成
  └── @musubix/knowledge, @musubix/policy, @musubix/decisions

Phase 2: MCPツール追加
  └── knowledge_*, policy_*, decision_* ツール

Phase 3: CLIコマンド追加
  └── musubix knowledge, musubix policy, musubix decision

Phase 4: ドキュメント更新
  └── AGENTS.md, README, ユーザーガイド
```

### 7.2 既存データ移行（オプション）

```bash
# YATAデータがある場合のエクスポート
npx musubix migrate yata-to-git --source ./knowledge.db --target ./.knowledge/
```

---

## 8. トレーサビリティマトリクス

| 要件ID | 設計要素 | 実装箇所 |
|--------|---------|----------|
| REQ-KNW-001 | KnowledgeStore.putEntity | packages/knowledge/src/store.ts |
| REQ-KNW-002 | KnowledgeStore.query | packages/knowledge/src/query.ts |
| REQ-KNW-003 | KnowledgeStore.addRelation | packages/knowledge/src/relations.ts |
| REQ-KNW-004 | Git integration | packages/knowledge/src/persistence.ts |
| REQ-KNW-005 | KnowledgeStore.traverse | packages/knowledge/src/traverse.ts |
| REQ-KNW-006 | index/*.json | packages/knowledge/src/indexer.ts |
| REQ-KNW-007 | schema.json validation | packages/knowledge/src/schema.ts |
| REQ-POL-001 | PolicyEngine.registerPolicy | packages/policy/src/engine.ts |
| REQ-POL-002 | PolicyEngine.validate | packages/policy/src/validator.ts |
| REQ-POL-003 | Constitution policies | packages/policy/src/builtin/constitution.ts |
| REQ-POL-004 | PolicyEngine.fix | packages/policy/src/fixer.ts |
| REQ-POL-005 | Custom policy loading | packages/policy/src/loader.ts |
| REQ-POL-006 | PolicyResult interface | packages/policy/src/types.ts |
| REQ-POL-007 | Severity levels | packages/policy/src/types.ts |
| REQ-ADR-001 | DecisionManager.create | packages/decisions/src/manager.ts |
| REQ-ADR-002 | ADR template | packages/decisions/src/template.ts |
| REQ-ADR-003 | DecisionManager.generateIndex | packages/decisions/src/indexer.ts |
| REQ-ADR-004 | DecisionManager.search | packages/decisions/src/search.ts |

---

## 9. レビューチェックリスト

### 9.1 設計品質

- [ ] SOLID原則準拠
- [ ] 単一責任の原則（各パッケージの責務が明確）
- [ ] 依存性逆転（インターフェース定義）
- [ ] テスト容易性（DI可能な設計）

### 9.2 YATA削除確認

- [x] MCPツールからYATA参照削除済み
- [x] AGENTS.mdからYATA参照削除済み
- [x] README.md/README.ja.mdからYATA参照削除済み
- [x] package.jsonからYATA参照削除済み
- [ ] YATAパッケージフォルダの削除（別途対応）

### 9.3 新機能の整合性

- [x] 既存のConstitution Checker（`validateConstitutionTool`）との統合 → セクション10で定義
- [x] 既存のTraceability機能との連携 → セクション11で定義
- [x] 既存のLearning Systemとの共存 → セクション12で定義

---

## 10. 既存機能との統合設計

### 10.1 Constitution Checker統合

#### 現行実装

```typescript
// packages/mcp-server/src/tools/sdd-tools.ts
export const validateConstitutionTool: ToolDefinition = {
  name: 'sdd_validate_constitution',
  description: 'Validate against the 9 Constitutional Articles',
  // ...シンプルな検証ロジック
};
```

#### 統合方針

```
┌─────────────────────────────────────────────────────────┐
│  sdd_validate_constitution (既存MCPツール)              │
│    │                                                    │
│    └──▶ @musubix/policy の薄いラッパーとして再実装     │
│           │                                             │
│           └──▶ PolicyEngine.validate(                   │
│                  context,                               │
│                  ['CONST-001'...'CONST-009']           │
│                )                                        │
└─────────────────────────────────────────────────────────┘
```

#### 実装例

```typescript
// packages/mcp-server/src/tools/sdd-tools.ts (更新後)
import { createPolicyEngine } from '@musubix/policy';

export const validateConstitutionTool: ToolDefinition = {
  name: 'sdd_validate_constitution',
  handler: async (args) => {
    const { documentPath, articles } = args;
    const engine = createPolicyEngine();
    await engine.loadPolicies('.policies');
    
    const policyIds = (articles ?? [1,2,3,4,5,6,7,8,9])
      .map(n => `CONST-00${n}`);
    
    const result = await engine.validateFile(documentPath, policyIds);
    
    return success({
      action: 'validate_constitution',
      articlesChecked: articles,
      results: result.violations,
      overallCompliance: result.passed,
    });
  },
};
```

### 10.2 新旧ツールの共存

| 既存ツール | 新ツール | 関係 |
|-----------|---------|------|
| `sdd_validate_constitution` | `policy_check_constitution` | 既存は新の薄いラッパー |
| `sdd_validate_traceability` | `knowledge_traverse` | 既存は新を内部利用 |
| `sdd_create_requirements` | - | 変更なし |
| `sdd_create_design` | - | 変更なし |

---

## 11. CLIコマンド詳細設計

### 11.1 Knowledge コマンド

```bash
# 知識グラフの初期化
npx musubix knowledge init
  # → .knowledge/graph.json を作成

# エンティティ追加
npx musubix knowledge add <type> <id> --name <name> [--tags <tags>]
  # 例: npx musubix knowledge add requirement REQ-001 --name "ユーザー認証" --tags "security,auth"

# エンティティ検索
npx musubix knowledge query --type <type> [--tag <tag>] [--limit <n>]
  # 例: npx musubix knowledge query --type requirement --tag security

# リレーション追加
npx musubix knowledge relate <source> <relation> <target>
  # 例: npx musubix knowledge relate DES-001 implements REQ-001

# グラフ探索
npx musubix knowledge traverse <start-id> [--depth <n>] [--relations <types>]
  # 例: npx musubix knowledge traverse REQ-001 --depth 3

# 統計表示
npx musubix knowledge stats
  # → エンティティ数、リレーション数、タイプ別内訳

# エクスポート
npx musubix knowledge export --format <json|mermaid|dot>
  # 例: npx musubix knowledge export --format mermaid > graph.md
```

### 11.2 Policy コマンド

```bash
# ポリシー一覧
npx musubix policy list [--category <category>]
  # 例: npx musubix policy list --category constitution

# プロジェクト検証
npx musubix policy validate [<path>] [--policy <ids>]
  # 例: npx musubix policy validate ./src --policy CONST-001,SEC-001

# 憲法準拠チェック（ショートカット）
npx musubix policy constitution [<path>]
  # 例: npx musubix policy constitution

# 自動修正
npx musubix policy fix [<path>] [--policy <ids>] [--dry-run]
  # 例: npx musubix policy fix ./src --policy SEC-001 --dry-run

# カスタムポリシー生成
npx musubix policy create <name> --category <category>
  # 例: npx musubix policy create no-console-log --category custom
  # → .policies/custom/no-console-log.ts を生成
```

### 11.3 Decision コマンド

```bash
# ADR作成
npx musubix decision new <title>
  # 例: npx musubix decision new "Use Git-Native Knowledge"
  # → docs/decisions/0001-use-git-native-knowledge.md を生成

# ADR一覧
npx musubix decision list [--status <status>]
  # 例: npx musubix decision list --status accepted

# ADR承認
npx musubix decision accept <id>
  # 例: npx musubix decision accept 0001

# ADR廃止
npx musubix decision deprecate <id> [--superseded-by <new-id>]
  # 例: npx musubix decision deprecate 0001 --superseded-by 0005

# インデックス再生成
npx musubix decision index
  # → docs/decisions/index.md を更新

# ADR検索
npx musubix decision search <query>
  # 例: npx musubix decision search "authentication"
```

---

## 12. 初期化フロー設計

### 12.1 `musubix init` 拡張

```bash
npx musubix init [path] [--name <name>] [--force]
```

#### 生成されるディレクトリ構造

```
<project>/
├── .knowledge/                    # NEW: 知識グラフ
│   ├── graph.json                 # メイングラフ（空の初期状態）
│   └── schema.json                # スキーマ定義
├── .policies/                     # NEW: ポリシー
│   ├── constitution.ts            # 9憲法条項
│   ├── naming.ts                  # 命名規則
│   └── custom/                    # カスタムポリシー用
│       └── .gitkeep
├── docs/
│   └── decisions/                 # NEW: ADR
│       ├── template.md            # ADRテンプレート
│       └── index.md               # ADRインデックス
├── steering/                      # 既存: プロジェクトメモリ
│   ├── rules/
│   │   └── constitution.md
│   ├── structure.ja.md
│   ├── tech.ja.md
│   └── product.ja.md
├── storage/                       # 既存: 仕様書・成果物
│   ├── specs/
│   ├── design/
│   └── traceability/
└── AGENTS.md                      # 既存: AIエージェント向けガイド
```

### 12.2 初期ファイル内容

#### .knowledge/graph.json（初期状態）

```json
{
  "version": "1.0.0",
  "metadata": {
    "lastModified": "2026-01-11T00:00:00.000Z",
    "entityCount": 0,
    "relationCount": 0
  },
  "entities": {},
  "relations": []
}
```

#### .policies/constitution.ts

```typescript
import { Policy, ValidationContext, PolicyResult } from '@musubix/policy';

export const constitutionPolicies: Policy[] = [
  {
    id: 'CONST-001',
    name: 'Library-First',
    description: 'Article I: Features must start as independent libraries',
    severity: 'error',
    category: 'constitution',
    async validate(ctx: ValidationContext): Promise<PolicyResult> {
      // 実装: packages/ 配下に独立パッケージがあるか確認
      return { passed: true, violations: [] };
    },
  },
  // CONST-002 ~ CONST-009 も同様に定義
];
```

### 12.3 実装箇所

```typescript
// packages/core/src/cli/commands/init.ts
import { createKnowledgeStore } from '@musubix/knowledge';
import { createPolicyEngine } from '@musubix/policy';
import { createDecisionManager } from '@musubix/decisions';

export async function initProject(options: InitOptions): Promise<void> {
  // 既存の初期化処理...
  
  // NEW: Knowledge Store初期化
  const knowledge = createKnowledgeStore(path.join(projectPath, '.knowledge'));
  await knowledge.save();
  
  // NEW: Policy Engine初期化（デフォルトポリシーコピー）
  await copyDefaultPolicies(path.join(projectPath, '.policies'));
  
  // NEW: Decision Manager初期化
  const decisions = createDecisionManager(path.join(projectPath, 'docs/decisions'));
  await decisions.generateIndex();
}
```

---

## 13. Learning System との共存

### 13.1 既存Learning System

```
packages/core/src/learning/
├── feedback-collector.ts    # フィードバック収集
├── pattern-extractor.ts     # パターン抽出
├── adaptive-reasoner.ts     # 適応的推論
└── storage/                 # ローカルストレージ
```

### 13.2 Knowledge Storeとの連携

```typescript
// 学習パターンをKnowledge Graphに同期
interface LearningKnowledgeSync {
  // 学習パターンをエンティティとして保存
  syncPattern(pattern: LearnedPattern): Promise<void>;
  
  // フィードバックをリレーションとして保存
  syncFeedback(feedback: Feedback): Promise<void>;
  
  // Knowledge Graphから関連パターンを取得
  getRelatedPatterns(context: string): Promise<LearnedPattern[]>;
}
```

### 13.3 データフロー

```
┌──────────────────┐     ┌─────────────────┐     ┌──────────────────┐
│  Learning System │     │ LearningKnowledge│     │  Knowledge Store │
│  (既存)          │────▶│ Sync            │────▶│  (.knowledge/)   │
└──────────────────┘     └─────────────────┘     └──────────────────┘
        │                                                 │
        │                                                 │
        ▼                                                 ▼
┌──────────────────┐                            ┌──────────────────┐
│ storage/learning/│                            │ Git Repository   │
│ (ローカル永続化) │                            │ (共有・バージョン)│
└──────────────────┘                            └──────────────────┘
```

---

**レビュー日**: 2026-01-11
**レビュアー**: AI Agent (GitHub Copilot)
**ステータス**: レビュー完了 - 修正済み
