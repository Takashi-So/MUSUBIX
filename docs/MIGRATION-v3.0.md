# MUSUBIX v3.0 マイグレーションガイド

このドキュメントは MUSUBIX v2.x から v3.0 への移行手順を説明します。

## 概要

MUSUBIX v3.0.0 では **Git-Native Knowledge System** を導入し、YATA（Yet Another Temporal Architecture）を廃止しました。

### 主な変更点

| 項目 | v2.x | v3.0 |
|------|------|------|
| 知識ストレージ | YATA (SQLite/分散) | Git-friendly JSON |
| ストレージパス | `.yata/` | `.knowledge/` |
| 知識グラフAPI | YATAClient | FileKnowledgeStore |
| ポリシー検証 | 手動 | PolicyEngine (9憲法条項) |
| ADR管理 | 手動 | DecisionManager |

---

## Step 1: パッケージ更新

### package.json の更新

```diff
{
  "dependencies": {
-   "@nahisaho/musubix-yata-client": "^2.4.2",
-   "@nahisaho/yata-local": "^2.4.6",
-   "@nahisaho/yata-global": "^2.4.4",
+   "@musubix/knowledge": "^3.0.0",
+   "@musubix/policy": "^3.0.0",
+   "@musubix/decisions": "^3.0.0"
  }
}
```

### インストール

```bash
npm install @musubix/knowledge @musubix/policy @musubix/decisions
npm uninstall @nahisaho/musubix-yata-client @nahisaho/yata-local @nahisaho/yata-global
```

---

## Step 2: 知識グラフ API の移行

### v2.x (YATA)

```typescript
import { YATAClient } from '@nahisaho/musubix-yata-client';

const client = new YATAClient({ dbPath: '.yata/knowledge.db' });
await client.addNode({ id: 'REQ-001', type: 'requirement', label: 'User Login' });
await client.addEdge({ from: 'REQ-001', to: 'DES-001', type: 'implements' });
const nodes = await client.query({ type: 'requirement' });
```

### v3.0 (FileKnowledgeStore)

```typescript
import { createKnowledgeStore } from '@musubix/knowledge';

const store = createKnowledgeStore('.knowledge');
await store.putEntity({ id: 'REQ-001', type: 'requirement', name: 'User Login' });
await store.addRelation({ from: 'REQ-001', to: 'DES-001', type: 'implements' });
const entities = await store.query({ type: 'requirement' });
```

### API マッピング表

| YATA (v2.x) | Knowledge (v3.0) | 説明 |
|-------------|------------------|------|
| `addNode()` | `putEntity()` | エンティティ作成/更新 |
| `getNode()` | `getEntity()` | エンティティ取得 |
| `deleteNode()` | `deleteEntity()` | エンティティ削除 |
| `addEdge()` | `addRelation()` | リレーション追加 |
| `deleteEdge()` | `removeRelation()` | リレーション削除 |
| `query()` | `query()` | 検索 |
| `traverse()` | `traverse()` | グラフ走査 |

---

## Step 3: データ移行

### 自動移行スクリプト

```typescript
// scripts/migrate-yata-to-knowledge.ts
import Database from 'better-sqlite3';
import { createKnowledgeStore } from '@musubix/knowledge';
import * as fs from 'node:fs';

async function migrateYataToKnowledge(yataDbPath: string, knowledgePath: string) {
  // 1. Open YATA SQLite database
  const db = new Database(yataDbPath, { readonly: true });
  
  // 2. Create Knowledge store
  const store = createKnowledgeStore(knowledgePath);
  
  // 3. Migrate nodes → entities
  const nodes = db.prepare('SELECT * FROM nodes').all();
  for (const node of nodes) {
    await store.putEntity({
      id: node.id,
      type: mapNodeType(node.type),
      name: node.label || node.id,
      properties: JSON.parse(node.properties || '{}'),
    });
  }
  
  // 4. Migrate edges → relations
  const edges = db.prepare('SELECT * FROM edges').all();
  for (const edge of edges) {
    await store.addRelation({
      from: edge.from_id,
      to: edge.to_id,
      type: mapEdgeType(edge.type),
    });
  }
  
  db.close();
  console.log(`Migrated ${nodes.length} entities, ${edges.length} relations`);
}

function mapNodeType(yataType: string): string {
  const mapping: Record<string, string> = {
    'requirement': 'requirement',
    'design': 'design',
    'task': 'task',
    'code': 'code',
    'test': 'code',
    'pattern': 'pattern',
  };
  return mapping[yataType] || 'code';
}

function mapEdgeType(yataType: string): string {
  const mapping: Record<string, string> = {
    'implements': 'implements',
    'depends': 'depends_on',
    'traces': 'traces_to',
    'uses': 'depends_on',
  };
  return mapping[yataType] || 'depends_on';
}

// 実行
migrateYataToKnowledge('.yata/knowledge.db', '.knowledge');
```

### 手動移行

1. `.yata/` ディレクトリをバックアップ
2. 新しい `.knowledge/` ディレクトリを作成
3. 既存データを JSON 形式でエクスポート/インポート

---

## Step 4: ポリシー検証の追加

v3.0 では9憲法条項をプログラマブルに検証できます。

```typescript
import { createPolicyEngine } from '@musubix/policy';

const engine = createPolicyEngine();

// プロジェクト全体の検証
const report = await engine.validate({ projectPath: '.' });

if (!report.passed) {
  for (const violation of report.violations) {
    console.error(`[${violation.policyId}] ${violation.message}`);
  }
}

// 特定ポリシーのみ検証
const earsReport = await engine.validate(
  { filePath: 'storage/specs/REQ-001.md', content: fileContent },
  ['CONST-004'] // EARS Format のみ
);
```

### 利用可能なポリシー

| ID | 名称 | 説明 |
|----|------|------|
| CONST-001 | Library-First | 独立ライブラリ化の検証 |
| CONST-002 | CLI Interface | CLI公開必須の検証 |
| CONST-003 | Test-First | テスト先行の検証 |
| CONST-004 | EARS Format | EARS形式準拠の検証 |
| CONST-005 | Traceability | トレーサビリティの検証 |
| CONST-006 | Project Memory | steering/参照の検証 |
| CONST-007 | Design Patterns | 設計パターン適用の検証 |
| CONST-008 | Decision Records | ADR記録の検証 |
| CONST-009 | Quality Gates | 品質ゲートの検証 |

---

## Step 5: ADR 管理の追加

```typescript
import { createDecisionManager } from '@musubix/decisions';

const manager = createDecisionManager('docs/decisions');

// ADR 作成
const adr = await manager.create({
  title: 'Use Git-Native Knowledge System',
  context: 'Need simpler knowledge storage that works with Git',
  decision: 'Replace YATA with JSON-based FileKnowledgeStore',
  rationale: 'Git-friendly, no external database required',
});

// ADR 承認
await manager.accept(adr.id);

// ADR 一覧
const adrs = await manager.list({ status: 'accepted' });
```

---

## Step 6: CLI コマンドの更新

### v2.x

```bash
# YATA 関連コマンドは非推奨
npx yata-ui
npx yata-global-server
```

### v3.0

```bash
# Knowledge コマンド
npx musubix knowledge put REQ-001 requirement "User Login"
npx musubix knowledge get REQ-001
npx musubix knowledge link REQ-001 DES-001 implements
npx musubix knowledge query --type requirement

# Policy コマンド
npx musubix policy validate
npx musubix policy list
npx musubix policy check storage/specs/REQ-001.md

# Decision コマンド
npx musubix decision create "Use TypeScript" --context "..." --decision "..."
npx musubix decision list
npx musubix decision accept 0001
npx musubix adr index
```

---

## Step 7: MCP ツールの更新

### v2.x MCP ツール (廃止)

- `yata_query` → 廃止
- `yata_add_node` → 廃止
- `yata_add_edge` → 廃止

### v3.0 MCP ツール (新規)

| ツール | 説明 |
|--------|------|
| `knowledge_put_entity` | エンティティ作成/更新 |
| `knowledge_get_entity` | エンティティ取得 |
| `knowledge_delete_entity` | エンティティ削除 |
| `knowledge_add_relation` | リレーション追加 |
| `knowledge_query` | グラフクエリ |
| `knowledge_traverse` | グラフ走査 |
| `policy_validate` | ポリシー検証 |
| `policy_list` | ポリシー一覧 |
| `policy_get` | ポリシー詳細 |
| `policy_check_file` | ファイル検証 |
| `decision_create` | ADR作成 |
| `decision_list` | ADR一覧 |
| `decision_get` | ADR詳細 |
| `decision_accept` | ADR承認 |
| `decision_deprecate` | ADR廃止 |
| `decision_search` | ADR検索 |
| `decision_find_by_requirement` | 要件からADR検索 |
| `decision_generate_index` | インデックス生成 |

---

## トラブルシューティング

### Q: YATA データベースが見つからない

A: `.yata/` ディレクトリが存在しない場合、移行は不要です。新規に `.knowledge/` を作成してください。

### Q: エンティティタイプが一致しない

A: v3.0 では以下のタイプのみサポート:
- `requirement`
- `design`
- `task`
- `code`
- `pattern`

### Q: リレーションタイプが一致しない

A: v3.0 では以下のタイプのみサポート:
- `implements`
- `depends_on`
- `traces_to`

---

## サポート

問題が発生した場合は GitHub Issues で報告してください:
https://github.com/nahisaho/MUSUBIX/issues

---

**Last Updated**: 2026-01-14
**Version**: v3.0.0
