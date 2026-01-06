# MUSUBIX YATA パッケージ群

**関連パッケージ**:
- `@nahisaho/musubix-yata-client`
- `@nahisaho/yata-local`
- `@nahisaho/yata-global`
- `@nahisaho/yata-ui`

**バージョン**: 1.7.5  
**最終更新**: 2026-01-06

---

## 1. YATA概要

**YATA (Yet Another Triple Architecture)** は、MUSUBIXの知識グラフシステムです。ローカルとグローバルの2層構造で知識を管理し、AIエージェントに構造化された知識を提供します。

### 1.1 YATAの役割

```
┌─────────────────────────────────────────────────────────────┐
│                      AI Agent                                │
│              （Claude, Copilot, etc.）                       │
└──────────────────────┬──────────────────────────────────────┘
                       │
┌──────────────────────▼──────────────────────────────────────┐
│                  YATA Client                                 │
│           統一API・キャッシュ・同期                           │
└──────────────────────┬──────────────────────────────────────┘
                       │
        ┌──────────────┴──────────────┐
        │                             │
┌───────▼────────┐           ┌────────▼───────┐
│   YATA Local   │ ◄──同期──► │  YATA Global   │
│    SQLite      │           │    分散型      │
│   ローカルKG    │           │  グローバルKG   │
└────────────────┘           └────────────────┘
```

### 1.2 パッケージ構成

| パッケージ | 役割 |
|-----------|------|
| **yata-client** | クライアントライブラリ（統一API） |
| **yata-local** | SQLiteベースローカル知識グラフ |
| **yata-global** | 分散型グローバル知識グラフ |
| **yata-ui** | Web可視化・管理UI |

---

## 2. YATA Local

### 2.1 概要

`@nahisaho/yata-local` は、SQLiteベースのローカル知識グラフです。高速なクエリと永続化を提供します。

### 2.2 アーキテクチャ

```
packages/yata-local/src/
├── store/
│   ├── sqlite-store.ts    # SQLiteストレージ
│   ├── triple-store.ts    # トリプルストア
│   └── index-manager.ts   # インデックス管理
├── query/
│   ├── sparql-parser.ts   # SPARQLパーサー
│   ├── query-engine.ts    # クエリエンジン
│   └── optimizer.ts       # クエリ最適化
├── inference/
│   ├── reasoner.ts        # 推論エンジン
│   ├── rules.ts           # 推論ルール
│   └── transitive.ts      # 推移的閉包
├── sync/
│   ├── change-log.ts      # 変更ログ
│   └── delta-sync.ts      # 差分同期
└── index.ts
```

### 2.3 主要機能

#### 2.3.1 トリプルストア

RDF形式の知識を格納・検索します。

```typescript
import { YataLocal } from '@nahisaho/yata-local';

const yata = new YataLocal({
  dbPath: './knowledge.db',
});

// トリプル追加
await yata.addTriple({
  subject: 'req:REQ-001',
  predicate: 'rdf:type',
  object: 'sdd:Requirement',
});

// トリプル検索
const results = await yata.query({
  subject: 'req:REQ-001',
});
```

#### 2.3.2 SPARQLクエリ

SPARQL形式でクエリを実行します。

```typescript
const results = await yata.sparql(`
  SELECT ?req ?pattern
  WHERE {
    ?req rdf:type sdd:Requirement .
    ?req sdd:pattern ?pattern .
    FILTER(?pattern = "event-driven")
  }
`);
```

#### 2.3.3 推論エンジン

組み込みの推論ルールで暗黙知を導出します。

```typescript
// 推論を有効化
const yata = new YataLocal({
  inference: {
    enabled: true,
    rules: ['transitive', 'subclass', 'inverse'],
  },
});

// 推移的閉包クエリ
const ancestors = await yata.inferTransitive({
  subject: 'comp:UserService',
  predicate: 'sdd:dependsOn',
});
```

### 2.4 スキーマ

```sql
-- トリプルテーブル
CREATE TABLE triples (
  id INTEGER PRIMARY KEY,
  subject TEXT NOT NULL,
  predicate TEXT NOT NULL,
  object TEXT NOT NULL,
  graph TEXT DEFAULT 'default',
  created_at TEXT NOT NULL,
  UNIQUE(subject, predicate, object, graph)
);

-- インデックス
CREATE INDEX idx_subject ON triples(subject);
CREATE INDEX idx_predicate ON triples(predicate);
CREATE INDEX idx_object ON triples(object);
CREATE INDEX idx_spo ON triples(subject, predicate, object);

-- 変更ログ
CREATE TABLE change_log (
  id INTEGER PRIMARY KEY,
  operation TEXT NOT NULL,  -- 'add' | 'remove'
  subject TEXT NOT NULL,
  predicate TEXT NOT NULL,
  object TEXT NOT NULL,
  timestamp TEXT NOT NULL,
  synced INTEGER DEFAULT 0
);
```

---

## 3. YATA Global

### 3.1 概要

`@nahisaho/yata-global` は、分散型のグローバル知識グラフです。チーム間での知識共有と集合知を実現します。

### 3.2 アーキテクチャ

```
packages/yata-global/src/
├── network/
│   ├── peer-manager.ts    # P2Pピア管理
│   ├── gossip.ts          # ゴシッププロトコル
│   └── consensus.ts       # 合意形成
├── store/
│   ├── distributed-store.ts # 分散ストア
│   ├── partition.ts       # パーティション管理
│   └── replication.ts     # レプリケーション
├── privacy/
│   ├── filter.ts          # プライバシーフィルタ
│   ├── anonymizer.ts      # 匿名化
│   └── consent.ts         # 同意管理
├── api/
│   ├── server.ts          # APIサーバー
│   └── routes.ts          # APIルート
└── index.ts
```

### 3.3 主要機能

#### 3.3.1 分散ストレージ

```typescript
import { YataGlobal } from '@nahisaho/yata-global';

const yataGlobal = new YataGlobal({
  nodeId: 'node-001',
  peers: ['https://yata-peer-1.example.com'],
  replicationFactor: 3,
});

// グローバルクエリ
const patterns = await yataGlobal.queryPatterns({
  domain: 'authentication',
  minConfidence: 0.9,
});
```

#### 3.3.2 プライバシー保護

機密情報を除外して共有します。

```typescript
const yataGlobal = new YataGlobal({
  privacy: {
    level: 'strict',  // 'strict' | 'moderate' | 'none'
    excludePatterns: [
      '*.password',
      '*.apiKey',
      'company.*',
    ],
    anonymize: true,
  },
});
```

#### 3.3.3 KGPR（Knowledge Graph Pull Request）

知識グラフへの変更をレビュー可能な形式で提案します。

```typescript
// KGPR作成
const kgpr = await yataGlobal.createKGPR({
  title: 'Add authentication patterns',
  description: 'New patterns learned from Project-15',
  changes: [
    { operation: 'add', triple: {...} },
  ],
});

// KGPR送信
await yataGlobal.submitKGPR(kgpr.id);

// KGPRレビュー
await yataGlobal.reviewKGPR(kgpr.id, {
  decision: 'approve',
  comment: 'LGTM',
});
```

### 3.4 同期プロトコル

```
┌──────────────────────────────────────────────────────────────┐
│                    同期プロトコル                             │
└──────────────────────────────────────────────────────────────┘

1. 変更検出
   Local KG → Change Log → Delta Calculation

2. プライバシーフィルタリング
   Delta → Privacy Filter → Sanitized Delta

3. ゴシップ配信
   Sanitized Delta → Gossip Protocol → Peers

4. 合意形成
   Peers → Consensus → Global KG Update

5. 逆同期
   Global Updates → Local KG
```

---

## 4. YATA Client

### 4.1 概要

`@nahisaho/musubix-yata-client` は、YATAシステムへの統一アクセスを提供するクライアントライブラリです。

### 4.2 アーキテクチャ

```
packages/yata-client/src/
├── client.ts            # メインクライアント
├── cache.ts             # LRUキャッシュ
├── sync.ts              # 同期マネージャー
├── query-builder.ts     # クエリビルダー
├── types.ts             # 型定義
└── index.ts
```

### 4.3 主要API

#### 4.3.1 クライアント初期化

```typescript
import { YataClient } from '@nahisaho/musubix-yata-client';

const client = new YataClient({
  local: {
    dbPath: './knowledge.db',
  },
  global: {
    enabled: true,
    endpoint: 'https://yata.example.com',
    apiKey: process.env.YATA_API_KEY,
  },
  cache: {
    maxSize: 1000,
    ttl: 3600,
  },
});
```

#### 4.3.2 知識の追加

```typescript
// 単一トリプル追加
await client.add({
  subject: 'req:REQ-001',
  predicate: 'sdd:pattern',
  object: 'event-driven',
});

// バッチ追加
await client.addBatch([
  { subject: 'req:REQ-001', predicate: 'rdf:type', object: 'sdd:Requirement' },
  { subject: 'req:REQ-001', predicate: 'sdd:priority', object: 'P0' },
]);
```

#### 4.3.3 知識のクエリ

```typescript
// シンプルクエリ
const results = await client.query({
  subject: 'req:REQ-001',
});

// パターンクエリ
const requirements = await client.query({
  predicate: 'rdf:type',
  object: 'sdd:Requirement',
});

// クエリビルダー
const results = await client
  .queryBuilder()
  .select('?req', '?pattern')
  .where('?req', 'rdf:type', 'sdd:Requirement')
  .where('?req', 'sdd:pattern', '?pattern')
  .filter('?pattern', '=', 'event-driven')
  .execute();
```

#### 4.3.4 推論

```typescript
// 関連知識の取得
const related = await client.infer({
  subject: 'comp:UserService',
  depth: 2,  // 関係の深さ
});

// パス検索
const path = await client.findPath({
  from: 'req:REQ-001',
  to: 'code:UserService.ts',
});
```

#### 4.3.5 同期

```typescript
// 手動同期
await client.sync();

// 同期状態の確認
const status = await client.getSyncStatus();
console.log(status);
// { lastSync: '2026-01-06T12:00:00Z', pendingChanges: 5 }
```

### 4.4 イベント

```typescript
client.on('sync:start', () => console.log('同期開始'));
client.on('sync:complete', (stats) => console.log('同期完了', stats));
client.on('sync:error', (error) => console.error('同期エラー', error));
client.on('change:local', (change) => console.log('ローカル変更', change));
```

---

## 5. YATA UI

### 5.1 概要

`@nahisaho/yata-ui` は、知識グラフの可視化・管理を行うWebインターフェースです。

### 5.2 アーキテクチャ

```
packages/yata-ui/src/
├── components/
│   ├── GraphViewer.tsx    # グラフ可視化
│   ├── QueryEditor.tsx    # SPARQLエディタ
│   ├── TripleEditor.tsx   # トリプル編集
│   └── SyncStatus.tsx     # 同期状態表示
├── pages/
│   ├── Dashboard.tsx      # ダッシュボード
│   ├── Explorer.tsx       # グラフ探索
│   ├── Query.tsx          # クエリ実行
│   └── Settings.tsx       # 設定
├── hooks/
│   └── useYata.ts         # YATAフック
└── index.tsx
```

### 5.3 主要機能

#### 5.3.1 グラフ可視化

インタラクティブなグラフ表示を提供します。

```tsx
import { GraphViewer } from '@nahisaho/yata-ui';

function Explorer() {
  return (
    <GraphViewer
      query={{
        subject: 'req:REQ-001',
        depth: 3,
      }}
      layout="force-directed"
      onNodeClick={(node) => console.log(node)}
    />
  );
}
```

#### 5.3.2 SPARQLエディタ

シンタックスハイライト付きのSPARQLエディタを提供します。

```tsx
import { QueryEditor } from '@nahisaho/yata-ui';

function QueryPage() {
  const [results, setResults] = useState([]);
  
  return (
    <QueryEditor
      defaultQuery={`SELECT * WHERE { ?s ?p ?o } LIMIT 10`}
      onExecute={async (query) => {
        const result = await yataClient.sparql(query);
        setResults(result);
      }}
    />
  );
}
```

#### 5.3.3 トリプル管理

GUIでトリプルの追加・編集・削除が可能です。

```tsx
import { TripleEditor } from '@nahisaho/yata-ui';

function TriplePage() {
  return (
    <TripleEditor
      onAdd={async (triple) => {
        await yataClient.add(triple);
      }}
      onDelete={async (triple) => {
        await yataClient.remove(triple);
      }}
    />
  );
}
```

### 5.4 起動方法

```bash
# 開発サーバー
cd packages/yata-ui
npm run dev

# ビルド
npm run build

# プロダクション
npm run start
```

---

## 6. データモデル

### 6.1 名前空間

| 接頭辞 | URI | 説明 |
|--------|-----|------|
| `rdf` | `http://www.w3.org/1999/02/22-rdf-syntax-ns#` | RDF基本 |
| `rdfs` | `http://www.w3.org/2000/01/rdf-schema#` | RDFスキーマ |
| `sdd` | `http://musubix.dev/sdd#` | SDD方法論 |
| `req` | `http://musubix.dev/requirements#` | 要件 |
| `des` | `http://musubix.dev/design#` | 設計 |
| `code` | `http://musubix.dev/code#` | コード |
| `test` | `http://musubix.dev/test#` | テスト |
| `pattern` | `http://musubix.dev/patterns#` | パターン |

### 6.2 クラス階層

```turtle
@prefix sdd: <http://musubix.dev/sdd#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .

# 基本クラス
sdd:Artifact rdfs:subClassOf rdfs:Resource .

# 成果物タイプ
sdd:Requirement rdfs:subClassOf sdd:Artifact .
sdd:Design rdfs:subClassOf sdd:Artifact .
sdd:Code rdfs:subClassOf sdd:Artifact .
sdd:Test rdfs:subClassOf sdd:Artifact .

# 要件パターン
sdd:UbiquitousRequirement rdfs:subClassOf sdd:Requirement .
sdd:EventDrivenRequirement rdfs:subClassOf sdd:Requirement .
sdd:StateDrivenRequirement rdfs:subClassOf sdd:Requirement .
sdd:UnwantedRequirement rdfs:subClassOf sdd:Requirement .
sdd:OptionalRequirement rdfs:subClassOf sdd:Requirement .
```

### 6.3 プロパティ

```turtle
@prefix sdd: <http://musubix.dev/sdd#> .

# トレーサビリティ
sdd:implements a rdf:Property ;
    rdfs:domain sdd:Design ;
    rdfs:range sdd:Requirement .

sdd:realizedBy a rdf:Property ;
    rdfs:domain sdd:Requirement ;
    rdfs:range sdd:Code .

sdd:testedBy a rdf:Property ;
    rdfs:domain sdd:Code ;
    rdfs:range sdd:Test .

# メタデータ
sdd:priority a rdf:Property ;
    rdfs:domain sdd:Requirement ;
    rdfs:range xsd:string .

sdd:pattern a rdf:Property ;
    rdfs:domain sdd:Requirement ;
    rdfs:range xsd:string .
```

---

## 7. 設定

### 7.1 環境変数

| 変数名 | 説明 | デフォルト |
|--------|------|-----------|
| `YATA_DB_PATH` | SQLiteデータベースパス | `~/.musubix/yata.db` |
| `YATA_GLOBAL_ENDPOINT` | グローバルAPIエンドポイント | - |
| `YATA_API_KEY` | APIキー | - |
| `YATA_PRIVACY_LEVEL` | プライバシーレベル | `moderate` |
| `YATA_SYNC_INTERVAL` | 同期間隔（秒） | `3600` |

### 7.2 設定ファイル

`yata.config.json`:

```json
{
  "local": {
    "dbPath": "./knowledge.db",
    "inference": {
      "enabled": true,
      "rules": ["transitive", "subclass"]
    }
  },
  "global": {
    "enabled": true,
    "endpoint": "https://yata.example.com",
    "syncInterval": 3600
  },
  "privacy": {
    "level": "moderate",
    "excludePatterns": ["*.password", "*.secret"]
  },
  "cache": {
    "maxSize": 1000,
    "ttl": 3600
  }
}
```

---

## 8. CLI コマンド

```bash
# ローカルKG操作
npx yata add "req:REQ-001" "rdf:type" "sdd:Requirement"
npx yata query --subject "req:REQ-001"
npx yata sparql "SELECT * WHERE { ?s ?p ?o } LIMIT 10"

# 同期
npx yata sync
npx yata sync --status

# KGPR
npx yata kgpr create --title "New patterns"
npx yata kgpr list
npx yata kgpr submit <id>

# エクスポート/インポート
npx yata export --format turtle --output knowledge.ttl
npx yata import --format turtle knowledge.ttl

# UI起動
npx yata ui
```

---

## 9. 関連ドキュメント

| ドキュメント | 説明 |
|-------------|------|
| [MUSUBIX-Overview.md](MUSUBIX-Overview.md) | 全体概要 |
| [MUSUBIX-Core.md](MUSUBIX-Core.md) | Coreパッケージ |
| [MUSUBIX-MCP-Server.md](MUSUBIX-MCP-Server.md) | MCPサーバー |
| [API-REFERENCE.md](API-REFERENCE.md) | APIリファレンス |

---

**© 2026 MUSUBIX Project**
