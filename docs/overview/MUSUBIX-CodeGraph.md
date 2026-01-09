# MUSUBIX CodeGraph v2.3.0

> **@nahisaho/musubix-codegraph** - コード知識グラフライブラリ

## 概要

CodeGraphは、ソースコードを知識グラフとして構造化し、GraphRAGベースのセマンティック検索を提供するライブラリです。AST解析、依存関係追跡、呼び出しグラフ分析など、コードベース全体を理解するための機能を提供します。

## 主要機能

### 1. AST解析・エンティティ抽出

複数言語のソースコードを解析し、関数、クラス、変数などのエンティティを抽出します。

```typescript
import { createCodeGraph } from '@nahisaho/musubix-codegraph';

const codeGraph = await createCodeGraph({ storage: 'memory' });
const result = await codeGraph.index('/path/to/project');

console.log(`Entities: ${result.entitiesIndexed}`);
console.log(`Relations: ${result.relationsIndexed}`);
```

**対応言語:**
- TypeScript / JavaScript
- Python
- Rust
- Go
- Java
- PHP
- C# / C / C++
- Ruby
- Kotlin / Swift / Scala
- Lua
- HCL (Terraform)

### 2. グラフクエリ

エンティティをさまざまな条件で検索できます。

```typescript
// テキスト検索
const result = await codeGraph.query({ textSearch: 'authentication' });

// 型フィルタ
const classes = await codeGraph.query({ entityTypes: ['class'] });

// ファイルフィルタ
const entities = await codeGraph.query({ filePath: 'src/auth/' });
```

### 3. 依存関係分析

エンティティ間の依存関係を追跡します。

```typescript
// 依存先を検索
const deps = await codeGraph.findDependencies('UserService');

// インターフェースの実装を検索
const impls = await codeGraph.findImplementations('IRepository');
```

### 4. 呼び出しグラフ分析

関数・メソッドの呼び出し関係を分析します。

```typescript
// 呼び出し元を検索
const callers = await codeGraph.findCallers('authenticate');

// 呼び出し先を検索
const callees = await codeGraph.findCallees('processRequest');
```

### 5. GraphRAGセマンティック検索

コミュニティ検出とセマンティック検索を組み合わせた高度な検索機能です。

```typescript
// グローバル検索（コードベース全体）
const results = await codeGraph.globalSearch('user authentication flow');

// ローカル検索（特定エンティティ周辺）
const local = await codeGraph.localSearch('validation', {
  radius: 2,
  limit: 10,
});
```

## アーキテクチャ

```
┌─────────────────────────────────────────────────────────────┐
│                      CodeGraph API                          │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌───────────┐  ┌───────────┐  ┌───────────┐  ┌──────────┐ │
│  │ AST Parser│  │Graph Engine│  │  Indexer  │  │ GraphRAG │ │
│  └─────┬─────┘  └─────┬─────┘  └─────┬─────┘  └────┬─────┘ │
│        │              │              │              │       │
│  ┌─────▼─────────────▼──────────────▼──────────────▼─────┐ │
│  │                  Storage Adapter                       │ │
│  │           (Memory / SQLite / Custom)                   │ │
│  └───────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────┘
```

### コンポーネント

| コンポーネント | 役割 |
|---------------|------|
| **AST Parser** | Tree-sitterベースの多言語AST解析 |
| **Graph Engine** | エンティティ・リレーション管理、クエリ処理 |
| **Indexer** | ファイルシステム走査、並列インデックス |
| **GraphRAG** | コミュニティ検出、セマンティック検索 |
| **Storage** | プラグイン可能なストレージバックエンド |

## CLI コマンド

```bash
# ディレクトリをインデックス
npx musubix cg index <path>

# エンティティを検索
npx musubix cg query [name] [-t type] [-l limit]

# 依存関係を検索
npx musubix cg deps <name>

# 呼び出し元を検索
npx musubix cg callers <name>

# 呼び出し先を検索
npx musubix cg callees <name>

# セマンティック検索
npx musubix cg search <query> [-L local] [-c context]

# 統計を表示
npx musubix cg stats
```

## MCP ツール

MCPサーバー経由で以下のツールが利用可能です：

| ツール名 | 説明 |
|---------|------|
| `codegraph_index` | リポジトリ/ディレクトリをインデックス |
| `codegraph_query` | エンティティをクエリ |
| `codegraph_find_dependencies` | 依存関係を検索 |
| `codegraph_find_callers` | 関数の呼び出し元を検索 |
| `codegraph_find_callees` | 関数の呼び出し先を検索 |
| `codegraph_global_search` | GraphRAGセマンティック検索 |
| `codegraph_local_search` | ローカルコンテキスト検索 |
| `codegraph_stats` | グラフ統計を取得 |

## 設定オプション

```typescript
interface CodeGraphOptions {
  // ストレージバックエンド
  storage?: 'memory' | 'sqlite' | StorageAdapter;
  sqlitePath?: string;
  
  // パーサー設定
  parser?: {
    languages?: Language[];      // 対象言語
    includeComments?: boolean;   // コメント含む
    extractDocstrings?: boolean; // docstring抽出
  };
  
  // グラフエンジン設定
  graph?: {
    maxDepth?: number;           // 最大探索深度
    enableCaching?: boolean;     // キャッシュ有効化
  };
  
  // インデクサー設定
  indexer?: {
    ignorePatterns?: string[];   // 除外パターン
    maxFileSize?: number;        // 最大ファイルサイズ
    parallelism?: number;        // 並列処理数
  };
  
  // GraphRAG設定
  graphrag?: {
    communityAlgorithm?: 'louvain' | 'label_propagation';
    minCommunitySize?: number;
  };
}
```

## エンティティタイプ

| タイプ | 説明 |
|--------|------|
| `function` | 関数・メソッド |
| `class` | クラス |
| `interface` | インターフェース |
| `type` | 型エイリアス |
| `variable` | 変数・定数 |
| `module` | モジュール・名前空間 |
| `enum` | 列挙型 |
| `property` | プロパティ |
| `parameter` | パラメータ |

## リレーションタイプ

| タイプ | 説明 |
|--------|------|
| `calls` | 関数呼び出し |
| `imports` | インポート |
| `extends` | 継承 |
| `implements` | インターフェース実装 |
| `uses` | 使用（変数参照等） |
| `defines` | 定義（クラス→メソッド等） |
| `returns` | 戻り値の型 |
| `parameter_of` | パラメータ関係 |

## イベント

CodeGraphはイベントエミッターとして動作し、処理の進捗を監視できます。

```typescript
const codeGraph = await createCodeGraph();

codeGraph.onIndexingStart((path) => {
  console.log(`Indexing started: ${path}`);
});

codeGraph.onIndexingProgress((processed, total, file) => {
  console.log(`Progress: ${processed}/${total} - ${file}`);
});

codeGraph.onIndexingComplete((result) => {
  console.log(`Complete: ${result.entitiesIndexed} entities`);
});

codeGraph.onIndexingError((error, file) => {
  console.error(`Error in ${file}: ${error.message}`);
});
```

## 使用例

### プロジェクト分析

```typescript
import { createCodeGraph } from '@nahisaho/musubix-codegraph';

async function analyzeProject(projectPath: string) {
  const cg = await createCodeGraph({ storage: 'sqlite', sqlitePath: '.codegraph.db' });
  
  // インデックス作成
  const result = await cg.index(projectPath);
  console.log(`Indexed ${result.filesProcessed} files`);
  
  // 統計取得
  const stats = await cg.getStats();
  console.log(`Entities: ${stats.entityCount}`);
  console.log(`Relations: ${stats.relationCount}`);
  console.log(`Languages: ${stats.languages.join(', ')}`);
  
  // クラス一覧
  const classes = await cg.query({ entityTypes: ['class'] });
  console.log(`Classes: ${classes.entities.length}`);
  
  // 依存関係分析
  for (const cls of classes.entities.slice(0, 5)) {
    const deps = await cg.findDependencies(cls.name);
    console.log(`${cls.name} depends on: ${deps.map(d => d.name).join(', ')}`);
  }
}
```

### コードナビゲーション

```typescript
// 関数の呼び出し関係を可視化
async function traceCallGraph(functionName: string) {
  const cg = await createCodeGraph();
  await cg.index('./src');
  
  const callers = await cg.findCallers(functionName);
  const callees = await cg.findCallees(functionName);
  
  console.log(`=== ${functionName} ===`);
  console.log('Called by:');
  callers.forEach(c => console.log(`  <- ${c.from.name}`));
  console.log('Calls:');
  callees.forEach(c => console.log(`  -> ${c.to.name}`));
}
```

## 要件トレーサビリティ

| 要件ID | 説明 |
|--------|------|
| REQ-CG-API-001 | 独立ライブラリとして動作 |
| REQ-CG-API-002 | プログラマティックAPI提供 |
| REQ-CG-API-003 | CLI統合 |
| REQ-CG-AST-001 | 多言語AST解析 |
| REQ-CG-GRF-001 | エンティティ・リレーション管理 |
| REQ-CG-GRF-003 | グラフクエリ |
| REQ-CG-GRF-004 | 依存関係分析 |
| REQ-CG-GRF-005 | 呼び出しグラフ分析 |
| REQ-CG-RAG-001 | コミュニティ検出 |
| REQ-CG-RAG-002 | セマンティック検索 |

## 関連ドキュメント

- [MUSUBIX Overview](MUSUBIX-Overview.md)
- [MUSUBIX Core](MUSUBIX-Core.md)
- [MUSUBIX MCP Server](MUSUBIX-MCP-Server.md)

---

**バージョン**: 2.3.0  
**最終更新**: 2026-01-09
