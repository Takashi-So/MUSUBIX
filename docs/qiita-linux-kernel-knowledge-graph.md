---
title: 【実践】MUSUBIXでLinuxカーネルのナレッジグラフを構築する - 大規模Cソースコード解析
tags: Linux Kernel MUSUBIX KnowledgeGraph AIコーディング
private: false
---

# 【実践】MUSUBIXでLinuxカーネルのナレッジグラフを構築する

## はじめに

Linuxカーネルは**9000万行以上**のコードを持つ世界最大級のオープンソースプロジェクトです。この巨大なコードベースを理解するには、効果的なナレッジ管理が不可欠です。

本記事では、**MUSUBIX v3.0** の Git-Native Knowledge System を使用して、Linuxカーネルのスケジューラ（`kernel/sched/`）からナレッジグラフを自動構築する方法を解説します。

### 達成できること

| 項目 | 内容 |
|------|------|
| 📊 解析規模 | 45ファイル、2,222関数、76構造体 |
| 📚 ナレッジ | 2,475エンティティ、2,484リレーション |
| 🗃️ 出力形式 | Git-friendly JSON（1.7MB） |
| ⏱️ 処理時間 | 約10秒 |

## 環境準備

### 前提条件

```bash
# Node.js v20以上
node --version  # v20.0.0+

# Git
git --version
```

### ディレクトリ構成

```
/tmp/linux-kernel/           # 作業ディレクトリ
├── kernel/sched/            # 解析対象（スケジューラ）
├── .knowledge/
│   └── graph.json           # 生成されるナレッジグラフ
├── package.json
├── node_modules/
└── build-knowledge.mjs      # 構築スクリプト
```

## Step 1: Linuxカーネルソースのダウンロード

```bash
# /tmp に移動してLinuxカーネルをshallow cloneでダウンロード
cd /tmp
git clone --depth 1 https://github.com/torvalds/linux.git linux-kernel

# 確認
ls -la linux-kernel/kernel/sched/
# → 45ファイル（.c, .h）
```

:::note info
**Shallow Clone (`--depth 1`)**を使用することで、ダウンロードサイズを約2GBに抑えます。全履歴をクローンすると数十GBになります。
:::

## Step 2: MUSUBIXのインストール

```bash
cd /tmp/linux-kernel

# プロジェクト初期化
npm init -y

# ESモジュールを有効化
sed -i 's/"type": "commonjs"/"type": "module"/' package.json

# MUSUBIXパッケージをインストール
npm install musubix
```

:::note warn
**npm バージョン依存の問題**

v3.0.3以前のバージョンでは`peerDependencies`の問題でインストールに失敗する場合があります。その場合は以下を試してください：

```bash
npm install musubix --legacy-peer-deps
```

または、ローカルビルドからインストール：

```bash
npm install /path/to/MUSUBIX/packages/musubix
npm install /path/to/MUSUBIX/packages/knowledge
npm install /path/to/MUSUBIX/packages/codegraph
```
:::

## Step 3: ナレッジ構築スクリプトの作成

`build-knowledge.mjs` を作成します：

```javascript
#!/usr/bin/env node
/**
 * Linux Kernel Knowledge Builder
 * 
 * MUSUBIXのKnowledge Storeを使用して
 * Linuxカーネルソースコードから知識グラフを構築します。
 */

import { createKnowledgeStore } from '@musubix/knowledge';
import { readdir, readFile } from 'fs/promises';
import { join, basename, extname } from 'path';

// 設定
const KERNEL_PATH = '/tmp/linux-kernel';
const TARGET_SUBSYSTEM = 'kernel/sched';
const KNOWLEDGE_PATH = join(KERNEL_PATH, '.knowledge');

// リレーションIDカウンター
let relationCounter = 0;
function nextRelationId() {
  return `rel-${++relationCounter}`;
}

/**
 * Cファイルを再帰的に取得
 */
async function getCFiles(dir, files = []) {
  const entries = await readdir(dir, { withFileTypes: true });
  
  for (const entry of entries) {
    const fullPath = join(dir, entry.name);
    if (entry.isDirectory()) {
      await getCFiles(fullPath, files);
    } else if (entry.isFile() && ['.c', '.h'].includes(extname(entry.name))) {
      files.push(fullPath);
    }
  }
  
  return files;
}

/**
 * 関数定義を抽出（簡易パーサー）
 */
function extractFunctions(content, filename) {
  const functions = [];
  
  // Cの関数定義パターン
  const funcRegex = /^(\w[\w\s\*]+?)\s+(\w+)\s*\(([^)]*)\)\s*\{/gm;
  let match;
  
  while ((match = funcRegex.exec(content)) !== null) {
    const returnType = match[1].trim();
    const name = match[2];
    const params = match[3].trim();
    
    functions.push({
      name,
      returnType: returnType.replace(/static|inline/g, '').trim(),
      params,
      isStatic: returnType.includes('static'),
      isInline: returnType.includes('inline'),
      file: filename,
    });
  }
  
  return functions;
}

/**
 * 構造体定義を抽出
 */
function extractStructs(content, filename) {
  const structs = [];
  const structRegex = /struct\s+(\w+)\s*\{/g;
  let match;
  
  while ((match = structRegex.exec(content)) !== null) {
    structs.push({
      name: match[1],
      file: filename,
    });
  }
  
  return structs;
}

/**
 * メイン処理
 */
async function main() {
  console.log('🐧 Linux Kernel Knowledge Builder');
  console.log(`Target: ${TARGET_SUBSYSTEM}`);

  // Knowledge Store初期化
  const store = createKnowledgeStore(KNOWLEDGE_PATH);
  
  // ファイル取得
  const targetPath = join(KERNEL_PATH, TARGET_SUBSYSTEM);
  const cFiles = await getCFiles(targetPath);
  console.log(`Found ${cFiles.length} C/H files`);
  
  // サブシステムエンティティを作成
  await store.putEntity({
    id: 'subsystem:sched',
    type: 'code',
    name: 'Linux Scheduler',
    description: 'Linux kernel process scheduler implementation',
    properties: {
      path: TARGET_SUBSYSTEM,
      algorithms: ['CFS', 'RT', 'Deadline', 'Stop', 'Idle'],
    },
    tags: ['kernel', 'scheduler', 'linux', 'subsystem'],
  });

  // 各ファイルを解析
  for (const file of cFiles) {
    const filename = file.replace(KERNEL_PATH + '/', '');
    const content = await readFile(file, 'utf-8');
    
    // ファイルエンティティ
    const fileId = `file:${filename.replace(/[\/\.]/g, '-')}`;
    await store.putEntity({
      id: fileId,
      type: 'code',
      name: basename(file),
      properties: {
        path: filename,
        lines: content.split('\n').length,
        language: 'c',
      },
      tags: extname(file) === '.h' ? ['header', 'c'] : ['source', 'c'],
    });
    
    await store.addRelation({
      id: nextRelationId(),
      source: 'subsystem:sched',
      target: fileId,
      type: 'implements',
    });
    
    // 関数抽出
    const functions = extractFunctions(content, filename);
    for (const func of functions) {
      const funcId = `function:${func.name}`;
      const existing = await store.getEntity(funcId);
      
      if (!existing) {
        await store.putEntity({
          id: funcId,
          type: 'code',
          name: func.name,
          properties: {
            returnType: func.returnType,
            params: func.params,
            isStatic: func.isStatic,
            file: func.file,
          },
          tags: ['function', func.isStatic ? 'static' : 'public'],
        });
        
        await store.addRelation({
          id: nextRelationId(),
          source: fileId,
          target: funcId,
          type: 'implements',
        });
      }
    }
    
    // 構造体抽出
    const structs = extractStructs(content, filename);
    for (const struct of structs) {
      const structId = `struct:${struct.name}`;
      const existing = await store.getEntity(structId);
      
      if (!existing) {
        await store.putEntity({
          id: structId,
          type: 'code',
          name: struct.name,
          properties: { file: struct.file },
          tags: ['struct', 'data-structure'],
        });
        
        await store.addRelation({
          id: nextRelationId(),
          source: fileId,
          target: structId,
          type: 'implements',
        });
      }
    }
    
    console.log(`📄 ${filename} (${functions.length} funcs)`);
  }
  
  // コンセプトエンティティを追加
  const concepts = [
    {
      id: 'concept:cfs',
      name: 'Completely Fair Scheduler (CFS)',
      description: 'The default scheduler. Uses red-black tree sorted by vruntime.',
      tags: ['scheduler', 'cfs', 'algorithm'],
    },
    {
      id: 'concept:runqueue',
      name: 'Run Queue (rq)',
      description: 'Per-CPU data structure holding runnable processes.',
      tags: ['scheduler', 'data-structure'],
    },
    {
      id: 'concept:vruntime',
      name: 'Virtual Runtime',
      description: 'Weighted CPU time. Used by CFS to pick next task.',
      tags: ['cfs', 'metric'],
    },
  ];
  
  for (const concept of concepts) {
    await store.putEntity({
      id: concept.id,
      type: 'pattern',
      name: concept.name,
      description: concept.description,
      properties: {},
      tags: concept.tags,
    });
    
    await store.addRelation({
      id: nextRelationId(),
      source: 'subsystem:sched',
      target: concept.id,
      type: 'implements',
    });
  }
  
  // 保存
  await store.save();
  
  const stats = store.getStats();
  console.log(`\n✅ Entities: ${stats.entityCount}, Relations: ${stats.relationCount}`);
  console.log(`📁 Saved to: ${KNOWLEDGE_PATH}/graph.json`);
}

main().catch(console.error);
```

## Step 4: ナレッジグラフの構築

```bash
# スクリプト実行
node build-knowledge.mjs
```

### 実行結果

```
🐧 Linux Kernel Knowledge Builder
Target: kernel/sched
Found 45 C/H files
📄 kernel/sched/autogroup.c (16 funcs)
📄 kernel/sched/clock.c (24 funcs)
📄 kernel/sched/core.c (403 funcs)
📄 kernel/sched/fair.c (445 funcs)
📄 kernel/sched/rt.c (121 funcs)
📄 kernel/sched/deadline.c (134 funcs)
...

✅ Entities: 2475, Relations: 2484
📁 Saved to: /tmp/linux-kernel/.knowledge/graph.json
```

## Step 5: ナレッジグラフの確認

```bash
# ファイルサイズ確認
ls -lh /tmp/linux-kernel/.knowledge/graph.json
# → 1.7M

# 構造確認
head -50 /tmp/linux-kernel/.knowledge/graph.json
```

### 生成されたナレッジグラフの構造

```json
{
  "version": "1.0.0",
  "metadata": {
    "lastModified": "2026-01-11T20:14:57.921Z",
    "entityCount": 2475,
    "relationCount": 2484
  },
  "entities": {
    "subsystem:sched": {
      "id": "subsystem:sched",
      "type": "code",
      "name": "Linux Scheduler",
      "description": "Linux kernel process scheduler implementation",
      "properties": {
        "path": "kernel/sched",
        "algorithms": ["CFS", "RT", "Deadline", "Stop", "Idle"]
      },
      "tags": ["kernel", "scheduler", "linux", "subsystem"]
    },
    "function:update_curr": {
      "id": "function:update_curr",
      "type": "code",
      "name": "update_curr",
      "properties": {
        "returnType": "void",
        "params": "struct cfs_rq *cfs_rq",
        "isStatic": true,
        "file": "kernel/sched/fair.c"
      },
      "tags": ["function", "static"]
    }
    // ... 2,473件のエンティティ
  },
  "relations": [
    {
      "id": "rel-1",
      "source": "subsystem:sched",
      "target": "file:kernel-sched-autogroup-c",
      "type": "implements"
    }
    // ... 2,483件のリレーション
  ]
}
```

## ナレッジの活用例

### 1. 関数の検索

```javascript
import { createKnowledgeStore } from '@musubix/knowledge';

const store = createKnowledgeStore('/tmp/linux-kernel/.knowledge');
await store.load();

// CFSに関連する関数を検索
const cfsFunctions = await store.search('cfs', {
  fields: ['name', 'tags'],
  limit: 10,
});

console.log(cfsFunctions.map(f => f.name));
// ['pick_next_task_fair', 'enqueue_task_fair', 'dequeue_task_fair', ...]
```

### 2. 構造体の依存関係

```javascript
// rq構造体に関連するエンティティを取得
const rqRelations = await store.getRelations('struct:rq', 'both');
console.log(`rq has ${rqRelations.length} relations`);
```

### 3. サブグラフの抽出

```javascript
// スケジューラサブシステムから深さ2のサブグラフを取得
const subgraph = await store.getSubgraph('subsystem:sched', 2);
console.log(`Subgraph: ${Object.keys(subgraph.entities).length} entities`);
```

## Step 5: CodeGraph CLIによるインデックス作成（オプション）

MUSUBIXにはCodeGraph CLIが付属しており、AST解析によるコードグラフも作成できます。

```bash
# CodeGraph CLIでインデックス作成
npx musubix cg index ./kernel/sched

# サポート言語一覧
npx musubix cg languages

# 統計表示
npx musubix cg stats
```

### CodeGraphの機能

| 機能 | 説明 |
|------|------|
| **AST解析** | Tree-sitterベースの構文解析（16言語対応） |
| **依存関係** | 関数間の呼び出しグラフ構築 |
| **GraphRAG** | 意味的なコード検索 |

```bash
# 依存関係の検索
npx musubix cg deps schedule

# 関数の呼び出し元を検索
npx musubix cg callers update_curr

# セマンティック検索
npx musubix cg search "process scheduling algorithm"
```

:::note info
**Knowledge Store vs CodeGraph**

| 観点 | Knowledge Store | CodeGraph |
|------|-----------------|-----------|
| 用途 | ドメイン知識・概念の管理 | コード構造・依存関係の解析 |
| 永続化 | JSON（Git管理可） | SQLite / メモリ |
| 抽象度 | 高（概念レベル） | 低（コードレベル） |
| 検索 | タグ・テキスト検索 | GraphRAG・依存関係走査 |

両者を組み合わせることで、**コード構造**と**ドメイン知識**の両方を統合管理できます。
:::

## Git-Native Knowledge Systemの利点

### 1. サーバーレス

```
❌ 従来: データベースサーバーが必要
   PostgreSQL, Neo4j, etc.

✅ MUSUBIX v3.0: JSONファイルのみ
   .knowledge/graph.json
```

### 2. バージョン管理

```bash
# ナレッジグラフの変更をGitで追跡
git add .knowledge/
git commit -m "Add scheduler knowledge graph"
git push
```

### 3. チーム協業

```bash
# プルリクエストでナレッジの変更をレビュー
git diff .knowledge/graph.json

# マージコンフリクトはJSONレベルで解決可能
```

## 拡張: 全カーネルの解析

スケジューラ以外のサブシステムも同様に解析できます：

```javascript
const SUBSYSTEMS = [
  'kernel/sched',    // スケジューラ
  'mm',              // メモリ管理
  'fs',              // ファイルシステム
  'net',             // ネットワーク
  'drivers/usb',     // USBドライバ
];

for (const subsystem of SUBSYSTEMS) {
  const files = await getCFiles(join(KERNEL_PATH, subsystem));
  console.log(`${subsystem}: ${files.length} files`);
}
```

:::note warn
**注意**: 全カーネル（9万ファイル以上）を解析すると、数十GBのナレッジグラフが生成される可能性があります。サブシステム単位での解析を推奨します。
:::

## まとめ

| 項目 | 内容 |
|------|------|
| **目的** | Linuxカーネルのナレッジグラフ構築 |
| **ツール** | MUSUBIX v3.0 Git-Native Knowledge System |
| **対象** | kernel/sched（スケジューラ） |
| **結果** | 2,475エンティティ、2,484リレーション |
| **出力** | JSON形式（1.7MB、Git管理可能） |

### 今後の発展

- 🔍 **CodeGraph連携**: ASTパーサーによる精密な解析
- 🤖 **AI連携**: LLMによるナレッジの自動拡充
- 📊 **可視化**: グラフDBへのエクスポート、D3.js可視化

## 参考リンク

- [MUSUBIX GitHub](https://github.com/nahisaho/MUSUBIX)
- [Linux Kernel Source](https://github.com/torvalds/linux)
- [Linuxカーネルスケジューラ - LWN.net](https://lwn.net/Kernel/Index/)

---

**関連記事**:
- [MUSUBIXで始めるエンタープライズナレッジ管理](https://qiita.com/nahisaho/items/xxx)
- [Git-Native Knowledge Systemの設計思想](https://qiita.com/nahisaho/items/yyy)
