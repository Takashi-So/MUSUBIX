# DES-YATA-SCALE-001: YATA Scale Design

## 文書情報

| 項目 | 内容 |
|------|------|
| 文書ID | DES-YATA-SCALE-001 |
| バージョン | 1.0.0 |
| 作成日 | 2026-01-08 |
| 作成者 | MUSUBIX Development Team |
| ステータス | Draft |
| トレーサビリティ | REQ-YATA-SCALE-001 |

---

## 1. 概要

### 1.1 設計目標

yata-scaleパッケージは、YATAナレッジグラフを大規模環境（100万エンティティ以上）でスケーラブルに動作させるための拡張機能を提供します。

### 1.2 設計原則

1. **水平スケーラビリティ**: シャード追加による線形スケーリング
2. **低レイテンシ**: マルチレベルキャッシュとインデックス最適化
3. **高可用性**: レプリケーションと自動フェイルオーバー
4. **後方互換性**: 既存yata-local/yata-globalとのシームレス統合

---

## 2. アーキテクチャ

### 2.1 C4 Context Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                           System Context                                  │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                           │
│  ┌─────────────┐     ┌───────────────────────────────────┐               │
│  │ AI Coding   │────▶│         YATA Scale                │               │
│  │ Assistant   │     │   (Distributed KG Platform)       │               │
│  └─────────────┘     └───────────────────────────────────┘               │
│         │                        │                                        │
│         │                        │                                        │
│         ▼                        ▼                                        │
│  ┌─────────────┐     ┌─────────────┐  ┌─────────────┐                   │
│  │ yata-local  │     │ yata-global │  │  External   │                   │
│  │  (SQLite)   │     │ (Framework) │  │  Storage    │                   │
│  └─────────────┘     └─────────────┘  └─────────────┘                   │
│                                                                           │
└─────────────────────────────────────────────────────────────────────────┘
```

### 2.2 C4 Container Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        YATA Scale Containers                             │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                           │
│  ┌───────────────────────────────────────────────────────────────────┐  │
│  │                     API Layer                                      │  │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐               │  │
│  │  │ YataScale   │  │ CLI         │  │ MCP Server  │               │  │
│  │  │ Manager     │  │ Interface   │  │ Adapter     │               │  │
│  │  └─────────────┘  └─────────────┘  └─────────────┘               │  │
│  └───────────────────────────────────────────────────────────────────┘  │
│                              │                                           │
│  ┌───────────────────────────┼───────────────────────────────────────┐  │
│  │                     Core Layer                                     │  │
│  │                           │                                        │  │
│  │  ┌─────────────┐  ┌───────┴─────┐  ┌─────────────┐               │  │
│  │  │ Query       │  │ Shard       │  │ Cache       │               │  │
│  │  │ Coordinator │◀▶│ Manager     │◀▶│ Manager     │               │  │
│  │  └─────────────┘  └─────────────┘  └─────────────┘               │  │
│  │         │                │                │                        │  │
│  │  ┌──────┴───────┐  ┌─────┴─────┐  ┌──────┴──────┐               │  │
│  │  │ Parallel     │  │ Partition │  │ Replication │               │  │
│  │  │ Executor     │  │ Router    │  │ Controller  │               │  │
│  │  └──────────────┘  └───────────┘  └─────────────┘               │  │
│  └───────────────────────────────────────────────────────────────────┘  │
│                              │                                           │
│  ┌───────────────────────────┼───────────────────────────────────────┐  │
│  │                    Storage Layer                                   │  │
│  │                           │                                        │  │
│  │  ┌─────────────┐  ┌───────┴─────┐  ┌─────────────┐               │  │
│  │  │ Index       │  │ Storage     │  │ WAL         │               │  │
│  │  │ Engine      │  │ Engine      │  │ Manager     │               │  │
│  │  └─────────────┘  └─────────────┘  └─────────────┘               │  │
│  └───────────────────────────────────────────────────────────────────┘  │
│                                                                           │
│  ┌───────────────────────────────────────────────────────────────────┐  │
│  │                    Shard Instances                                 │  │
│  │  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐             │  │
│  │  │ Shard 0 │  │ Shard 1 │  │ Shard 2 │  │ Shard N │             │  │
│  │  │ (Local) │  │ (Local) │  │ (Remote)│  │ (Remote)│             │  │
│  │  └─────────┘  └─────────┘  └─────────┘  └─────────┘             │  │
│  └───────────────────────────────────────────────────────────────────┘  │
│                                                                           │
└─────────────────────────────────────────────────────────────────────────┘
```

### 2.3 C4 Component Diagram

```
┌───────────────────────────────────────────────────────────────────────────┐
│                       YATA Scale Components                                │
├───────────────────────────────────────────────────────────────────────────┤
│                                                                            │
│  ┌────────────────────────────────────────────────────────────────────┐   │
│  │                    Shard Manager Component                          │   │
│  │                                                                      │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐              │   │
│  │  │ HashPartition│  │ RangePartition│ │GraphPartition│              │   │
│  │  │ Strategy     │  │ Strategy     │  │ Strategy     │              │   │
│  │  └──────────────┘  └──────────────┘  └──────────────┘              │   │
│  │          │                │                │                        │   │
│  │          └────────────────┼────────────────┘                        │   │
│  │                           ▼                                         │   │
│  │                  ┌──────────────┐                                   │   │
│  │                  │ Partition    │                                   │   │
│  │                  │ Router       │                                   │   │
│  │                  └──────────────┘                                   │   │
│  │                           │                                         │   │
│  │          ┌────────────────┼────────────────┐                        │   │
│  │          ▼                ▼                ▼                        │   │
│  │  ┌──────────────┐ ┌──────────────┐ ┌──────────────┐                │   │
│  │  │ Shard        │ │ Rebalancer   │ │ Failover     │                │   │
│  │  │ Registry     │ │              │ │ Handler      │                │   │
│  │  └──────────────┘ └──────────────┘ └──────────────┘                │   │
│  └────────────────────────────────────────────────────────────────────┘   │
│                                                                            │
│  ┌────────────────────────────────────────────────────────────────────┐   │
│  │                    Index Engine Component                           │   │
│  │                                                                      │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐              │   │
│  │  │ BPlusTree    │  │ FullText     │  │ Graph        │              │   │
│  │  │ Index        │  │ Index        │  │ Index        │              │   │
│  │  └──────────────┘  └──────────────┘  └──────────────┘              │   │
│  │          │                │                │                        │   │
│  │          └────────────────┼────────────────┘                        │   │
│  │                           ▼                                         │   │
│  │                  ┌──────────────┐  ┌──────────────┐                │   │
│  │                  │ Bloom Filter │  │ Index        │                │   │
│  │                  │ Layer        │  │ Compactor    │                │   │
│  │                  └──────────────┘  └──────────────┘                │   │
│  └────────────────────────────────────────────────────────────────────┘   │
│                                                                            │
│  ┌────────────────────────────────────────────────────────────────────┐   │
│  │                    Cache Manager Component                          │   │
│  │                                                                      │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐              │   │
│  │  │ L1 Cache     │  │ L2 Cache     │  │ L3 Cache     │              │   │
│  │  │ (Hot/Memory) │  │ (Warm/Comp)  │  │ (Cold/Disk)  │              │   │
│  │  └──────────────┘  └──────────────┘  └──────────────┘              │   │
│  │          │                │                │                        │   │
│  │          └────────────────┼────────────────┘                        │   │
│  │                           ▼                                         │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐              │   │
│  │  │ Invalidation │  │ Promotion/   │  │ Cache        │              │   │
│  │  │ Manager      │  │ Demotion     │  │ Warmer       │              │   │
│  │  └──────────────┘  └──────────────┘  └──────────────┘              │   │
│  └────────────────────────────────────────────────────────────────────┘   │
│                                                                            │
│  ┌────────────────────────────────────────────────────────────────────┐   │
│  │                    Query Coordinator Component                      │   │
│  │                                                                      │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐              │   │
│  │  │ Query        │  │ Distributed  │  │ Result       │              │   │
│  │  │ Planner      │  │ Executor     │  │ Merger       │              │   │
│  │  └──────────────┘  └──────────────┘  └──────────────┘              │   │
│  │          │                │                │                        │   │
│  │          └────────────────┼────────────────┘                        │   │
│  │                           ▼                                         │   │
│  │  ┌──────────────┐  ┌──────────────┐                                │   │
│  │  │ Worker       │  │ Pipeline     │                                │   │
│  │  │ Thread Pool  │  │ Processor    │                                │   │
│  │  └──────────────┘  └──────────────┘                                │   │
│  └────────────────────────────────────────────────────────────────────┘   │
│                                                                            │
│  ┌────────────────────────────────────────────────────────────────────┐   │
│  │                    Sync Controller Component                        │   │
│  │                                                                      │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐              │   │
│  │  │ WAL          │  │ Vector       │  │ Conflict     │              │   │
│  │  │ Manager      │  │ Clock        │  │ Resolver     │              │   │
│  │  └──────────────┘  └──────────────┘  └──────────────┘              │   │
│  │          │                │                │                        │   │
│  │          └────────────────┼────────────────┘                        │   │
│  │                           ▼                                         │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐              │   │
│  │  │ Delta        │  │ Replication  │  │ Offline      │              │   │
│  │  │ Sync         │  │ Controller   │  │ Queue        │              │   │
│  │  └──────────────┘  └──────────────┘  └──────────────┘              │   │
│  └────────────────────────────────────────────────────────────────────┘   │
│                                                                            │
└───────────────────────────────────────────────────────────────────────────┘
```

---

## 3. 詳細設計

### 3.1 シャード管理 (REQ-SCALE-DIST-*)

#### 3.1.1 パーティショニング戦略

```typescript
// パーティション戦略インターフェース
interface PartitionStrategy {
  /** エンティティのシャードを決定 */
  getShardId(entityId: string, metadata?: EntityMetadata): string;
  
  /** シャード追加時のキーリマッピング */
  remap(oldShardCount: number, newShardCount: number): Map<string, string>;
  
  /** パーティションキーの抽出 */
  extractPartitionKey(entity: Entity): string;
}

// ハッシュパーティショニング
class HashPartitionStrategy implements PartitionStrategy {
  constructor(
    private readonly shardCount: number,
    private readonly hashFunction: HashFunction = xxhash64
  ) {}

  getShardId(entityId: string): string {
    const hash = this.hashFunction(entityId);
    const shardIndex = hash % BigInt(this.shardCount);
    return `shard-${shardIndex}`;
  }

  // 一貫性ハッシュリングでリマッピングを最小化
  remap(oldCount: number, newCount: number): Map<string, string> {
    return this.consistentHashRemap(oldCount, newCount);
  }
}

// レンジパーティショニング
class RangePartitionStrategy implements PartitionStrategy {
  constructor(private readonly ranges: RangeConfig[]) {}

  getShardId(entityId: string, metadata?: EntityMetadata): string {
    const key = this.extractPartitionKey({ id: entityId, ...metadata } as Entity);
    for (const range of this.ranges) {
      if (key >= range.start && key < range.end) {
        return range.shardId;
      }
    }
    throw new Error(`No shard for key: ${key}`);
  }
}

// グラフパーティショニング（連結成分ベース）
class GraphPartitionStrategy implements PartitionStrategy {
  private componentMap: Map<string, string> = new Map();

  async initialize(graph: KnowledgeGraph): Promise<void> {
    const components = this.findConnectedComponents(graph);
    this.assignComponentsToShards(components);
  }

  getShardId(entityId: string): string {
    return this.componentMap.get(entityId) ?? 'shard-default';
  }
}
```

#### 3.1.2 シャードマネージャー

```typescript
interface ShardManager {
  // ライフサイクル
  createShard(config: ShardConfig): Promise<ShardInfo>;
  removeShard(shardId: string, graceful?: boolean): Promise<void>;
  
  // シャード操作
  getShardInfo(shardId: string): Promise<ShardInfo>;
  listShards(): Promise<ShardInfo[]>;
  getShardForEntity(entityId: string): Promise<ShardInfo>;
  
  // リバランシング
  startRebalance(options?: RebalanceOptions): Promise<RebalanceJob>;
  getRebalanceStatus(jobId: string): Promise<RebalanceStatus>;
  cancelRebalance(jobId: string): Promise<void>;
  
  // ヘルスチェック
  checkHealth(): Promise<Map<string, ShardHealth>>;
  repairShard(shardId: string): Promise<RepairResult>;
}

interface ShardConfig {
  shardId: string;
  capacity: number;
  location: 'local' | 'remote';
  endpoint?: string;
  replicationFactor?: number;
}

interface ShardInfo {
  shardId: string;
  status: 'active' | 'rebalancing' | 'draining' | 'offline';
  entityCount: number;
  sizeBytes: number;
  location: string;
  replicas: string[];
  lastModified: Date;
}
```

### 3.2 インデックスエンジン (REQ-SCALE-INDEX-*)

#### 3.2.1 B+Treeインデックス

```typescript
interface BPlusTreeIndex<K, V> {
  // 基本操作
  insert(key: K, value: V): Promise<void>;
  delete(key: K): Promise<boolean>;
  get(key: K): Promise<V | undefined>;
  
  // レンジクエリ
  range(start: K, end: K, options?: RangeOptions): AsyncIterable<[K, V]>;
  
  // バルク操作
  bulkInsert(entries: [K, V][]): Promise<void>;
  
  // メンテナンス
  compact(): Promise<void>;
  getStats(): Promise<IndexStats>;
}

interface BPlusTreeConfig {
  pageSize: number;        // デフォルト: 4096
  fanout: number;          // デフォルト: 128
  cacheSize: number;       // ページキャッシュサイズ
  compression?: 'none' | 'lz4' | 'zstd';
}

class BPlusTreeIndexImpl<K, V> implements BPlusTreeIndex<K, V> {
  private root: BPlusTreeNode<K, V>;
  private pageCache: LRUCache<number, Page>;
  private wal: WriteAheadLog;

  async insert(key: K, value: V): Promise<void> {
    await this.wal.append({ type: 'insert', key, value });
    const leaf = await this.findLeaf(key);
    await leaf.insert(key, value);
    if (leaf.isOverfull()) {
      await this.split(leaf);
    }
  }

  async *range(start: K, end: K): AsyncIterable<[K, V]> {
    const leaf = await this.findLeaf(start);
    let current: BPlusTreeLeaf<K, V> | null = leaf;
    
    while (current) {
      for (const [key, value] of current.entries()) {
        if (key >= end) return;
        if (key >= start) yield [key, value];
      }
      current = await current.getNextLeaf();
    }
  }
}
```

#### 3.2.2 グラフインデックス

```typescript
interface GraphIndex {
  // 隣接関係
  getOutgoingEdges(entityId: string): Promise<Edge[]>;
  getIncomingEdges(entityId: string): Promise<Edge[]>;
  
  // k-hopクエリ
  getNeighbors(entityId: string, depth: number): Promise<Set<string>>;
  
  // パス検索
  findPath(source: string, target: string, maxDepth?: number): Promise<Path | null>;
  findAllPaths(source: string, target: string, maxDepth?: number): AsyncIterable<Path>;
  
  // パターンマッチング
  matchPattern(pattern: GraphPattern): AsyncIterable<PatternMatch>;
}

class GraphIndexImpl implements GraphIndex {
  private adjacencyIndex: Map<string, Set<string>>;
  private reverseIndex: Map<string, Set<string>>;
  private edgeIndex: BPlusTreeIndex<string, Edge>;

  async getNeighbors(entityId: string, depth: number): Promise<Set<string>> {
    const visited = new Set<string>();
    const queue: [string, number][] = [[entityId, 0]];

    while (queue.length > 0) {
      const [current, d] = queue.shift()!;
      if (d > depth || visited.has(current)) continue;
      visited.add(current);

      const neighbors = this.adjacencyIndex.get(current) ?? new Set();
      for (const neighbor of neighbors) {
        queue.push([neighbor, d + 1]);
      }
    }

    visited.delete(entityId);
    return visited;
  }

  async *findAllPaths(
    source: string,
    target: string,
    maxDepth: number = 10
  ): AsyncIterable<Path> {
    const stack: { node: string; path: string[] }[] = [
      { node: source, path: [source] },
    ];

    while (stack.length > 0) {
      const { node, path } = stack.pop()!;
      
      if (node === target) {
        yield { nodes: path, length: path.length - 1 };
        continue;
      }

      if (path.length > maxDepth) continue;

      const neighbors = this.adjacencyIndex.get(node) ?? new Set();
      for (const neighbor of neighbors) {
        if (!path.includes(neighbor)) {
          stack.push({ node: neighbor, path: [...path, neighbor] });
        }
      }
    }
  }
}
```

#### 3.2.3 ブルームフィルタ

```typescript
class BloomFilter {
  private bitArray: Uint8Array;
  private hashCount: number;
  private size: number;

  constructor(expectedItems: number, falsePositiveRate: number = 0.01) {
    this.size = this.calculateSize(expectedItems, falsePositiveRate);
    this.hashCount = this.calculateHashCount(this.size, expectedItems);
    this.bitArray = new Uint8Array(Math.ceil(this.size / 8));
  }

  add(item: string): void {
    for (let i = 0; i < this.hashCount; i++) {
      const hash = this.hash(item, i);
      const index = hash % this.size;
      this.bitArray[Math.floor(index / 8)] |= 1 << (index % 8);
    }
  }

  mightContain(item: string): boolean {
    for (let i = 0; i < this.hashCount; i++) {
      const hash = this.hash(item, i);
      const index = hash % this.size;
      if ((this.bitArray[Math.floor(index / 8)] & (1 << (index % 8))) === 0) {
        return false;
      }
    }
    return true;
  }

  private hash(item: string, seed: number): number {
    // MurmurHash3 with seed
    return murmur3(item, seed);
  }

  private calculateSize(n: number, p: number): number {
    return Math.ceil(-n * Math.log(p) / (Math.log(2) ** 2));
  }

  private calculateHashCount(m: number, n: number): number {
    return Math.ceil((m / n) * Math.log(2));
  }
}
```

### 3.3 キャッシュマネージャー (REQ-SCALE-CACHE-*)

#### 3.3.1 マルチレベルキャッシュ

```typescript
interface CacheManager {
  // 基本操作
  get<T>(key: string): Promise<T | undefined>;
  set<T>(key: string, value: T, options?: CacheOptions): Promise<void>;
  delete(key: string): Promise<boolean>;
  
  // 無効化
  invalidate(pattern: string): Promise<number>;
  invalidateByTags(tags: string[]): Promise<number>;
  
  // プリウォーミング
  warmup(keys: string[]): Promise<void>;
  
  // 統計
  getStats(): Promise<CacheStats>;
}

interface CacheStats {
  l1Hits: number;
  l2Hits: number;
  l3Hits: number;
  misses: number;
  hitRate: number;
  memoryUsage: number;
}

class MultiLevelCache implements CacheManager {
  private l1: LRUCache<string, unknown>;           // Hot: In-memory
  private l2: CompressedCache<string, unknown>;    // Warm: Compressed memory
  private l3: DiskCache<string, unknown>;          // Cold: Disk-based

  async get<T>(key: string): Promise<T | undefined> {
    // L1チェック
    const l1Value = this.l1.get(key);
    if (l1Value !== undefined) {
      this.stats.l1Hits++;
      return l1Value as T;
    }

    // L2チェック
    const l2Value = await this.l2.get(key);
    if (l2Value !== undefined) {
      this.stats.l2Hits++;
      this.promoteToL1(key, l2Value);
      return l2Value as T;
    }

    // L3チェック
    const l3Value = await this.l3.get(key);
    if (l3Value !== undefined) {
      this.stats.l3Hits++;
      this.promoteToL2(key, l3Value);
      return l3Value as T;
    }

    this.stats.misses++;
    return undefined;
  }

  async set<T>(key: string, value: T, options?: CacheOptions): Promise<void> {
    const tier = this.determineTier(options);
    
    switch (tier) {
      case 'l1':
        this.l1.set(key, value);
        break;
      case 'l2':
        await this.l2.set(key, value);
        break;
      case 'l3':
        await this.l3.set(key, value);
        break;
    }

    if (options?.tags) {
      await this.tagIndex.addTags(key, options.tags);
    }
  }

  async invalidate(pattern: string): Promise<number> {
    let count = 0;
    const regex = new RegExp(pattern.replace('*', '.*'));

    for (const key of this.l1.keys()) {
      if (regex.test(key)) {
        this.l1.delete(key);
        count++;
      }
    }

    count += await this.l2.invalidate(regex);
    count += await this.l3.invalidate(regex);

    return count;
  }
}
```

### 3.4 クエリコーディネーター (REQ-SCALE-PARALLEL-*)

#### 3.4.1 分散クエリ実行

```typescript
interface QueryCoordinator {
  // クエリ実行
  execute(query: GraphQuery, options?: QueryOptions): Promise<QueryResult>;
  executeStream(query: GraphQuery, options?: QueryOptions): AsyncIterable<Entity>;
  
  // 実行計画
  explain(query: GraphQuery): Promise<QueryPlan>;
  
  // バッチ処理
  batchExecute(queries: GraphQuery[]): Promise<QueryResult[]>;
}

interface QueryPlan {
  steps: QueryStep[];
  estimatedCost: number;
  shards: string[];
  parallelizable: boolean;
}

class QueryCoordinatorImpl implements QueryCoordinator {
  private planner: QueryPlanner;
  private executor: DistributedExecutor;
  private merger: ResultMerger;

  async execute(query: GraphQuery, options?: QueryOptions): Promise<QueryResult> {
    // 1. クエリプランニング
    const plan = await this.planner.plan(query);

    // 2. キャッシュチェック
    const cacheKey = this.computeCacheKey(query);
    const cached = await this.cache.get<QueryResult>(cacheKey);
    if (cached) return cached;

    // 3. 分散実行
    const shardResults = await this.executor.execute(plan);

    // 4. 結果マージ
    const result = await this.merger.merge(shardResults, query);

    // 5. キャッシュ保存
    await this.cache.set(cacheKey, result, {
      ttl: options?.cacheTtl ?? 60000,
      tags: this.extractCacheTags(query),
    });

    return result;
  }

  async *executeStream(
    query: GraphQuery,
    options?: QueryOptions
  ): AsyncIterable<Entity> {
    const plan = await this.planner.plan(query);

    // パイプライン処理
    const pipeline = new QueryPipeline(plan);
    
    for await (const batch of pipeline.execute()) {
      for (const entity of batch) {
        yield entity;
      }
    }
  }
}

class DistributedExecutor {
  private workerPool: WorkerPool;

  async execute(plan: QueryPlan): Promise<Map<string, ShardResult>> {
    const tasks = plan.shards.map(shardId => ({
      shardId,
      steps: this.filterStepsForShard(plan.steps, shardId),
    }));

    // 並列実行
    const results = await Promise.all(
      tasks.map(task =>
        this.workerPool.submit(async worker => {
          const shard = await this.getShardConnection(task.shardId);
          return shard.executeSteps(task.steps);
        })
      )
    );

    return new Map(tasks.map((t, i) => [t.shardId, results[i]]));
  }
}
```

### 3.5 同期コントローラー (REQ-SCALE-SYNC-*)

#### 3.5.1 増分同期

```typescript
interface SyncController {
  // 同期開始
  startSync(remote: string, options?: SyncOptions): Promise<SyncSession>;
  stopSync(sessionId: string): Promise<void>;
  
  // 状態取得
  getSyncStatus(sessionId: string): Promise<SyncStatus>;
  
  // コンフリクト解決
  resolveConflict(conflictId: string, resolution: ConflictResolution): Promise<void>;
}

interface SyncSession {
  sessionId: string;
  remote: string;
  status: 'syncing' | 'idle' | 'conflict' | 'error';
  lastSyncTime: Date;
  pendingChanges: number;
}

class SyncControllerImpl implements SyncController {
  private wal: WriteAheadLog;
  private vectorClock: VectorClock;
  private conflictResolver: ConflictResolver;

  async startSync(remote: string, options?: SyncOptions): Promise<SyncSession> {
    const session = await this.createSession(remote);

    // 1. 初期同期（差分計算）
    const localVersion = await this.vectorClock.current();
    const remoteVersion = await this.fetchRemoteVersion(remote);
    
    const delta = this.vectorClock.compare(localVersion, remoteVersion);

    // 2. 双方向同期
    if (delta.needsPull) {
      await this.pullChanges(remote, delta.pullFrom);
    }
    if (delta.needsPush) {
      await this.pushChanges(remote, delta.pushFrom);
    }

    // 3. リアルタイム同期開始
    this.startRealtimeSync(session);

    return session;
  }

  private async pullChanges(remote: string, fromVersion: VectorClockValue): Promise<void> {
    const changes = await this.fetchChanges(remote, fromVersion);
    
    for (const change of changes) {
      const conflict = await this.detectConflict(change);
      if (conflict) {
        await this.handleConflict(conflict, change);
      } else {
        await this.applyChange(change);
      }
    }
  }

  private async handleConflict(
    conflict: Conflict,
    change: Change
  ): Promise<void> {
    const resolution = await this.conflictResolver.resolve(conflict, {
      strategy: this.options.conflictStrategy ?? 'last-write-wins',
    });

    switch (resolution.action) {
      case 'accept-local':
        // ローカルを保持
        break;
      case 'accept-remote':
        await this.applyChange(change);
        break;
      case 'merge':
        await this.applyChange(resolution.mergedChange);
        break;
      case 'manual':
        await this.queueConflict(conflict);
        break;
    }
  }
}

class VectorClock {
  private clock: Map<string, number> = new Map();

  increment(nodeId: string): void {
    const current = this.clock.get(nodeId) ?? 0;
    this.clock.set(nodeId, current + 1);
  }

  compare(other: VectorClock): 'before' | 'after' | 'concurrent' {
    let before = false;
    let after = false;

    for (const [node, time] of this.clock) {
      const otherTime = other.clock.get(node) ?? 0;
      if (time < otherTime) before = true;
      if (time > otherTime) after = true;
    }

    for (const [node, otherTime] of other.clock) {
      if (!this.clock.has(node) && otherTime > 0) before = true;
    }

    if (before && !after) return 'before';
    if (after && !before) return 'after';
    return 'concurrent';
  }
}
```

---

## 4. パッケージ構造

```
packages/yata-scale/
├── package.json
├── tsconfig.json
├── vitest.config.ts
├── src/
│   ├── index.ts                    # メインエクスポート
│   ├── types.ts                    # 型定義
│   ├── errors.ts                   # エラークラス（下記参照）
│   │
│   ├── shard/                      # シャード管理
│   │   ├── index.ts
│   │   ├── ShardManager.ts
│   │   ├── PartitionStrategy.ts
│   │   ├── ShardRouter.ts
│   │   ├── Rebalancer.ts
│   │   └── FailoverHandler.ts
│   │
│   ├── index/                      # インデックスエンジン
│   │   ├── index.ts
│   │   ├── BPlusTreeIndex.ts
│   │   ├── FullTextIndex.ts
│   │   ├── GraphIndex.ts
│   │   ├── BloomFilter.ts
│   │   └── IndexCompactor.ts
│   │
│   ├── cache/                      # キャッシュ管理
│   │   ├── index.ts
│   │   ├── CacheManager.ts
│   │   ├── L1Cache.ts
│   │   ├── L2Cache.ts
│   │   ├── L3Cache.ts
│   │   ├── InvalidationManager.ts
│   │   └── CacheWarmer.ts
│   │
│   ├── query/                      # クエリ処理
│   │   ├── index.ts
│   │   ├── QueryCoordinator.ts
│   │   ├── QueryPlanner.ts
│   │   ├── DistributedExecutor.ts
│   │   ├── ResultMerger.ts
│   │   ├── WorkerPool.ts
│   │   └── Pipeline.ts
│   │
│   ├── sync/                       # 同期・レプリケーション
│   │   ├── index.ts
│   │   ├── SyncController.ts
│   │   ├── VectorClock.ts
│   │   ├── ConflictResolver.ts
│   │   ├── WALManager.ts
│   │   ├── ReplicationController.ts
│   │   └── OfflineQueue.ts
│   │
│   ├── storage/                    # ストレージ
│   │   ├── index.ts
│   │   ├── StorageEngine.ts
│   │   ├── MemoryMappedFile.ts
│   │   ├── Compressor.ts
│   │   └── Compactor.ts
│   │
│   └── integration/                # 統合
│       ├── index.ts
│       ├── YataScaleManager.ts
│       └── MigrationHelper.ts
│
└── tests/
    ├── shard/
    ├── index/
    ├── cache/
    ├── query/
    ├── sync/
    └── integration/
```

---

## 5. API設計

### 5.1 エラー型定義

```typescript
// 基底エラークラス
export class YataScaleError extends Error {
  constructor(
    message: string,
    public readonly code: string,
    public readonly cause?: Error
  ) {
    super(message);
    this.name = 'YataScaleError';
  }
}

// シャード関連エラー
export class ShardError extends YataScaleError {
  constructor(message: string, public readonly shardId: string, cause?: Error) {
    super(message, 'SHARD_ERROR', cause);
    this.name = 'ShardError';
  }
}

export class ShardNotFoundError extends ShardError {
  constructor(shardId: string) {
    super(`Shard not found: ${shardId}`, shardId);
    this.name = 'ShardNotFoundError';
  }
}

export class ShardUnavailableError extends ShardError {
  constructor(shardId: string, cause?: Error) {
    super(`Shard unavailable: ${shardId}`, shardId, cause);
    this.name = 'ShardUnavailableError';
  }
}

// インデックス関連エラー
export class IndexError extends YataScaleError {
  constructor(message: string, public readonly indexName: string, cause?: Error) {
    super(message, 'INDEX_ERROR', cause);
    this.name = 'IndexError';
  }
}

export class IndexCorruptedError extends IndexError {
  constructor(indexName: string) {
    super(`Index corrupted: ${indexName}`, indexName);
    this.name = 'IndexCorruptedError';
  }
}

// キャッシュ関連エラー
export class CacheError extends YataScaleError {
  constructor(message: string, cause?: Error) {
    super(message, 'CACHE_ERROR', cause);
    this.name = 'CacheError';
  }
}

// 同期関連エラー
export class SyncError extends YataScaleError {
  constructor(message: string, cause?: Error) {
    super(message, 'SYNC_ERROR', cause);
    this.name = 'SyncError';
  }
}

export class ConflictError extends SyncError {
  constructor(
    public readonly entityId: string,
    public readonly localVersion: number,
    public readonly remoteVersion: number
  ) {
    super(`Conflict detected for entity ${entityId}: local=${localVersion}, remote=${remoteVersion}`);
    this.name = 'ConflictError';
  }
}

// クエリ関連エラー
export class QueryError extends YataScaleError {
  constructor(message: string, cause?: Error) {
    super(message, 'QUERY_ERROR', cause);
    this.name = 'QueryError';
  }
}

export class QueryTimeoutError extends QueryError {
  constructor(public readonly timeoutMs: number) {
    super(`Query timed out after ${timeoutMs}ms`);
    this.name = 'QueryTimeoutError';
  }
}
```

### 5.2 メインAPI

```typescript
// YataScaleの作成
const scale = createYataScale({
  shards: [
    { id: 'shard-0', type: 'local', path: './data/shard-0' },
    { id: 'shard-1', type: 'local', path: './data/shard-1' },
  ],
  partitionStrategy: 'hash',
  cache: {
    l1Size: 1000,
    l2Size: 10000,
    l3Path: './cache',
  },
  sync: {
    enabled: true,
    remote: 'https://yata-global.example.com',
  },
});

// 初期化
await scale.initialize();

// エンティティ追加（自動シャーディング）
await scale.addEntity({
  type: 'class',
  name: 'UserService',
  namespace: 'app.services',
});

// 分散クエリ
const result = await scale.query({
  entityFilters: { types: ['class'] },
  textSearch: 'Service',
});

// シャード管理
const stats = await scale.getShardStats();
await scale.rebalanceShards();

// 同期
await scale.startSync();
const syncStatus = await scale.getSyncStatus();

// クリーンアップ
await scale.close();
```

---

## 6. 性能目標

REQ-YATA-SCALE-001の性能要件に基づく設計目標：

| 項目 | 目標値 | 設計対応 |
|------|--------|---------|
| 単一エンティティ取得 | < 1ms p99 | L1キャッシュ + B+Treeインデックス |
| 属性フィルタクエリ | < 10ms p99 | 複合インデックス + ブルームフィルタ |
| k-hopトラバーサル (k≤3) | < 50ms p99 | グラフインデックス + 並列実行 |
| パス検索クエリ | < 100ms p99 | 双方向BFS + キャッシュ |
| 読み取りQPS | ≥ 10,000 | ワーカープール + パイプライン |
| 書き込みOPS | ≥ 1,000 | WALバッファリング + 非同期I/O |
| メモリ (1Mエンティティ) | < 4GB | mmap + LRUキャッシュ + 圧縮 |
| 最大エンティティ数 | 100M+ | 水平シャーディング (最大100シャード) |
| 可用性 | 99.9% | レプリケーション + 自動フェイルオーバー |

---

## 7. トレーサビリティマトリクス

| 要件ID | 設計コンポーネント |
|--------|-------------------|
| REQ-SCALE-DIST-001 | PartitionStrategy, ShardManager |
| REQ-SCALE-DIST-002 | ShardManager, Rebalancer, FailoverHandler |
| REQ-SCALE-DIST-003 | QueryCoordinator, DistributedExecutor |
| REQ-SCALE-INDEX-001 | BPlusTreeIndex |
| REQ-SCALE-INDEX-002 | FullTextIndex |
| REQ-SCALE-INDEX-003 | GraphIndex |
| REQ-SCALE-INDEX-004 | BloomFilter |
| REQ-SCALE-CACHE-001 | CacheManager, L1/L2/L3Cache |
| REQ-SCALE-CACHE-002 | InvalidationManager |
| REQ-SCALE-CACHE-003 | CacheWarmer |
| REQ-SCALE-PARALLEL-001 | WorkerPool, DistributedExecutor |
| REQ-SCALE-PARALLEL-002 | Pipeline |
| REQ-SCALE-PARALLEL-003 | StorageEngine (async I/O) |
| REQ-SCALE-SYNC-001 | SyncController, VectorClock |
| REQ-SCALE-SYNC-002 | ReplicationController |
| REQ-SCALE-SYNC-003 | OfflineQueue |
| REQ-SCALE-MEM-001 | MemoryMappedFile |
| REQ-SCALE-MEM-002 | Compressor |
| REQ-SCALE-MEM-003 | Compactor |

---

## 7. レビュー記録

| 日付 | レビュアー | ステータス | コメント |
|------|-----------|-----------|---------|
| 2026-01-08 | AI Review | APPROVED | 全要件カバー確認、開発着手可 |

---

## 変更履歴

| バージョン | 日付 | 変更内容 |
|-----------|------|---------|
| 1.0.0 | 2026-01-08 | 初版作成 |
