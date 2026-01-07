# @nahisaho/yata-scale

YATA Knowledge Graph Scale-up Package - Distributed graph architecture, high-performance indexing, and multi-level caching for large-scale knowledge graphs.

## Features

- **Distributed Graph Architecture**: Hash/Range/Graph-based partitioning with automatic rebalancing
- **High-Performance Indexes**: B+Tree, Full-text, Graph indexes with Bloom filters
- **Multi-Level Cache**: L1 (hot), L2 (warm), L3 (cold) with automatic promotion/demotion
- **Parallel Query Processing**: Worker pool, pipelined execution, async I/O
- **Sync & Replication**: Vector clock, conflict resolution, offline support

## Installation

```bash
npm install @nahisaho/yata-scale
```

## Quick Start

```typescript
import { createYataScale } from '@nahisaho/yata-scale';

const scale = createYataScale({
  shards: [
    { id: 'shard-0', type: 'local', path: './data/shard-0' },
    { id: 'shard-1', type: 'local', path: './data/shard-1' },
  ],
  partitionStrategy: 'hash',
  cache: {
    l1Size: 1000,
    l2Size: 10000,
  },
});

await scale.initialize();

// Add entities (auto-sharding)
await scale.addEntity({
  type: 'class',
  name: 'UserService',
  namespace: 'app.services',
});

// Distributed query
const result = await scale.query({
  entityFilters: { types: ['class'] },
  textSearch: 'Service',
});

await scale.close();
```

## Performance Targets

| Metric | Target |
|--------|--------|
| Single entity lookup | < 1ms p99 |
| Complex graph queries | < 100ms p99 |
| Read QPS | ≥ 10,000 |
| Memory (1M entities) | < 4GB |
| Max entities | 100M+ |

## License

MIT
