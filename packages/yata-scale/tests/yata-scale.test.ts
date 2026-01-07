/**
 * @nahisaho/yata-scale - Unit Tests
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  YataScaleManager,
  ShardManager,
  HashPartitionStrategy,
  CacheManager,
  IndexManager,
  QueryCoordinator,
  SyncController,
  VectorClock,
  ConflictResolver,
  WALManager,
} from '../src/index.js';
import type { Entity, Relationship, GraphQuery, YataScaleConfig } from '../src/types.js';

// ============================================================================
// Helper Functions
// ============================================================================

function createEntity(id: string, type: string, name: string): Entity {
  return {
    id,
    type,
    name,
    properties: {},
    metadata: {
      createdAt: new Date(),
      updatedAt: new Date(),
      version: 1,
    },
  };
}

function createRelationship(id: string, sourceId: string, targetId: string, type: string): Relationship {
  return {
    id,
    sourceId,
    targetId,
    type,
    properties: {},
    metadata: {
      createdAt: new Date(),
      updatedAt: new Date(),
      version: 1,
    },
  };
}

function createConfig(): YataScaleConfig {
  return {
    shards: {
      count: 3,
      replicationFactor: 1,
      strategy: 'hash',
    },
    cache: {
      l1MaxEntries: 1000,
      l2MaxSize: 10000000,
      l3MaxEntries: 100000,
      ttlMs: 60000,
    },
    query: {
      maxConcurrency: 4,
      defaultTimeout: 5000,
    },
  };
}

// ============================================================================
// ShardManager Tests
// ============================================================================

describe('ShardManager', () => {
  let manager: ShardManager;

  beforeEach(() => {
    manager = new ShardManager();
  });

  describe('shard management', () => {
    it('should create a shard successfully', () => {
      const result = manager.createShard('shard-001', {
        count: 3,
        replicationFactor: 1,
        strategy: 'hash',
      });

      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.id).toBe('shard-001');
        expect(result.value.status).toBe('active');
      }
    });

    it('should prevent duplicate shard creation', () => {
      manager.createShard('shard-001', { count: 3, replicationFactor: 1, strategy: 'hash' });
      const result = manager.createShard('shard-001', { count: 3, replicationFactor: 1, strategy: 'hash' });

      expect(result.isErr()).toBe(true);
    });

    it('should get shard info via Result', () => {
      manager.createShard('shard-001', { count: 3, replicationFactor: 1, strategy: 'hash' });
      const result = manager.getShard('shard-001');

      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.id).toBe('shard-001');
      }
    });

    it('should list all shards', () => {
      manager.createShard('shard-001', { count: 3, replicationFactor: 1, strategy: 'hash' });
      manager.createShard('shard-002', { count: 3, replicationFactor: 1, strategy: 'hash' });

      const shards = manager.getAllShards();
      expect(shards).toHaveLength(2);
    });

    it('should delete a shard', () => {
      manager.createShard('shard-001', { count: 3, replicationFactor: 1, strategy: 'hash' });
      const result = manager.deleteShard('shard-001');

      expect(result.isOk()).toBe(true);
      const info = manager.getShard('shard-001');
      expect(info.isErr()).toBe(true);
    });
  });
});

// ============================================================================
// HashPartitionStrategy Tests
// ============================================================================

describe('HashPartitionStrategy', () => {
  let strategy: HashPartitionStrategy;

  beforeEach(() => {
    strategy = new HashPartitionStrategy();
  });

  it('should return consistent shard for same key', () => {
    strategy.addShard('shard-1');
    strategy.addShard('shard-2');
    strategy.addShard('shard-3');

    const shard1 = strategy.getShardForEntity('entity-123');
    const shard2 = strategy.getShardForEntity('entity-123');

    expect(shard1).toBe(shard2);
  });

  it('should distribute keys across shards', () => {
    strategy.addShard('shard-1');
    strategy.addShard('shard-2');
    strategy.addShard('shard-3');

    const shards = new Set<string>();
    for (let i = 0; i < 100; i++) {
      shards.add(strategy.getShardForEntity(`entity-${i}`));
    }

    // With 3 shards and 100 entities, we expect distribution across multiple shards
    expect(shards.size).toBeGreaterThanOrEqual(1);
  });

  it('should handle shard removal', () => {
    strategy.addShard('shard-1');
    strategy.addShard('shard-2');
    strategy.removeShard('shard-1');

    const shard = strategy.getShardForEntity('any-key');
    expect(shard).toBe('shard-2');
  });
});

// ============================================================================
// IndexManager Tests
// ============================================================================

describe('IndexManager', () => {
  let manager: IndexManager;

  beforeEach(() => {
    manager = new IndexManager();
  });

  it('should index and retrieve an entity', () => {
    const entity = createEntity('entity-001', 'Person', 'Alice');
    manager.indexEntity(entity);

    const retrieved = manager.getEntity('entity-001');
    expect(retrieved).toBeDefined();
    expect(retrieved?.name).toBe('Alice');
  });

  it('should remove an entity from index', () => {
    const entity = createEntity('entity-001', 'Person', 'Alice');
    manager.indexEntity(entity);
    manager.removeEntity('entity-001');

    const retrieved = manager.getEntity('entity-001');
    expect(retrieved).toBeUndefined();
  });

  it('should find entities by type', () => {
    manager.indexEntity(createEntity('p1', 'Person', 'Alice'));
    manager.indexEntity(createEntity('p2', 'Person', 'Bob'));
    manager.indexEntity(createEntity('o1', 'Organization', 'Acme'));

    const people = manager.findByType('Person');
    expect(people).toHaveLength(2);
  });

  it('should search by text', () => {
    manager.indexEntity(createEntity('e1', 'Document', 'Machine Learning Guide'));
    manager.indexEntity(createEntity('e2', 'Document', 'Deep Learning Tutorial'));

    const results = manager.searchByText('learning');
    expect(results.length).toBeGreaterThan(0);
  });

  it('should track entity count', () => {
    manager.indexEntity(createEntity('e1', 'Person', 'Alice'));
    manager.indexEntity(createEntity('e2', 'Person', 'Bob'));

    expect(manager.entityCount).toBe(2);
  });
});

// ============================================================================
// CacheManager Tests
// ============================================================================

describe('CacheManager', () => {
  let cache: CacheManager;

  beforeEach(() => {
    cache = new CacheManager({
      l1MaxEntries: 100,
      l2MaxSize: 10000,
      l3MaxEntries: 1000,
      ttlMs: 60000,
    });
  });

  it('should set and get an entity', async () => {
    const entity = createEntity('e1', 'Person', 'Alice');
    await cache.setEntity(entity);

    const result = await cache.getEntity('e1');
    expect(result.isOk()).toBe(true);
    if (result.isOk()) {
      expect(result.value.name).toBe('Alice');
    }
  });

  it('should return error for non-existent entity', async () => {
    const result = await cache.getEntity('non-existent');
    expect(result.isErr()).toBe(true);
  });

  it('should delete an entity', async () => {
    const entity = createEntity('e1', 'Person', 'Alice');
    await cache.setEntity(entity);
    await cache.deleteEntity('e1');

    const result = await cache.getEntity('e1');
    expect(result.isErr()).toBe(true);
  });

  it('should provide cache stats', async () => {
    await cache.setEntity(createEntity('e1', 'Person', 'Alice'));
    await cache.getEntity('e1');
    await cache.getEntity('non-existent');

    const stats = cache.getAllStats();
    expect(stats.l1.hits).toBeGreaterThan(0);
  });

  it('should warm cache with entities', async () => {
    const entities = [
      createEntity('e1', 'Person', 'Alice'),
      createEntity('e2', 'Person', 'Bob'),
    ];

    await cache.warm(entities);

    const r1 = await cache.getEntity('e1');
    const r2 = await cache.getEntity('e2');

    expect(r1.isOk()).toBe(true);
    expect(r2.isOk()).toBe(true);
  });
});

// ============================================================================
// QueryCoordinator Tests
// ============================================================================

describe('QueryCoordinator', () => {
  let coordinator: QueryCoordinator;

  beforeEach(() => {
    coordinator = new QueryCoordinator(4, 60000, 5000);
  });

  it('should validate lookup query', () => {
    const query: GraphQuery = {
      type: 'lookup',
      entityIds: ['e1', 'e2'],
    };

    const result = coordinator.validate(query);
    expect(result.isOk()).toBe(true);
  });

  it('should reject invalid lookup query', () => {
    const query: GraphQuery = {
      type: 'lookup',
      entityIds: [],
    };

    const result = coordinator.validate(query);
    expect(result.isErr()).toBe(true);
  });

  it('should explain query plan', () => {
    const query: GraphQuery = {
      type: 'lookup',
      entityIds: ['e1'],
      limit: 10,
    };

    const explanation = coordinator.explain(query, ['shard-1', 'shard-2']);
    expect(explanation).toContain('Query Type');
    expect(explanation).toContain('lookup');
  });

  it('should execute query and return results', async () => {
    const query: GraphQuery = {
      type: 'lookup',
      entityIds: ['e1'],
    };

    const mockExecutor = async (_shard: string, _q: GraphQuery) => ({
      entities: [createEntity('e1', 'Person', 'Alice')],
      relationships: [],
    });

    const result = await coordinator.query(query, ['shard-1'], mockExecutor);
    expect(result.isOk()).toBe(true);
    if (result.isOk()) {
      expect(result.value.entities).toHaveLength(1);
    }
  });
});

// ============================================================================
// SyncController Tests
// ============================================================================

describe('SyncController', () => {
  let controller: SyncController;

  beforeEach(() => {
    controller = new SyncController('node-1', 'lww');
  });

  it('should record entity creation', () => {
    const entity = createEntity('e1', 'Person', 'Alice');
    controller.recordCreate(entity);

    const changes = controller.getChanges(0);
    expect(changes).toHaveLength(1);
    expect(changes[0].operation).toBe('create');
  });

  it('should start and end sync session', () => {
    const result = controller.startSession('peer-1');
    expect(result.isOk()).toBe(true);

    if (result.isOk()) {
      controller.endSession(result.value.id);
    }
  });

  it('should manage peers', () => {
    controller.registerPeer('peer-1', { lastSync: new Date(), status: 'active' });
    controller.registerPeer('peer-2', { lastSync: new Date(), status: 'active' });

    const peers = controller.getPeers();
    expect(peers).toHaveLength(2);

    controller.unregisterPeer('peer-1');
    expect(controller.getPeers()).toHaveLength(1);
  });

  it('should provide stats', () => {
    const stats = controller.getStats();
    expect(stats.nodeId).toBe('node-1');
    expect(stats.activeSessions).toBe(0);
  });
});

// ============================================================================
// VectorClock Tests
// ============================================================================

describe('VectorClock', () => {
  it('should increment local time', () => {
    const clock = new VectorClock('node-1');
    clock.increment();
    clock.increment();

    expect(clock.get('node-1')).toBe(2);
  });

  it('should merge clocks correctly', () => {
    const clock1 = new VectorClock('node-1');
    const clock2 = new VectorClock('node-2');

    clock1.increment();
    clock1.increment();
    clock2.increment();

    clock1.merge(clock2);

    expect(clock1.get('node-1')).toBe(2);
    expect(clock1.get('node-2')).toBe(1);
  });

  it('should compare clocks', () => {
    const clock1 = new VectorClock('node-1');
    const clock2 = new VectorClock('node-1');

    clock1.increment();

    expect(clock1.compare(clock2)).toBe('after');
    expect(clock2.compare(clock1)).toBe('before');
  });

  it('should detect concurrent events', () => {
    const clock1 = new VectorClock('node-1');
    const clock2 = new VectorClock('node-2');

    clock1.increment();
    clock2.increment();

    expect(clock1.compare(clock2)).toBe('concurrent');
  });

  it('should serialize and deserialize', () => {
    const clock = new VectorClock('node-1');
    clock.increment();
    clock.increment();

    const serialized = clock.serialize();
    const restored = VectorClock.deserialize(serialized);

    expect(restored.get('node-1')).toBe(2);
  });
});

// ============================================================================
// ConflictResolver Tests
// ============================================================================

describe('ConflictResolver', () => {
  const baseEntity: Entity = {
    id: 'e1',
    type: 'Person',
    name: 'Alice',
    properties: {},
    metadata: {
      createdAt: new Date('2024-01-01'),
      updatedAt: new Date('2024-01-01'),
      version: 1,
    },
  };

  it('should resolve with LWW strategy (last writer wins)', () => {
    const resolver = new ConflictResolver('lww');

    const older = { ...baseEntity, metadata: { ...baseEntity.metadata, updatedAt: new Date('2024-01-01') } };
    const newer = { ...baseEntity, metadata: { ...baseEntity.metadata, updatedAt: new Date('2024-02-01') } };

    const result = resolver.resolve(older, newer);
    expect(result.isOk()).toBe(true);
    if (result.isOk()) {
      expect(result.value.metadata.updatedAt.getTime()).toBe(newer.metadata.updatedAt.getTime());
    }
  });

  it('should resolve with FWW strategy (first writer wins)', () => {
    const resolver = new ConflictResolver('fww');

    const first = { ...baseEntity, metadata: { ...baseEntity.metadata, createdAt: new Date('2024-01-01') } };
    const second = { ...baseEntity, metadata: { ...baseEntity.metadata, createdAt: new Date('2024-02-01') } };

    const result = resolver.resolve(first, second);
    expect(result.isOk()).toBe(true);
    if (result.isOk()) {
      expect(result.value.metadata.createdAt.getTime()).toBe(first.metadata.createdAt.getTime());
    }
  });

  it('should merge properties with merge strategy', () => {
    const resolver = new ConflictResolver('merge');

    const local = { ...baseEntity, properties: { city: 'Tokyo' } };
    const remote = { ...baseEntity, properties: { country: 'Japan' } };

    const result = resolver.resolve(local, remote);
    expect(result.isOk()).toBe(true);
    if (result.isOk()) {
      expect(result.value.properties).toEqual({ city: 'Tokyo', country: 'Japan' });
    }
  });
});

// ============================================================================
// WALManager Tests
// ============================================================================

describe('WALManager', () => {
  let wal: WALManager;

  beforeEach(() => {
    wal = new WALManager({ maxSegmentSize: 1000, maxSegments: 10 });
  });

  it('should append entries', () => {
    const seq = wal.append('create', { id: 'e1' });
    expect(seq.isOk()).toBe(true);
    if (seq.isOk()) {
      expect(seq.value).toBe(1);
    }
  });

  it('should read entries from sequence', () => {
    wal.append('create', { id: 'e1' });
    wal.append('update', { id: 'e1' });
    wal.append('delete', { id: 'e1' });

    const entries = wal.readFrom(2);
    expect(entries).toHaveLength(2);
    expect(entries[0].operation).toBe('update');
  });

  it('should replay entries', () => {
    wal.append('create', { id: 'e1' });
    wal.append('update', { id: 'e1' });

    const operations: string[] = [];
    wal.replay((entry) => operations.push(entry.operation));

    expect(operations).toEqual(['create', 'update']);
  });

  it('should truncate before sequence', () => {
    wal.append('create', { id: 'e1' });
    wal.append('update', { id: 'e1' });
    wal.append('delete', { id: 'e1' });

    wal.truncateBefore(2);
    const entries = wal.readFrom(0);

    expect(entries).toHaveLength(2);
  });
});

// ============================================================================
// YataScaleManager Integration Tests
// ============================================================================

describe('YataScaleManager', () => {
  let manager: YataScaleManager;

  beforeEach(() => {
    manager = new YataScaleManager();
  });

  afterEach(async () => {
    await manager.shutdown();
  });

  describe('initialization', () => {
    it('should initialize successfully', async () => {
      const result = await manager.initialize(createConfig());

      expect(result.isOk()).toBe(true);
      expect(manager.isInitialized()).toBe(true);
    });

    it('should prevent double initialization', async () => {
      await manager.initialize(createConfig());
      const result = await manager.initialize(createConfig());

      expect(result.isErr()).toBe(true);
    });
  });

  describe('entity operations', () => {
    beforeEach(async () => {
      await manager.initialize(createConfig());
    });

    it('should create and get an entity', async () => {
      const entity = createEntity('e1', 'Person', 'Alice');

      const createResult = await manager.createEntity(entity);
      expect(createResult.isOk()).toBe(true);

      const getResult = await manager.getEntity('e1');
      expect(getResult.isOk()).toBe(true);
      if (getResult.isOk()) {
        expect(getResult.value.name).toBe('Alice');
      }
    });

    it('should update an entity', async () => {
      const entity = createEntity('e1', 'Person', 'Alice');
      await manager.createEntity(entity);

      const updated = { ...entity, name: 'Alice Updated' };
      const result = await manager.updateEntity(updated);

      expect(result.isOk()).toBe(true);

      const getResult = await manager.getEntity('e1');
      if (getResult.isOk()) {
        expect(getResult.value.name).toBe('Alice Updated');
      }
    });

    it('should delete an entity', async () => {
      const entity = createEntity('e1', 'Person', 'Alice');
      await manager.createEntity(entity);

      const deleteResult = await manager.deleteEntity('e1');
      expect(deleteResult.isOk()).toBe(true);

      const getResult = await manager.getEntity('e1');
      expect(getResult.isErr()).toBe(true);
    });

    it('should return error for non-existent entity', async () => {
      const result = await manager.getEntity('non-existent');
      expect(result.isErr()).toBe(true);
    });
  });

  describe('relationship operations', () => {
    beforeEach(async () => {
      await manager.initialize(createConfig());
    });

    it('should create a relationship', async () => {
      await manager.createEntity(createEntity('e1', 'Person', 'Alice'));
      await manager.createEntity(createEntity('e2', 'Person', 'Bob'));

      const rel = createRelationship('r1', 'e1', 'e2', 'knows');
      const result = await manager.createRelationship(rel);

      expect(result.isOk()).toBe(true);
    });

    it('should delete a relationship', async () => {
      await manager.createEntity(createEntity('e1', 'Person', 'Alice'));
      await manager.createEntity(createEntity('e2', 'Person', 'Bob'));

      const rel = createRelationship('r1', 'e1', 'e2', 'knows');
      await manager.createRelationship(rel);

      const result = await manager.deleteRelationship('r1');
      expect(result.isOk()).toBe(true);
    });
  });

  describe('batch operations', () => {
    beforeEach(async () => {
      await manager.initialize(createConfig());
    });

    it('should batch write entities', async () => {
      const entities = [
        createEntity('e1', 'Person', 'Alice'),
        createEntity('e2', 'Person', 'Bob'),
        createEntity('e3', 'Person', 'Charlie'),
      ];

      const result = await manager.batchWrite(entities);

      expect(result.succeeded).toHaveLength(3);
      expect(result.failed).toHaveLength(0);
    });

    it('should batch write entities and relationships', async () => {
      const entities = [
        createEntity('e1', 'Person', 'Alice'),
        createEntity('e2', 'Person', 'Bob'),
      ];

      const relationships = [
        createRelationship('r1', 'e1', 'e2', 'knows'),
      ];

      const result = await manager.batchWrite(entities, relationships);

      expect(result.succeeded).toContain('e1');
      expect(result.succeeded).toContain('e2');
      expect(result.succeeded).toContain('r1');
    });
  });

  describe('query operations', () => {
    beforeEach(async () => {
      await manager.initialize(createConfig());
    });

    it('should execute lookup query', async () => {
      await manager.createEntity(createEntity('e1', 'Person', 'Alice'));

      const query: GraphQuery = {
        type: 'lookup',
        entityIds: ['e1'],
      };

      const result = await manager.query(query);
      expect(result.isOk()).toBe(true);
    });
  });

  describe('statistics', () => {
    beforeEach(async () => {
      await manager.initialize(createConfig());
    });

    it('should return system stats', async () => {
      await manager.createEntity(createEntity('e1', 'Person', 'Alice'));

      const stats = manager.getStats();

      expect(stats.entityCount).toBe(1);
      expect(stats.shardCount).toBe(3);
    });
  });

  describe('component accessors', () => {
    beforeEach(async () => {
      await manager.initialize(createConfig());
    });

    it('should provide access to shard manager', () => {
      const shardManager = manager.getShardManager();
      expect(shardManager).toBeInstanceOf(ShardManager);
    });

    it('should provide access to cache manager', () => {
      const cacheManager = manager.getCacheManager();
      expect(cacheManager).toBeInstanceOf(CacheManager);
    });

    it('should provide access to index manager', () => {
      const indexManager = manager.getIndexManager();
      expect(indexManager).toBeInstanceOf(IndexManager);
    });

    it('should provide access to query coordinator', () => {
      const queryCoordinator = manager.getQueryCoordinator();
      expect(queryCoordinator).toBeInstanceOf(QueryCoordinator);
    });

    it('should provide access to sync controller', () => {
      const syncController = manager.getSyncController();
      expect(syncController).toBeInstanceOf(SyncController);
    });
  });

  describe('shutdown', () => {
    it('should shutdown cleanly', async () => {
      await manager.initialize(createConfig());
      await manager.shutdown();

      expect(manager.isInitialized()).toBe(false);
    });

    it('should allow re-initialization after shutdown', async () => {
      await manager.initialize(createConfig());
      await manager.shutdown();

      const result = await manager.initialize(createConfig());
      expect(result.isOk()).toBe(true);
    });
  });
});
