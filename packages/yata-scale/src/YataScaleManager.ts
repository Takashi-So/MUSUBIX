/**
 * @nahisaho/yata-scale - YataScale Manager
 * 
 * High-level manager for the entire yata-scale system
 */

import { ok, err, type Result } from 'neverthrow';
import type {
  YataScaleConfig,
  YataScaleStats,
  Entity,
  Relationship,
  GraphQuery,
  QueryResult,
  BatchWriteResult,
} from './types.js';
import {
  InitializationError,
  AlreadyInitializedError,
  NotInitializedError,
  EntityNotFoundError,
  EntityAlreadyExistsError,
  QueryError,
} from './errors.js';
import { ShardManager } from './ShardManager.js';
import { CacheManager } from './CacheManager.js';
import { IndexManager } from './IndexManager.js';
import { QueryCoordinator } from './QueryCoordinator.js';
import { SyncController } from './SyncController.js';

/**
 * YataScale manager - main entry point for the system
 */
export class YataScaleManager {
  private config: YataScaleConfig | null = null;
  private shardManager: ShardManager | null = null;
  private cache: CacheManager | null = null;
  private indexManager: IndexManager | null = null;
  private queryCoordinator: QueryCoordinator | null = null;
  private syncController: SyncController | null = null;
  private initialized = false;

  /**
   * Initialize the system
   */
  async initialize(config: YataScaleConfig): Promise<Result<void, InitializationError>> {
    if (this.initialized) {
      return err(new AlreadyInitializedError());
    }

    try {
      this.config = config;

      this.shardManager = new ShardManager();
      this.cache = new CacheManager(config.cache);
      this.indexManager = new IndexManager();
      this.queryCoordinator = new QueryCoordinator(
        config.query.maxConcurrency,
        60000,
        config.query.defaultTimeout
      );

      const nodeId = config.nodeId ?? `node_${Date.now()}`;
      this.syncController = new SyncController(nodeId);

      // Create shards
      for (let i = 0; i < config.shards.count; i++) {
        const shardId = `shard_${i}`;
        this.shardManager.createShard(shardId, config.shards);
      }

      this.initialized = true;
      return ok(undefined);
    } catch (error) {
      return err(
        new InitializationError(
          `Failed to initialize: ${error instanceof Error ? error.message : String(error)}`
        )
      );
    }
  }

  private ensureInitialized(): void {
    if (!this.initialized) {
      throw new NotInitializedError();
    }
  }

  /**
   * Create an entity
   */
  async createEntity(entity: Entity): Promise<Result<Entity, EntityAlreadyExistsError>> {
    this.ensureInitialized();

    const cached = await this.cache!.getEntity(entity.id);
    if (cached.isOk()) {
      return err(new EntityAlreadyExistsError(entity.id));
    }

    await this.cache!.setEntity(entity);
    this.indexManager!.indexEntity(entity);
    this.syncController!.recordCreate(entity);

    return ok(entity);
  }

  /**
   * Get an entity by ID
   */
  async getEntity(id: string): Promise<Result<Entity, EntityNotFoundError>> {
    this.ensureInitialized();

    const cached = await this.cache!.getEntity(id);
    if (cached.isOk()) {
      return ok(cached.value);
    }

    const indexed = this.indexManager!.getEntity(id);
    if (indexed) {
      await this.cache!.setEntity(indexed);
      return ok(indexed);
    }

    return err(new EntityNotFoundError(id));
  }

  /**
   * Update an entity
   */
  async updateEntity(entity: Entity): Promise<Result<Entity, EntityNotFoundError>> {
    this.ensureInitialized();

    const existing = await this.getEntity(entity.id);
    if (existing.isErr()) {
      return err(existing.error);
    }

    await this.cache!.setEntity(entity);
    this.indexManager!.removeEntity(entity.id);
    this.indexManager!.indexEntity(entity);
    this.syncController!.recordUpdate(entity, existing.value);

    return ok(entity);
  }

  /**
   * Delete an entity
   */
  async deleteEntity(id: string): Promise<Result<void, EntityNotFoundError>> {
    this.ensureInitialized();

    const existing = await this.getEntity(id);
    if (existing.isErr()) {
      return err(existing.error);
    }

    await this.cache!.deleteEntity(id);
    this.indexManager!.removeEntity(id);
    this.syncController!.recordDelete(id, existing.value);

    return ok(undefined);
  }

  /**
   * Create a relationship
   */
  async createRelationship(relationship: Relationship): Promise<Result<Relationship, Error>> {
    this.ensureInitialized();

    await this.cache!.setRelationship(relationship);
    this.indexManager!.indexRelationship(relationship);
    this.syncController!.recordRelationshipCreate(relationship);

    return ok(relationship);
  }

  /**
   * Delete a relationship
   */
  async deleteRelationship(id: string): Promise<Result<void, Error>> {
    this.ensureInitialized();

    await this.cache!.deleteRelationship(id);
    this.indexManager!.removeRelationship(id);
    this.syncController!.recordRelationshipDelete(id);

    return ok(undefined);
  }

  /**
   * Execute a query
   */
  async query(graphQuery: GraphQuery): Promise<Result<QueryResult, QueryError>> {
    this.ensureInitialized();

    const shards = this.shardManager!.getAllShards();

    const queryFn = async (_shardId: string, query: GraphQuery) => {
      const entities: Entity[] = [];
      const relationships: Relationship[] = [];

      if (query.startEntityIds) {
        for (const id of query.startEntityIds) {
          const entity = this.indexManager!.getEntity(id);
          if (entity) {
            entities.push(entity);
          }
        }
      }

      if (query.entityIds) {
        for (const id of query.entityIds) {
          const entity = this.indexManager!.getEntity(id);
          if (entity) {
            entities.push(entity);
          }
        }
      }

      return { entities, relationships };
    };

    return await this.queryCoordinator!.query(graphQuery, shards, queryFn);
  }

  /**
   * Batch write entities
   */
  async batchWrite(
    entities: Entity[],
    relationships: Relationship[] = []
  ): Promise<BatchWriteResult> {
    this.ensureInitialized();

    const succeeded: string[] = [];
    const failed: Array<{ id: string; error: string }> = [];
    const startTime = Date.now();

    for (const entity of entities) {
      const result = await this.createEntity(entity);
      if (result.isOk()) {
        succeeded.push(entity.id);
      } else {
        const updateResult = await this.updateEntity(entity);
        if (updateResult.isOk()) {
          succeeded.push(entity.id);
        } else {
          failed.push({ id: entity.id, error: updateResult.error.message });
        }
      }
    }

    for (const rel of relationships) {
      const result = await this.createRelationship(rel);
      if (result.isOk()) {
        succeeded.push(rel.id);
      } else {
        failed.push({ id: rel.id, error: result.error.message });
      }
    }

    return {
      succeeded,
      failed,
      totalTime: Date.now() - startTime,
    };
  }

  /**
   * Get system statistics
   */
  getStats(): YataScaleStats {
    this.ensureInitialized();

    const cacheStats = this.cache!.getAllStats();
    const indexStats = this.indexManager!.getAllStats();
    const syncStats = this.syncController!.getStats();
    const shardStats = this.shardManager!.getStats();

    return {
      entityCount: this.indexManager!.entityCount,
      relationshipCount: this.indexManager!.relationshipCount,
      shardCount: shardStats.totalShards,
      cacheStats: cacheStats.l1,
      indexStats: indexStats[0],
      syncStats: {
        nodeId: syncStats.nodeId,
        activeSessions: syncStats.activeSessions,
        walSequence: syncStats.walSequence,
      },
    };
  }

  getShardManager(): ShardManager {
    this.ensureInitialized();
    return this.shardManager!;
  }

  getCacheManager(): CacheManager {
    this.ensureInitialized();
    return this.cache!;
  }

  getIndexManager(): IndexManager {
    this.ensureInitialized();
    return this.indexManager!;
  }

  getQueryCoordinator(): QueryCoordinator {
    this.ensureInitialized();
    return this.queryCoordinator!;
  }

  getSyncController(): SyncController {
    this.ensureInitialized();
    return this.syncController!;
  }

  async shutdown(): Promise<void> {
    if (!this.initialized) {
      return;
    }

    await this.cache?.close();
    await this.queryCoordinator?.shutdown();

    this.initialized = false;
    this.config = null;
    this.shardManager = null;
    this.cache = null;
    this.indexManager = null;
    this.queryCoordinator = null;
    this.syncController = null;
  }

  isInitialized(): boolean {
    return this.initialized;
  }

  getConfig(): YataScaleConfig | null {
    return this.config;
  }
}
