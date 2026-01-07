/**
 * @nahisaho/yata-scale - Shard Manager
 * 
 * Manages sharding for distributed knowledge graph
 */

import { ok, err, type Result } from 'neverthrow';
import type { ShardConfig, ShardInfo, ShardStatus, RebalancePlan, Migration } from './types.js';
import { ShardNotFoundError, ShardError } from './errors.js';

/**
 * Hash-based partition strategy using consistent hashing
 */
export class HashPartitionStrategy {
  private readonly virtualNodes: number;
  private ring: Map<number, string> = new Map();
  private sortedKeys: number[] = [];
  private shards: Set<string> = new Set();

  constructor(virtualNodes = 150) {
    this.virtualNodes = virtualNodes;
  }

  private hash(key: string): number {
    let hash = 2166136261;
    for (let i = 0; i < key.length; i++) {
      hash ^= key.charCodeAt(i);
      hash = (hash * 16777619) >>> 0;
    }
    return hash;
  }

  addShard(shardId: string): void {
    if (this.shards.has(shardId)) return;
    this.shards.add(shardId);

    for (let i = 0; i < this.virtualNodes; i++) {
      const virtualKey = `${shardId}:${i}`;
      const hash = this.hash(virtualKey);
      this.ring.set(hash, shardId);
    }

    this.sortedKeys = Array.from(this.ring.keys()).sort((a, b) => a - b);
  }

  removeShard(shardId: string): void {
    if (!this.shards.has(shardId)) return;
    this.shards.delete(shardId);

    for (let i = 0; i < this.virtualNodes; i++) {
      const virtualKey = `${shardId}:${i}`;
      const hash = this.hash(virtualKey);
      this.ring.delete(hash);
    }

    this.sortedKeys = Array.from(this.ring.keys()).sort((a, b) => a - b);
  }

  getShardForEntity(entityId: string): string {
    if (this.sortedKeys.length === 0) {
      throw new Error('No shards available');
    }

    const hash = this.hash(entityId);
    let left = 0;
    let right = this.sortedKeys.length - 1;

    while (left < right) {
      const mid = Math.floor((left + right) / 2);
      if (this.sortedKeys[mid] < hash) {
        left = mid + 1;
      } else {
        right = mid;
      }
    }

    const key = this.sortedKeys[left] >= hash ? this.sortedKeys[left] : this.sortedKeys[0];
    return this.ring.get(key)!;
  }

  getAllShards(): string[] {
    return Array.from(this.shards);
  }
}

/**
 * Shard manager for distributed knowledge graph
 */
export class ShardManager {
  private shards: Map<string, ShardInfo> = new Map();
  private strategy: HashPartitionStrategy;

  constructor() {
    this.strategy = new HashPartitionStrategy();
  }

  createShard(shardId: string, _config: ShardConfig): Result<ShardInfo, ShardError> {
    if (this.shards.has(shardId)) {
      return err(new ShardError(`Shard ${shardId} already exists`, shardId));
    }

    const info: ShardInfo = {
      id: shardId,
      status: 'active',
      entityCount: 0,
      relationshipCount: 0,
      sizeBytes: 0,
      replicas: [],
      lastModified: new Date(),
      health: {
        healthy: true,
        latencyMs: 0,
        errorRate: 0,
        lastChecked: new Date(),
      },
    };

    this.shards.set(shardId, info);
    this.strategy.addShard(shardId);

    return ok(info);
  }

  getShard(shardId: string): Result<ShardInfo, ShardNotFoundError> {
    const shard = this.shards.get(shardId);
    if (!shard) {
      return err(new ShardNotFoundError(shardId));
    }
    return ok(shard);
  }

  deleteShard(shardId: string): Result<void, ShardNotFoundError> {
    if (!this.shards.has(shardId)) {
      return err(new ShardNotFoundError(shardId));
    }

    this.shards.delete(shardId);
    this.strategy.removeShard(shardId);
    return ok(undefined);
  }

  updateShardStatus(shardId: string, status: ShardStatus): Result<void, ShardNotFoundError> {
    const shard = this.shards.get(shardId);
    if (!shard) {
      return err(new ShardNotFoundError(shardId));
    }

    this.shards.set(shardId, { ...shard, status });
    return ok(undefined);
  }

  getShardForEntity(entityId: string): string {
    return this.strategy.getShardForEntity(entityId);
  }

  getAllShards(): string[] {
    return Array.from(this.shards.keys());
  }

  getStats(): { totalShards: number; totalEntities: number; healthyShards: number } {
    let totalEntities = 0;
    let healthyShards = 0;

    for (const shard of this.shards.values()) {
      totalEntities += shard.entityCount;
      if (shard.health.healthy) {
        healthyShards++;
      }
    }

    return {
      totalShards: this.shards.size,
      totalEntities,
      healthyShards,
    };
  }

  checkHealth(): { healthy: boolean; unhealthyShards: string[] } {
    const unhealthyShards: string[] = [];

    for (const [id, shard] of this.shards) {
      if (!shard.health.healthy) {
        unhealthyShards.push(id);
      }
    }

    return {
      healthy: unhealthyShards.length === 0,
      unhealthyShards,
    };
  }

  planRebalance(loads: Map<string, number>): RebalancePlan {
    const migrations: Migration[] = [];
    const sortedShards = Array.from(loads.entries()).sort((a, b) => b[1] - a[1]);

    if (sortedShards.length < 2) {
      return { migrations, estimatedDuration: 0, affectedEntities: 0 };
    }

    const avgLoad = Array.from(loads.values()).reduce((a, b) => a + b, 0) / loads.size;
    const threshold = avgLoad * 0.2;

    for (let i = 0; i < sortedShards.length; i++) {
      const [heavyId, heavyLoad] = sortedShards[i];
      if (heavyLoad <= avgLoad + threshold) break;

      for (let j = sortedShards.length - 1; j > i; j--) {
        const [lightId, lightLoad] = sortedShards[j];
        if (lightLoad >= avgLoad - threshold) continue;

        const toMove = Math.floor((heavyLoad - avgLoad) / 2);
        if (toMove > 0) {
          migrations.push({
            from: heavyId,
            to: lightId,
            entityIds: [`placeholder_${toMove}`],
          });
        }
      }
    }

    return {
      migrations,
      estimatedDuration: migrations.length * 1000,
      affectedEntities: migrations.reduce((sum, m) => sum + m.entityIds.length, 0),
    };
  }
}
