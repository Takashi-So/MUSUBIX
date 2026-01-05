/**
 * YATA Local KGPR - Diff Engine
 *
 * Generates diffs between knowledge graph states
 *
 * @packageDocumentation
 * @module @nahisaho/yata-local/kgpr
 *
 * @see REQ-YL-EXT-KGPR-003
 */

import { createHash } from 'crypto';
import type { Entity, Relationship, EntityType, RelationType } from '../types.js';
import type {
  LocalEntityChange,
  LocalRelationshipChange,
  LocalKGPRDiff,
  LocalDiffStats,
  KGSnapshot,
  DiffOptions,
  ChangeType,
} from './types.js';

/**
 * Diff engine for generating knowledge graph diffs
 *
 * @example
 * ```typescript
 * const engine = createLocalDiffEngine();
 *
 * // Create baseline snapshot
 * const baseline = engine.createSnapshot(entities, relationships, 'Initial state');
 *
 * // ... make changes to KG ...
 *
 * // Generate diff from baseline
 * const diff = engine.generateDiff(baseline, currentEntities, currentRelationships);
 * ```
 */
export class LocalDiffEngine {
  private lastSnapshotId = 0;

  /**
   * Create a snapshot of the current knowledge graph state
   *
   * @param entities - Current entities
   * @param relationships - Current relationships
   * @param description - Optional description
   * @returns Snapshot object
   */
  createSnapshot(
    entities: Entity[],
    relationships: Relationship[],
    description?: string
  ): KGSnapshot {
    const entityHashes = new Map<string, string>();
    const relationshipHashes = new Map<string, string>();

    // Hash all entities
    for (const entity of entities) {
      entityHashes.set(entity.id, this.hashEntity(entity));
    }

    // Hash all relationships
    for (const rel of relationships) {
      relationshipHashes.set(rel.id, this.hashRelationship(rel));
    }

    return {
      id: `snapshot-${++this.lastSnapshotId}-${Date.now()}`,
      timestamp: new Date(),
      entityHashes,
      relationshipHashes,
      description,
    };
  }

  /**
   * Generate a diff between baseline snapshot and current state
   *
   * @param baseline - Baseline snapshot (or null for full diff)
   * @param currentEntities - Current entities
   * @param currentRelationships - Current relationships
   * @param options - Diff options
   * @returns The diff
   */
  generateDiff(
    baseline: KGSnapshot | null,
    currentEntities: Entity[],
    currentRelationships: Relationship[],
    options?: DiffOptions
  ): LocalKGPRDiff {
    // Apply filters
    const filteredEntities = this.filterEntities(currentEntities, options);
    const filteredRelationships = this.filterRelationships(currentRelationships, options);

    if (!baseline) {
      // No baseline - everything is added
      return this.createFullDiff(filteredEntities, filteredRelationships);
    }

    // Calculate entity changes
    const entityChanges = this.calculateEntityChanges(
      baseline.entityHashes,
      filteredEntities
    );

    // Calculate relationship changes
    const relationshipChanges = this.calculateRelationshipChanges(
      baseline.relationshipHashes,
      filteredRelationships
    );

    // Calculate stats
    const stats = this.calculateStats(entityChanges, relationshipChanges);

    return {
      entities: entityChanges,
      relationships: relationshipChanges,
      stats,
    };
  }

  /**
   * Generate diff between two snapshots (without current state)
   *
   * @param oldSnapshot - Old snapshot
   * @param newSnapshot - New snapshot
   * @returns Summary diff (IDs only)
   */
  compareSnapshots(
    oldSnapshot: KGSnapshot,
    newSnapshot: KGSnapshot
  ): { added: string[]; updated: string[]; deleted: string[] } {
    const added: string[] = [];
    const updated: string[] = [];
    const deleted: string[] = [];

    // Check entities
    for (const [id, hash] of newSnapshot.entityHashes) {
      const oldHash = oldSnapshot.entityHashes.get(id);
      if (!oldHash) {
        added.push(id);
      } else if (oldHash !== hash) {
        updated.push(id);
      }
    }

    for (const id of oldSnapshot.entityHashes.keys()) {
      if (!newSnapshot.entityHashes.has(id)) {
        deleted.push(id);
      }
    }

    return { added, updated, deleted };
  }

  /**
   * Hash an entity for comparison
   */
  hashEntity(entity: Entity): string {
    const data = JSON.stringify({
      type: entity.type,
      name: entity.name,
      namespace: entity.namespace,
      filePath: entity.filePath,
      line: entity.line,
      metadata: entity.metadata,
    });
    return createHash('sha256').update(data).digest('hex').substring(0, 16);
  }

  /**
   * Hash a relationship for comparison
   */
  hashRelationship(rel: Relationship): string {
    const data = JSON.stringify({
      type: rel.type,
      sourceId: rel.sourceId,
      targetId: rel.targetId,
      metadata: rel.metadata,
    });
    return createHash('sha256').update(data).digest('hex').substring(0, 16);
  }

  /**
   * Filter entities based on options
   */
  private filterEntities(entities: Entity[], options?: DiffOptions): Entity[] {
    if (!options) return entities;

    return entities.filter((entity) => {
      // Filter by namespace
      if (options.namespace && !entity.namespace.startsWith(options.namespace)) {
        return false;
      }

      // Filter by entity type
      if (options.entityTypes && !options.entityTypes.includes(entity.type)) {
        return false;
      }

      return true;
    });
  }

  /**
   * Filter relationships based on options
   */
  private filterRelationships(
    relationships: Relationship[],
    options?: DiffOptions
  ): Relationship[] {
    if (!options) return relationships;

    // For relationships, we can't easily filter by namespace without entity info
    // This would require the caller to provide filtered entity IDs
    return relationships;
  }

  /**
   * Create a full diff (all entities/relationships as added)
   */
  private createFullDiff(
    entities: Entity[],
    relationships: Relationship[]
  ): LocalKGPRDiff {
    const entityChanges: LocalEntityChange[] = entities.map((e) =>
      this.entityToChange(e, 'add')
    );
    const relationshipChanges: LocalRelationshipChange[] = relationships.map((r) =>
      this.relationshipToChange(r, 'add')
    );

    return {
      entities: {
        added: entityChanges,
        updated: [],
        deleted: [],
      },
      relationships: {
        added: relationshipChanges,
        updated: [],
        deleted: [],
      },
      stats: {
        entitiesAdded: entityChanges.length,
        entitiesUpdated: 0,
        entitiesDeleted: 0,
        relationshipsAdded: relationshipChanges.length,
        relationshipsUpdated: 0,
        relationshipsDeleted: 0,
        totalChanges: entityChanges.length + relationshipChanges.length,
      },
    };
  }

  /**
   * Calculate entity changes between baseline and current
   */
  private calculateEntityChanges(
    baselineHashes: Map<string, string>,
    currentEntities: Entity[]
  ): LocalKGPRDiff['entities'] {
    const added: LocalEntityChange[] = [];
    const updated: LocalEntityChange[] = [];
    const deleted: LocalEntityChange[] = [];

    const currentMap = new Map<string, Entity>();
    for (const entity of currentEntities) {
      currentMap.set(entity.id, entity);
    }

    // Find added and updated
    for (const entity of currentEntities) {
      const baselineHash = baselineHashes.get(entity.id);
      const currentHash = this.hashEntity(entity);

      if (!baselineHash) {
        // New entity
        added.push(this.entityToChange(entity, 'add'));
      } else if (baselineHash !== currentHash) {
        // Updated entity
        updated.push(this.entityToChange(entity, 'update'));
      }
    }

    // Find deleted (in baseline but not in current)
    for (const id of baselineHashes.keys()) {
      if (!currentMap.has(id)) {
        // Deleted - we don't have the entity data, just the ID
        deleted.push({
          changeType: 'delete',
          localId: id,
          name: `[deleted:${id}]`,
          entityType: 'unknown' as EntityType,
          namespace: 'unknown',
        });
      }
    }

    return { added, updated, deleted };
  }

  /**
   * Calculate relationship changes between baseline and current
   */
  private calculateRelationshipChanges(
    baselineHashes: Map<string, string>,
    currentRelationships: Relationship[]
  ): LocalKGPRDiff['relationships'] {
    const added: LocalRelationshipChange[] = [];
    const updated: LocalRelationshipChange[] = [];
    const deleted: LocalRelationshipChange[] = [];

    const currentMap = new Map<string, Relationship>();
    for (const rel of currentRelationships) {
      currentMap.set(rel.id, rel);
    }

    // Find added and updated
    for (const rel of currentRelationships) {
      const baselineHash = baselineHashes.get(rel.id);
      const currentHash = this.hashRelationship(rel);

      if (!baselineHash) {
        // New relationship
        added.push(this.relationshipToChange(rel, 'add'));
      } else if (baselineHash !== currentHash) {
        // Updated relationship
        updated.push(this.relationshipToChange(rel, 'update'));
      }
    }

    // Find deleted
    for (const id of baselineHashes.keys()) {
      if (!currentMap.has(id)) {
        deleted.push({
          changeType: 'delete',
          localId: id,
          sourceName: `[deleted:${id}]`,
          sourceNamespace: 'unknown',
          targetName: 'unknown',
          targetNamespace: 'unknown',
          relationshipType: 'unknown' as RelationType,
        });
      }
    }

    return { added, updated, deleted };
  }

  /**
   * Convert entity to change format
   */
  private entityToChange(entity: Entity, changeType: ChangeType): LocalEntityChange {
    return {
      changeType,
      localId: entity.id,
      name: entity.name,
      entityType: entity.type,
      namespace: entity.namespace,
      filePath: entity.filePath,
      line: entity.line,
      metadata: entity.metadata as Record<string, unknown> | undefined,
    };
  }

  /**
   * Convert relationship to change format
   * Note: This requires entity lookup for names - simplified version uses IDs
   */
  private relationshipToChange(
    rel: Relationship,
    changeType: ChangeType
  ): LocalRelationshipChange {
    return {
      changeType,
      localId: rel.id,
      // Note: In a full implementation, we'd look up entity names
      sourceName: rel.sourceId,
      sourceNamespace: 'unknown', // Would need entity lookup
      targetName: rel.targetId,
      targetNamespace: 'unknown', // Would need entity lookup
      relationshipType: rel.type,
      metadata: rel.metadata as Record<string, unknown> | undefined,
    };
  }

  /**
   * Calculate diff statistics
   */
  private calculateStats(
    entityChanges: LocalKGPRDiff['entities'],
    relationshipChanges: LocalKGPRDiff['relationships']
  ): LocalDiffStats {
    return {
      entitiesAdded: entityChanges.added.length,
      entitiesUpdated: entityChanges.updated.length,
      entitiesDeleted: entityChanges.deleted.length,
      relationshipsAdded: relationshipChanges.added.length,
      relationshipsUpdated: relationshipChanges.updated.length,
      relationshipsDeleted: relationshipChanges.deleted.length,
      totalChanges:
        entityChanges.added.length +
        entityChanges.updated.length +
        entityChanges.deleted.length +
        relationshipChanges.added.length +
        relationshipChanges.updated.length +
        relationshipChanges.deleted.length,
    };
  }
}

/**
 * Create a new diff engine instance
 *
 * @returns New diff engine
 */
export function createLocalDiffEngine(): LocalDiffEngine {
  return new LocalDiffEngine();
}
