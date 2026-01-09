/**
 * @nahisaho/musubix-codegraph - Memory Storage Implementation
 *
 * In-memory storage adapter for CodeGraph
 *
 * @see REQ-CG-API-005
 * @see DES-CG-006
 * @see TSK-CG-051
 */

import type {
  StorageAdapter,
  StorageStats,
  Entity,
  Relation,
  GraphQuery,
  RelationType,
} from '../types.js';

/**
 * In-memory storage adapter
 *
 * Stores entities and relations in memory using Maps.
 * Suitable for testing and small codebases.
 *
 * @example
 * ```typescript
 * const storage = new MemoryStorage();
 * await storage.initialize();
 *
 * await storage.saveEntity(entity);
 * const retrieved = await storage.getEntity(entity.id);
 * ```
 */
export class MemoryStorage implements StorageAdapter {
  private entities = new Map<string, Entity>();
  private relations = new Map<string, Relation>();
  private relationsBySource = new Map<string, Set<string>>();
  private relationsByTarget = new Map<string, Set<string>>();
  private fileCount = new Set<string>();
  private initialized = false;

  /**
   * Initialize the storage
   */
  async initialize(): Promise<void> {
    if (this.initialized) return;
    this.initialized = true;
  }

  /**
   * Close the storage and release resources
   */
  async close(): Promise<void> {
    this.entities.clear();
    this.relations.clear();
    this.relationsBySource.clear();
    this.relationsByTarget.clear();
    this.fileCount.clear();
    this.initialized = false;
  }

  // =========================================================================
  // Entity Operations
  // =========================================================================

  /**
   * Save an entity
   */
  async saveEntity(entity: Entity): Promise<void> {
    this.entities.set(entity.id, entity);
    if (entity.filePath) {
      this.fileCount.add(entity.filePath);
    }
  }

  /**
   * Get an entity by ID
   */
  async getEntity(id: string): Promise<Entity | null> {
    return this.entities.get(id) ?? null;
  }

  /**
   * Query entities
   */
  async queryEntities(query: GraphQuery): Promise<Entity[]> {
    let results = Array.from(this.entities.values());

    // Filter by entity types
    if (query.entityTypes && query.entityTypes.length > 0) {
      results = results.filter((e) => query.entityTypes!.includes(e.type));
    }

    // Filter by file path
    if (query.filePath) {
      const normalizedPath = query.filePath.toLowerCase();
      results = results.filter(
        (e) => e.filePath?.toLowerCase() === normalizedPath
      );
    }

    // Text search
    if (query.textSearch) {
      const searchLower = query.textSearch.toLowerCase();
      results = results.filter(
        (e) =>
          e.name.toLowerCase().includes(searchLower) ||
          e.id.toLowerCase().includes(searchLower) ||
          e.docstring?.toLowerCase().includes(searchLower)
      );
    }

    // Apply limit
    if (query.limit && query.limit > 0) {
      results = results.slice(0, query.limit);
    }

    return results;
  }

  /**
   * Delete an entity
   */
  async deleteEntity(id: string): Promise<void> {
    const entity = this.entities.get(id);
    if (entity) {
      // Also remove related relations
      const relatedRelationIds = new Set<string>();

      // Outgoing relations
      const outgoing = this.relationsBySource.get(id);
      if (outgoing) {
        outgoing.forEach((rid) => relatedRelationIds.add(rid));
        this.relationsBySource.delete(id);
      }

      // Incoming relations
      const incoming = this.relationsByTarget.get(id);
      if (incoming) {
        incoming.forEach((rid) => relatedRelationIds.add(rid));
        this.relationsByTarget.delete(id);
      }

      // Delete relations
      for (const rid of relatedRelationIds) {
        this.relations.delete(rid);
      }

      // Delete entity
      this.entities.delete(id);
    }
  }

  // =========================================================================
  // Relation Operations
  // =========================================================================

  /**
   * Save a relation
   */
  async saveRelation(relation: Relation): Promise<void> {
    this.relations.set(relation.id, relation);

    // Index by source
    if (!this.relationsBySource.has(relation.sourceId)) {
      this.relationsBySource.set(relation.sourceId, new Set());
    }
    this.relationsBySource.get(relation.sourceId)!.add(relation.id);

    // Index by target
    if (!this.relationsByTarget.has(relation.targetId)) {
      this.relationsByTarget.set(relation.targetId, new Set());
    }
    this.relationsByTarget.get(relation.targetId)!.add(relation.id);
  }

  /**
   * Get relations for an entity
   */
  async getRelations(
    entityId: string,
    direction: 'in' | 'out' | 'both' = 'both'
  ): Promise<Relation[]> {
    const relationIds = new Set<string>();

    if (direction === 'out' || direction === 'both') {
      const outgoing = this.relationsBySource.get(entityId);
      if (outgoing) {
        outgoing.forEach((id) => relationIds.add(id));
      }
    }

    if (direction === 'in' || direction === 'both') {
      const incoming = this.relationsByTarget.get(entityId);
      if (incoming) {
        incoming.forEach((id) => relationIds.add(id));
      }
    }

    return Array.from(relationIds)
      .map((id) => this.relations.get(id))
      .filter((r): r is Relation => r !== undefined);
  }

  /**
   * Delete a relation
   */
  async deleteRelation(id: string): Promise<void> {
    const relation = this.relations.get(id);
    if (relation) {
      // Remove from source index
      const sourceRels = this.relationsBySource.get(relation.sourceId);
      if (sourceRels) {
        sourceRels.delete(id);
        if (sourceRels.size === 0) {
          this.relationsBySource.delete(relation.sourceId);
        }
      }

      // Remove from target index
      const targetRels = this.relationsByTarget.get(relation.targetId);
      if (targetRels) {
        targetRels.delete(id);
        if (targetRels.size === 0) {
          this.relationsByTarget.delete(relation.targetId);
        }
      }

      this.relations.delete(id);
    }
  }

  // =========================================================================
  // Bulk Operations
  // =========================================================================

  /**
   * Bulk save entities and relations
   */
  async bulkSave(entities: Entity[], relations: Relation[]): Promise<void> {
    for (const entity of entities) {
      await this.saveEntity(entity);
    }
    for (const relation of relations) {
      await this.saveRelation(relation);
    }
  }

  /**
   * Clear all data
   */
  async clear(): Promise<void> {
    this.entities.clear();
    this.relations.clear();
    this.relationsBySource.clear();
    this.relationsByTarget.clear();
    this.fileCount.clear();
  }

  // =========================================================================
  // Statistics
  // =========================================================================

  /**
   * Get storage statistics
   */
  async getStats(): Promise<StorageStats> {
    return {
      entityCount: this.entities.size,
      relationCount: this.relations.size,
      fileCount: this.fileCount.size,
    };
  }

  // =========================================================================
  // Additional Helper Methods
  // =========================================================================

  /**
   * Find entities by name pattern
   */
  async findByName(name: string, exact = false): Promise<Entity[]> {
    const nameLower = name.toLowerCase();
    return Array.from(this.entities.values()).filter((e) =>
      exact
        ? e.name.toLowerCase() === nameLower
        : e.name.toLowerCase().includes(nameLower)
    );
  }

  /**
   * Get all entities of a specific type
   */
  async getEntitiesByType(type: Entity['type']): Promise<Entity[]> {
    return Array.from(this.entities.values()).filter((e) => e.type === type);
  }

  /**
   * Get relations by type
   */
  async getRelationsByType(type: RelationType): Promise<Relation[]> {
    return Array.from(this.relations.values()).filter((r) => r.type === type);
  }

  /**
   * Get all file paths
   */
  async getFilePaths(): Promise<string[]> {
    return Array.from(this.fileCount);
  }

  /**
   * Check if storage is initialized
   */
  isInitialized(): boolean {
    return this.initialized;
  }
}
