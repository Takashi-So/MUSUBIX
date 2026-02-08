/**
 * @nahisaho/musubix-codegraph - Knowledge Store Adapter
 *
 * Adapts @musubix/knowledge's KnowledgeStore to the codegraph StorageAdapter interface.
 * Maps codegraph entities/relations to knowledge graph entities/relations.
 *
 * @see REQ-CG-API-005
 * @see DES-CG-006
 */

import type {
  StorageAdapter,
  StorageStats,
  Entity,
  Relation,
  GraphQuery,
  RelationType,
} from '../types.js';

import type {
  KnowledgeStore,
  Entity as KnowledgeEntity,
  Relation as KnowledgeRelation,
  RelationType as KnowledgeRelationType,
} from '@musubix/knowledge';

/**
 * Options for KnowledgeAdapter
 */
export interface KnowledgeAdapterOptions {
  /** Whether to auto-save after each mutation (default: false) */
  autoSave?: boolean;
}

/** Relation types shared between codegraph and knowledge */
const SHARED_RELATION_TYPES: Set<string> = new Set([
  'implements',
  'depends_on',
]);

/**
 * Map a codegraph RelationType to a knowledge RelationType.
 * Shared types map directly; others map to 'related_to'.
 */
function toKnowledgeRelationType(type: RelationType): KnowledgeRelationType {
  if (SHARED_RELATION_TYPES.has(type)) {
    return type as KnowledgeRelationType;
  }
  return 'related_to';
}

/**
 * Convert a codegraph Entity to a knowledge Entity
 */
function toKnowledgeEntity(entity: Entity): KnowledgeEntity {
  const now = new Date().toISOString();
  const tags: string[] = [];

  if (entity.language) tags.push(`lang:${entity.language}`);
  if (entity.type) tags.push(`kind:${entity.type}`);
  if (entity.communityId) tags.push(`community:${entity.communityId}`);

  return {
    id: `code-node:${entity.id}`,
    type: 'code',
    name: entity.name,
    description: entity.docstring,
    properties: {
      entityType: entity.type,
      qualifiedName: entity.qualifiedName,
      namespace: entity.namespace,
      filePath: entity.filePath,
      startLine: entity.startLine,
      endLine: entity.endLine,
      signature: entity.signature,
      sourceCode: entity.sourceCode,
      communityId: entity.communityId,
      language: entity.language,
      metadata: entity.metadata,
    },
    tags,
    createdAt: entity.createdAt?.toISOString() ?? now,
    updatedAt: entity.updatedAt?.toISOString() ?? now,
  };
}

/**
 * Convert a knowledge Entity back to a codegraph Entity
 */
function fromKnowledgeEntity(kEntity: KnowledgeEntity): Entity {
  const props = kEntity.properties;
  return {
    id: String(kEntity.id).replace(/^code-node:/, ''),
    type: (props.entityType as Entity['type']) ?? 'unknown',
    name: kEntity.name,
    qualifiedName: props.qualifiedName as string | undefined,
    namespace: props.namespace as string | undefined,
    filePath: props.filePath as string | undefined,
    startLine: props.startLine as number | undefined,
    endLine: props.endLine as number | undefined,
    signature: props.signature as string | undefined,
    docstring: kEntity.description,
    sourceCode: props.sourceCode as string | undefined,
    communityId: props.communityId as string | undefined,
    language: props.language as Entity['language'],
    metadata: (props.metadata as Record<string, unknown>) ?? {},
    createdAt: kEntity.createdAt ? new Date(kEntity.createdAt) : undefined,
    updatedAt: kEntity.updatedAt ? new Date(kEntity.updatedAt) : undefined,
  };
}

/**
 * Convert a codegraph Relation to a knowledge Relation
 */
function toKnowledgeRelation(relation: Relation): KnowledgeRelation {
  return {
    id: `code-rel:${relation.id}`,
    source: `code-node:${relation.sourceId}`,
    target: `code-node:${relation.targetId}`,
    type: toKnowledgeRelationType(relation.type),
    properties: {
      relationType: relation.type,
      weight: relation.weight,
      metadata: relation.metadata,
    },
  };
}

/**
 * Convert a knowledge Relation back to a codegraph Relation
 */
function fromKnowledgeRelation(kRelation: KnowledgeRelation): Relation {
  const props = kRelation.properties ?? {};
  return {
    id: String(kRelation.id).replace(/^code-rel:/, ''),
    sourceId: String(kRelation.source).replace(/^code-node:/, ''),
    targetId: String(kRelation.target).replace(/^code-node:/, ''),
    type: (props.relationType as RelationType) ?? 'references',
    weight: (props.weight as number) ?? 1,
    metadata: (props.metadata as Record<string, unknown>) ?? {},
  };
}

/**
 * Knowledge Store adapter for codegraph
 *
 * Bridges @musubix/knowledge's KnowledgeStore to the codegraph StorageAdapter
 * interface, allowing codegraph data to be persisted in the knowledge graph.
 *
 * @example
 * ```typescript
 * import { createKnowledgeStore } from '@musubix/knowledge';
 * import { KnowledgeAdapter } from '@nahisaho/musubix-codegraph/storage';
 *
 * const store = createKnowledgeStore('.knowledge');
 * const adapter = new KnowledgeAdapter(store);
 * await adapter.initialize();
 *
 * await adapter.saveEntity(entity);
 * const retrieved = await adapter.getEntity(entity.id);
 * ```
 */
export class KnowledgeAdapter implements StorageAdapter {
  private store: KnowledgeStore;
  private options: Required<KnowledgeAdapterOptions>;
  private initialized = false;
  private filePathSet = new Set<string>();

  constructor(store: KnowledgeStore, options: KnowledgeAdapterOptions = {}) {
    this.store = store;
    this.options = {
      autoSave: options.autoSave ?? false,
    };
  }

  // =========================================================================
  // Lifecycle
  // =========================================================================

  async initialize(): Promise<void> {
    if (this.initialized) return;
    await this.store.load();
    // Rebuild the file path set from existing entities
    await this.rebuildFilePathIndex();
    this.initialized = true;
  }

  async close(): Promise<void> {
    if (this.options.autoSave) {
      await this.store.save();
    }
    this.filePathSet.clear();
    this.initialized = false;
  }

  // =========================================================================
  // Entity Operations
  // =========================================================================

  async saveEntity(entity: Entity): Promise<void> {
    const kEntity = toKnowledgeEntity(entity);
    await this.store.putEntity(kEntity);
    if (entity.filePath) {
      this.filePathSet.add(entity.filePath);
    }
    if (this.options.autoSave) {
      await this.store.save();
    }
  }

  async getEntity(id: string): Promise<Entity | null> {
    const kEntity = await this.store.getEntity(`code-node:${id}`);
    if (!kEntity) return null;
    return fromKnowledgeEntity(kEntity);
  }

  async queryEntities(query: GraphQuery): Promise<Entity[]> {
    // Use the knowledge store's query to get code entities
    const allCodeEntities = await this.store.query({
      type: 'code',
    });

    let results = allCodeEntities.map(fromKnowledgeEntity);

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

  async deleteEntity(id: string): Promise<void> {
    // Remove entity from knowledge store (which also removes related relations)
    await this.store.deleteEntity(`code-node:${id}`);
    if (this.options.autoSave) {
      await this.store.save();
    }
  }

  // =========================================================================
  // Relation Operations
  // =========================================================================

  async saveRelation(relation: Relation): Promise<void> {
    const kRelation = toKnowledgeRelation(relation);
    try {
      await this.store.addRelation(kRelation);
      if (this.options.autoSave) {
        await this.store.save();
      }
    } catch {
      // If source/target entity not found in knowledge store, silently skip
      // This can happen when relations reference entities not yet saved
    }
  }

  async getRelations(
    entityId: string,
    direction: 'in' | 'out' | 'both' = 'both'
  ): Promise<Relation[]> {
    const kRelations = await this.store.getRelations(
      `code-node:${entityId}`,
      direction
    );

    // Only return relations that belong to codegraph (prefixed with code-rel:)
    return kRelations
      .filter((r) => String(r.id).startsWith('code-rel:'))
      .map(fromKnowledgeRelation);
  }

  async deleteRelation(id: string): Promise<void> {
    await this.store.removeRelation(`code-rel:${id}`);
    if (this.options.autoSave) {
      await this.store.save();
    }
  }

  // =========================================================================
  // Bulk Operations
  // =========================================================================

  async bulkSave(entities: Entity[], relations: Relation[]): Promise<void> {
    for (const entity of entities) {
      await this.saveEntity(entity);
    }
    for (const relation of relations) {
      await this.saveRelation(relation);
    }
  }

  async clear(): Promise<void> {
    // Query all code entities and delete them
    const codeEntities = await this.store.query({ type: 'code' });
    for (const entity of codeEntities) {
      await this.store.deleteEntity(entity.id);
    }
    this.filePathSet.clear();
    if (this.options.autoSave) {
      await this.store.save();
    }
  }

  // =========================================================================
  // Statistics
  // =========================================================================

  async getStats(): Promise<StorageStats> {
    const codeEntities = await this.store.query({ type: 'code' });
    let relationCount = 0;

    for (const entity of codeEntities) {
      const rels = await this.store.getRelations(entity.id, 'out');
      relationCount += rels.filter((r) =>
        String(r.id).startsWith('code-rel:')
      ).length;
    }

    return {
      entityCount: codeEntities.length,
      relationCount,
      fileCount: this.filePathSet.size,
    };
  }

  // =========================================================================
  // Internal Helpers
  // =========================================================================

  /**
   * Rebuild the file path index from stored entities
   */
  private async rebuildFilePathIndex(): Promise<void> {
    this.filePathSet.clear();
    const codeEntities = await this.store.query({ type: 'code' });
    for (const entity of codeEntities) {
      const filePath = entity.properties.filePath;
      if (typeof filePath === 'string') {
        this.filePathSet.add(filePath);
      }
    }
  }

  /**
   * Save all pending changes to disk
   */
  async save(): Promise<void> {
    await this.store.save();
  }

  /**
   * Check if the adapter is initialized
   */
  isInitialized(): boolean {
    return this.initialized;
  }
}
