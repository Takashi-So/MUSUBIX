/**
 * YATA Local Auto-Learn Middleware
 *
 * CLI commands can use this middleware to automatically register
 * validated artifacts to YATA Local knowledge graph.
 *
 * @packageDocumentation
 * @module cli/middleware/auto-learn
 */

import type { EntityType, RelationType } from '@nahisaho/yata-local';

/**
 * Auto-learn options
 */
export interface AutoLearnOptions {
  /** Enable auto-learn */
  autoLearn?: boolean;
  /** YATA Local database path */
  db?: string;
}

/**
 * Entity input for YATA Local registration
 */
export interface YataEntityInput {
  name: string;
  type: EntityType;
  namespace: string;
  filePath?: string;
  metadata?: Record<string, unknown>;
}

/**
 * Relationship input for YATA Local registration
 */
export interface YataRelationshipInput {
  sourceId: string;
  targetId: string;
  type: RelationType;
  metadata?: Record<string, unknown>;
}

/**
 * Registration result
 */
export interface RegistrationResult {
  entityCount: number;
  relationshipCount: number;
  created: number;
  updated: number;
}

/**
 * Check if auto-learn is enabled
 */
export function isAutoLearnEnabled(options: AutoLearnOptions): boolean {
  return options.autoLearn === true || process.env.MUSUBIX_AUTO_LEARN === 'true';
}

/**
 * Get default database path
 */
export function getDefaultDbPath(options: AutoLearnOptions): string {
  return options.db ?? process.env.MUSUBIX_YATA_LOCAL_DB ?? './.yata-local.db';
}

/**
 * Auto-learn middleware class
 */
export class AutoLearnMiddleware {
  private dbPath: string;
  private yataLocal: unknown = null;

  constructor(options: AutoLearnOptions = {}) {
    this.dbPath = getDefaultDbPath(options);
  }

  /**
   * Initialize YATA Local connection
   */
  async init(): Promise<boolean> {
    try {
      const yataLocalModule = await import('@nahisaho/yata-local');
      const { createYataLocal } = yataLocalModule;
      this.yataLocal = createYataLocal({ path: this.dbPath });
      await (this.yataLocal as { open: () => Promise<void> }).open();
      return true;
    } catch {
      // YATA Local not available
      return false;
    }
  }

  /**
   * Close YATA Local connection
   */
  async close(): Promise<void> {
    if (this.yataLocal) {
      await (this.yataLocal as { close: () => Promise<void> }).close();
      this.yataLocal = null;
    }
  }

  /**
   * Register entity using upsert
   */
  async registerEntity(entity: YataEntityInput): Promise<{ id: string; created: boolean }> {
    if (!this.yataLocal) {
      throw new Error('YATA Local not initialized');
    }
    const yata = this.yataLocal as {
      upsertEntity: (
        entity: Omit<YataEntityInput, 'metadata'> & { metadata?: Record<string, unknown> },
        matchBy: 'name' | 'name-namespace'
      ) => Promise<{ id: string; created: boolean }>;
    };
    return yata.upsertEntity(entity, 'name-namespace');
  }

  /**
   * Register relationship
   */
  async registerRelationship(input: YataRelationshipInput): Promise<string> {
    if (!this.yataLocal) {
      throw new Error('YATA Local not initialized');
    }
    const yata = this.yataLocal as {
      addRelationship: (
        sourceId: string,
        targetId: string,
        type: RelationType,
        metadata?: Record<string, unknown>
      ) => Promise<string>;
    };
    return yata.addRelationship(input.sourceId, input.targetId, input.type, input.metadata);
  }

  /**
   * Register multiple entities and relationships
   */
  async registerBatch(
    entities: YataEntityInput[],
    relationships: YataRelationshipInput[]
  ): Promise<RegistrationResult> {
    const result: RegistrationResult = {
      entityCount: 0,
      relationshipCount: 0,
      created: 0,
      updated: 0,
    };

    const idMap = new Map<string, string>();

    // Register entities first
    for (const entity of entities) {
      const { id, created } = await this.registerEntity(entity);
      idMap.set(entity.name, id);
      result.entityCount++;
      if (created) result.created++;
      else result.updated++;
    }

    // Register relationships
    for (const rel of relationships) {
      const sourceId = idMap.get(rel.sourceId) ?? rel.sourceId;
      const targetId = idMap.get(rel.targetId) ?? rel.targetId;
      await this.registerRelationship({ ...rel, sourceId, targetId });
      result.relationshipCount++;
    }

    return result;
  }
}

/**
 * Create auto-learn middleware instance
 */
export function createAutoLearnMiddleware(options: AutoLearnOptions = {}): AutoLearnMiddleware {
  return new AutoLearnMiddleware(options);
}

/**
 * Wrap async function with auto-learn capability
 */
export function withAutoLearn<T extends (...args: unknown[]) => Promise<{ entities?: YataEntityInput[]; relationships?: YataRelationshipInput[] }>>(
  fn: T,
  options: AutoLearnOptions = {}
): T {
  return (async (...args: Parameters<T>) => {
    const result = await fn(...args);
    
    if (isAutoLearnEnabled(options) && result.entities) {
      const middleware = createAutoLearnMiddleware(options);
      const initialized = await middleware.init();
      
      if (initialized) {
        await middleware.registerBatch(
          result.entities,
          result.relationships ?? []
        );
        await middleware.close();
      }
    }
    
    return result;
  }) as T;
}
