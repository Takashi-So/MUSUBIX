// Knowledge Store Integration
// TSK-DR-025
// REQ: REQ-DR-INT-005
// DES: DES-DR-v3.4.0 Section 5.4

import type {
  Entity,
  Relation,
  KnowledgeStore,
  QueryFilter,
  SearchOptions,
  TraverseOptions,
} from '@musubix/knowledge';

/**
 * Configuration for Knowledge Store integration
 */
export interface KnowledgeStoreConfig {
  /** Base path for knowledge storage (default: .knowledge) */
  basePath?: string;
  /** Auto-save on updates */
  autoSave?: boolean;
  /** Load on initialization */
  autoLoad?: boolean;
}

/**
 * Default configuration
 */
const DEFAULT_CONFIG: Required<KnowledgeStoreConfig> = {
  basePath: '.knowledge',
  autoSave: true,
  autoLoad: true,
};

/**
 * Knowledge item from research
 */
export interface KnowledgeItem {
  content: string;
  type: 'fact' | 'concept' | 'relation' | 'source';
  confidence?: number;
  iteration: number;
  metadata?: Record<string, unknown>;
}

/**
 * Storage result
 */
export interface StorageResult {
  entityId: string;
  stored: boolean;
  message?: string;
}

/**
 * Query result with context
 */
export interface KnowledgeQueryResult {
  entities: Entity[];
  relationCount: number;
  depth: number;
}

/**
 * Knowledge Store Integration
 * 
 * Integrates Deep Research with @musubix/knowledge package
 * for persistent knowledge graph storage.
 * 
 * Features:
 * - Store research results as entities
 * - Query knowledge graph
 * - Track relations between findings
 * - Git-friendly JSON storage
 * - Export/import knowledge base
 */
export class KnowledgeStoreIntegration {
  private store: KnowledgeStore | null = null;
  private config: Required<KnowledgeStoreConfig>;
  private entityCounter = 0;

  constructor(config?: KnowledgeStoreConfig) {
    this.config = { ...DEFAULT_CONFIG, ...config };
  }

  /**
   * Initialize the knowledge store
   */
  async initialize(): Promise<void> {
    const knowledgeModule = await this.loadKnowledge();
    if (!knowledgeModule) {
      console.warn('⚠️  @musubix/knowledge package not available');
      return;
    }

    this.store = knowledgeModule.createKnowledgeStore(this.config.basePath);

    if (this.config.autoLoad) {
      await this.store.load();
      console.log(`📚 Knowledge store loaded from ${this.config.basePath}`);
    }
  }

  /**
   * Check if knowledge store is available
   */
  async isAvailable(): Promise<boolean> {
    if (this.store) return true;
    
    try {
      const knowledgeModule = await this.loadKnowledge();
      return knowledgeModule !== null;
    } catch {
      return false;
    }
  }

  /**
   * Store a knowledge item from research
   */
  async storeKnowledgeItem(
    item: KnowledgeItem,
    query: string
  ): Promise<StorageResult> {
    if (!this.store) {
      return {
        entityId: '',
        stored: false,
        message: 'Knowledge store not initialized',
      };
    }

    const entityId = this.generateEntityId(item.type);
    const entity: Entity = {
      id: entityId,
      type: 'pattern', // Map research findings to pattern entities
      name: this.extractTitle(item.content),
      description: item.content,
      properties: {
        query,
        itemType: item.type,
        confidence: item.confidence ?? 1.0,
        iteration: item.iteration,
        ...item.metadata,
      },
      tags: [item.type, `iteration-${item.iteration}`],
      createdAt: new Date().toISOString(),
      updatedAt: new Date().toISOString(),
    };

    await this.store.putEntity(entity);

    if (this.config.autoSave) {
      await this.store.save();
    }

    console.log(`💾 Stored knowledge item: ${entityId}`);

    return {
      entityId,
      stored: true,
      message: 'Successfully stored',
    };
  }

  /**
   * Query knowledge base
   */
  async query(filter: QueryFilter): Promise<Entity[]> {
    if (!this.store) {
      throw new Error('Knowledge store not initialized');
    }

    return await this.store.query(filter);
  }

  /**
   * Search knowledge base by text
   */
  async search(text: string, options?: SearchOptions): Promise<Entity[]> {
    if (!this.store) {
      throw new Error('Knowledge store not initialized');
    }

    return await this.store.search(text, options);
  }

  /**
   * Get related entities (graph traversal)
   */
  async getRelated(
    entityId: string,
    options?: TraverseOptions
  ): Promise<KnowledgeQueryResult> {
    if (!this.store) {
      throw new Error('Knowledge store not initialized');
    }

    const entities = await this.store.traverse(entityId, options);
    const relations = await this.store.getRelations(entityId, 'both');

    return {
      entities,
      relationCount: relations.length,
      depth: options?.depth ?? 1,
    };
  }

  /**
   * Add relation between entities
   */
  async addRelation(relation: Omit<Relation, 'id'>): Promise<void> {
    if (!this.store) {
      throw new Error('Knowledge store not initialized');
    }

    const relationId = `rel-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
    await this.store.addRelation({
      id: relationId,
      ...relation,
    });

    if (this.config.autoSave) {
      await this.store.save();
    }
  }

  /**
   * Export knowledge base
   */
  async export(): Promise<string> {
    if (!this.store) {
      throw new Error('Knowledge store not initialized');
    }

    const stats = this.store.getStats();
    const entities = await this.store.query({});

    return JSON.stringify(
      {
        exportedAt: new Date().toISOString(),
        stats,
        entities,
      },
      null,
      2
    );
  }

  /**
   * Get statistics
   */
  getStats(): { entityCount: number; relationCount: number } {
    if (!this.store) {
      return { entityCount: 0, relationCount: 0 };
    }

    return this.store.getStats();
  }

  /**
   * Save knowledge store to disk
   */
  async save(): Promise<void> {
    if (!this.store) {
      throw new Error('Knowledge store not initialized');
    }

    await this.store.save();
    console.log(`💾 Knowledge store saved to ${this.config.basePath}`);
  }

  // ============================================================
  // Private Helper Methods
  // ============================================================

  /**
   * Generate entity ID
   */
  private generateEntityId(type: string): string {
    this.entityCounter++;
    const timestamp = Date.now().toString(36);
    return `knowledge-${type}-${timestamp}-${this.entityCounter}`;
  }

  /**
   * Extract title from content (first 50 chars)
   */
  private extractTitle(content: string): string {
    const cleaned = content.replace(/\s+/g, ' ').trim();
    return cleaned.length > 50 ? cleaned.substring(0, 50) + '...' : cleaned;
  }

  /**
   * Load @musubix/knowledge package dynamically
   */
  private async loadKnowledge(): Promise<typeof import('@musubix/knowledge') | null> {
    try {
      const knowledgeModule = await import('@musubix/knowledge');
      return knowledgeModule;
    } catch (error) {
      console.error('⚠️  Failed to load @musubix/knowledge:', error);
      return null;
    }
  }
}

/**
 * Factory function to create Knowledge Store integration
 */
export function createKnowledgeStoreIntegration(
  config?: KnowledgeStoreConfig
): KnowledgeStoreIntegration {
  return new KnowledgeStoreIntegration(config);
}
