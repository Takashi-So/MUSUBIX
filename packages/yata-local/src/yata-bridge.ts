/**
 * YATA Local - YATA Bridge for MCP Integration
 *
 * Provides integration between YATA Local and MCP Server
 * for automatic knowledge graph updates.
 *
 * @packageDocumentation
 * @module @nahisaho/yata-local
 * @see REQ-YATA-AUTO-002
 */

import type { YataLocal } from './index.js';
import type {
  Entity,
} from './types.js';
import {
  KnowledgeGraphUpdater,
  type CodeAnalysisResult,
  type ExtractedEntity,
  type ExtractedRelationship,
  type UpdateResult,
} from './auto-updater.js';

/**
 * Bridge configuration
 */
export interface YataBridgeConfig {
  /** Auto-infer after updates */
  autoInfer?: boolean;
  /** Auto-validate after updates */
  autoValidate?: boolean;
  /** Batch size for bulk updates */
  batchSize?: number;
  /** Delete old entities before update */
  cleanBeforeUpdate?: boolean;
}

const DEFAULT_CONFIG: Required<YataBridgeConfig> = {
  autoInfer: false,
  autoValidate: true,
  batchSize: 100,
  cleanBeforeUpdate: true,
};

/**
 * YATA Bridge for MCP Integration
 *
 * Connects code analysis to YATA Local knowledge graph.
 */
export class YataBridge {
  private yata: YataLocal;
  private updater: KnowledgeGraphUpdater;
  private config: Required<YataBridgeConfig>;
  private entityNameIndex: Map<string, string> = new Map();

  constructor(yata: YataLocal, config?: YataBridgeConfig) {
    this.yata = yata;
    this.updater = new KnowledgeGraphUpdater();
    this.config = { ...DEFAULT_CONFIG, ...config };
  }

  /**
   * Analyze code and update knowledge graph
   */
  async updateFromCode(content: string, filePath: string): Promise<UpdateResult> {
    const result: UpdateResult = {
      success: true,
      entitiesAdded: 0,
      entitiesUpdated: 0,
      entitiesDeleted: 0,
      relationshipsAdded: 0,
      relationshipsDeleted: 0,
      errors: [],
    };

    try {
      // Analyze code
      const analysis = this.updater.analyzeCode(content, filePath);
      result.errors.push(...analysis.errors);

      // Clean old entities from this file if configured
      if (this.config.cleanBeforeUpdate) {
        const deleted = await this.yata.deleteEntitiesByFile(filePath);
        result.entitiesDeleted = deleted;
      }

      // Add entities
      const entityIds = await this.addEntities(analysis.entities);
      result.entitiesAdded = entityIds.length;

      // Refresh entity name index
      await this.refreshEntityIndex();

      // Add relationships
      const relCount = await this.addRelationships(analysis.relationships);
      result.relationshipsAdded = relCount;

      // Auto-infer if configured
      if (this.config.autoInfer) {
        await this.yata.infer();
      }

      // Auto-validate if configured
      if (this.config.autoValidate) {
        const validation = await this.yata.validate();
        if (!validation.valid) {
          result.errors.push(
            ...validation.violations.map(
              v => `Validation: ${v.message} (${v.constraintId})`
            )
          );
        }
      }
    } catch (error) {
      result.success = false;
      result.errors.push(
        error instanceof Error ? error.message : String(error)
      );
    }

    return result;
  }

  /**
   * Bulk update from multiple files
   */
  async updateFromFiles(
    files: Array<{ content: string; filePath: string }>
  ): Promise<UpdateResult> {
    const totalResult: UpdateResult = {
      success: true,
      entitiesAdded: 0,
      entitiesUpdated: 0,
      entitiesDeleted: 0,
      relationshipsAdded: 0,
      relationshipsDeleted: 0,
      errors: [],
    };

    // Process in batches
    for (let i = 0; i < files.length; i += this.config.batchSize) {
      const batch = files.slice(i, i + this.config.batchSize);

      for (const file of batch) {
        const result = await this.updateFromCode(file.content, file.filePath);
        totalResult.entitiesAdded += result.entitiesAdded;
        totalResult.entitiesUpdated += result.entitiesUpdated;
        totalResult.entitiesDeleted += result.entitiesDeleted;
        totalResult.relationshipsAdded += result.relationshipsAdded;
        totalResult.relationshipsDeleted += result.relationshipsDeleted;
        totalResult.errors.push(...result.errors);

        if (!result.success) {
          totalResult.success = false;
        }
      }
    }

    return totalResult;
  }

  /**
   * Analyze code without updating (preview)
   */
  analyzeOnly(content: string, filePath: string): CodeAnalysisResult {
    return this.updater.analyzeCode(content, filePath);
  }

  /**
   * Add entities to knowledge graph
   */
  private async addEntities(
    entities: ExtractedEntity[]
  ): Promise<string[]> {
    const ids: string[] = [];

    for (const entity of entities) {
      const id = await this.yata.addEntity({
        type: entity.type,
        name: entity.name,
        namespace: entity.namespace,
        filePath: entity.filePath,
        line: entity.line,
        description: entity.description,
        metadata: entity.metadata ?? {},
      });
      ids.push(id);

      // Index for relationship resolution
      const key = `${entity.namespace}.${entity.name}`;
      this.entityNameIndex.set(key, id);
    }

    return ids;
  }

  /**
   * Add relationships to knowledge graph
   */
  private async addRelationships(
    relationships: ExtractedRelationship[]
  ): Promise<number> {
    let count = 0;

    for (const rel of relationships) {
      // Resolve source and target IDs
      const sourceKey = `${rel.sourceNamespace}.${rel.sourceName}`;
      const targetKey = `${rel.targetNamespace}.${rel.targetName}`;

      const sourceId = this.entityNameIndex.get(sourceKey);
      const targetId = this.entityNameIndex.get(targetKey);

      if (sourceId && targetId) {
        await this.yata.addRelationship(
          sourceId,
          targetId,
          rel.type,
          rel.metadata
        );
        count++;
      }
    }

    return count;
  }

  /**
   * Refresh entity name index from database
   */
  private async refreshEntityIndex(): Promise<void> {
    const result = await this.yata.query({});
    
    this.entityNameIndex.clear();
    for (const entity of result.entities) {
      const key = `${entity.namespace}.${entity.name}`;
      this.entityNameIndex.set(key, entity.id);
    }
  }

  /**
   * Get entity by name and namespace
   */
  async getEntityByName(
    name: string,
    namespace: string
  ): Promise<Entity | null> {
    const key = `${namespace}.${name}`;
    const id = this.entityNameIndex.get(key);
    
    if (id) {
      return this.yata.getEntity(id);
    }
    
    return null;
  }

  /**
   * Search entities by name pattern
   */
  async searchByName(pattern: string): Promise<Entity[]> {
    return this.yata.search(pattern);
  }
}

/**
 * Factory function
 */
export function createYataBridge(
  yata: YataLocal,
  config?: YataBridgeConfig
): YataBridge {
  return new YataBridge(yata, config);
}
