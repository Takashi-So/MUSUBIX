/**
 * YATA Local - Import/Export Module
 *
 * @packageDocumentation
 * @module @nahisaho/yata-local/io
 *
 * @see REQ-YL-IO-001 ~ REQ-YL-IO-004
 */

import * as fs from 'fs/promises';
import type {
  Entity,
  Relationship,
  Delta,
  MergeResult,
} from './types.js';
import type { YataDatabase } from './database.js';

/**
 * JSON export format
 */
export interface JsonExport {
  version: '1.0';
  exportedAt: string;
  entities: Entity[];
  relationships: Relationship[];
}

/**
 * RDF export format (N-Triples)
 */
export interface RdfExportOptions {
  baseUri?: string;
  includeMetadata?: boolean;
}

/**
 * Import/Export module for YATA Local
 */
export class IoModule {
  constructor(private db: YataDatabase) {}

  /**
   * Export graph to JSON
   * @see REQ-YL-IO-001
   */
  async exportToJson(filePath?: string): Promise<JsonExport> {
    const { entities } = this.db.queryEntities({}, 100000);
    
    const allRelationships: Relationship[] = [];
    const seenRels = new Set<string>();
    
    for (const entity of entities) {
      const rels = this.db.getRelationships(entity.id);
      for (const rel of rels) {
        if (!seenRels.has(rel.id)) {
          seenRels.add(rel.id);
          allRelationships.push(rel);
        }
      }
    }

    const exportData: JsonExport = {
      version: '1.0',
      exportedAt: new Date().toISOString(),
      entities,
      relationships: allRelationships,
    };

    if (filePath) {
      await fs.writeFile(filePath, JSON.stringify(exportData, null, 2));
    }

    return exportData;
  }

  /**
   * Import graph from JSON
   * @see REQ-YL-IO-003
   */
  async importFromJson(
    input: string | JsonExport,
    options: { merge?: boolean; dryRun?: boolean } = {}
  ): Promise<MergeResult> {
    let data: JsonExport;

    if (typeof input === 'string') {
      const content = await fs.readFile(input, 'utf-8');
      data = JSON.parse(content) as JsonExport;
    } else {
      data = input;
    }

    const result: MergeResult = {
      success: true,
      entitiesAdded: 0,
      entitiesUpdated: 0,
      entitiesSkipped: 0,
      relationshipsAdded: 0,
      relationshipsSkipped: 0,
      conflicts: [],
    };

    // Process entities
    for (const entity of data.entities) {
      const existing = this.db.getEntity(entity.id);

      if (existing) {
        if (options.merge) {
          if (!options.dryRun) {
            this.db.updateEntity(entity.id, entity);
          }
          result.entitiesUpdated++;
        } else {
          result.entitiesSkipped++;
          result.conflicts.push({
            type: 'entity',
            id: entity.id,
            reason: 'Entity already exists',
          });
        }
      } else {
        if (!options.dryRun) {
          this.db.insertEntity(entity);
        }
        result.entitiesAdded++;
      }
    }

    // Process relationships
    for (const rel of data.relationships) {
      // Check if source and target exist
      const sourceExists = this.db.getEntity(rel.sourceId);
      const targetExists = this.db.getEntity(rel.targetId);

      if (!sourceExists || !targetExists) {
        result.relationshipsSkipped++;
        result.conflicts.push({
          type: 'relationship',
          id: rel.id,
          reason: `Missing ${!sourceExists ? 'source' : 'target'} entity`,
        });
        continue;
      }

      // Check if relationship exists
      const existingRels = this.db.getRelationships(rel.sourceId, 'out');
      const exists = existingRels.some(r => r.id === rel.id);

      if (exists) {
        result.relationshipsSkipped++;
      } else {
        if (!options.dryRun) {
          this.db.insertRelationship(rel);
        }
        result.relationshipsAdded++;
      }
    }

    return result;
  }

  /**
   * Export to RDF (N-Triples format)
   * @see REQ-YL-IO-001
   */
  async exportToRdf(
    filePath?: string,
    options: RdfExportOptions = {}
  ): Promise<string> {
    const baseUri = options.baseUri ?? 'http://yata.local/';
    const includeMetadata = options.includeMetadata ?? true;

    const triples: string[] = [];

    const { entities } = this.db.queryEntities({}, 100000);

    // Entity triples
    for (const entity of entities) {
      const subject = `<${baseUri}entity/${encodeURIComponent(entity.id)}>`;

      // Type triple
      triples.push(`${subject} <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <${baseUri}type/${entity.type}> .`);

      // Name triple
      triples.push(`${subject} <http://www.w3.org/2000/01/rdf-schema#label> "${this.escapeRdfString(entity.name)}" .`);

      // Namespace triple
      if (entity.namespace) {
        triples.push(`${subject} <${baseUri}namespace> "${this.escapeRdfString(entity.namespace)}" .`);
      }

      // File path triple
      if (entity.filePath) {
        triples.push(`${subject} <${baseUri}filePath> "${this.escapeRdfString(entity.filePath)}" .`);
      }

      // Line triple
      if (entity.line !== undefined) {
        triples.push(`${subject} <${baseUri}line> "${entity.line}"^^<http://www.w3.org/2001/XMLSchema#integer> .`);
      }

      // Description triple
      if (entity.description) {
        triples.push(`${subject} <http://www.w3.org/2000/01/rdf-schema#comment> "${this.escapeRdfString(entity.description)}" .`);
      }

      // Metadata triples
      if (includeMetadata && Object.keys(entity.metadata).length > 0) {
        triples.push(`${subject} <${baseUri}metadata> "${this.escapeRdfString(JSON.stringify(entity.metadata))}" .`);
      }

      // Timestamps
      triples.push(`${subject} <http://purl.org/dc/terms/created> "${entity.createdAt.toISOString()}"^^<http://www.w3.org/2001/XMLSchema#dateTime> .`);
      triples.push(`${subject} <http://purl.org/dc/terms/modified> "${entity.updatedAt.toISOString()}"^^<http://www.w3.org/2001/XMLSchema#dateTime> .`);
    }

    // Relationship triples
    const seenRels = new Set<string>();
    for (const entity of entities) {
      const rels = this.db.getRelationships(entity.id);
      for (const rel of rels) {
        if (seenRels.has(rel.id)) continue;
        seenRels.add(rel.id);

        const subject = `<${baseUri}entity/${encodeURIComponent(rel.sourceId)}>`;
        const predicate = `<${baseUri}rel/${rel.type}>`;
        const object = `<${baseUri}entity/${encodeURIComponent(rel.targetId)}>`;

        triples.push(`${subject} ${predicate} ${object} .`);

        // Relationship metadata as reification
        if (rel.weight !== 1.0 || Object.keys(rel.metadata).length > 0) {
          const relSubject = `<${baseUri}relationship/${encodeURIComponent(rel.id)}>`;
          triples.push(`${relSubject} <http://www.w3.org/1999/02/22-rdf-syntax-ns#subject> ${subject} .`);
          triples.push(`${relSubject} <http://www.w3.org/1999/02/22-rdf-syntax-ns#predicate> ${predicate} .`);
          triples.push(`${relSubject} <http://www.w3.org/1999/02/22-rdf-syntax-ns#object> ${object} .`);

          if (rel.weight !== 1.0) {
            triples.push(`${relSubject} <${baseUri}weight> "${rel.weight}"^^<http://www.w3.org/2001/XMLSchema#float> .`);
          }

          if (Object.keys(rel.metadata).length > 0) {
            triples.push(`${relSubject} <${baseUri}metadata> "${this.escapeRdfString(JSON.stringify(rel.metadata))}" .`);
          }
        }
      }
    }

    const rdfContent = triples.join('\n');

    if (filePath) {
      await fs.writeFile(filePath, rdfContent);
    }

    return rdfContent;
  }

  /**
   * Compute delta between two states
   * @see REQ-YL-IO-004
   */
  computeDelta(
    oldState: JsonExport,
    newState: JsonExport
  ): Delta {
    const delta: Delta = {
      entities: {
        added: [],
        updated: [],
        deleted: [],
      },
      relationships: {
        added: [],
        deleted: [],
      },
      timestamp: new Date(),
    };

    // Create maps for faster lookup
    const oldEntities = new Map(oldState.entities.map(e => [e.id, e]));
    const newEntities = new Map(newState.entities.map(e => [e.id, e]));

    // Find added and updated entities
    for (const [id, newEntity] of newEntities) {
      const oldEntity = oldEntities.get(id);
      if (!oldEntity) {
        delta.entities.added.push(newEntity);
      } else if (this.entityChanged(oldEntity, newEntity)) {
        delta.entities.updated.push(newEntity);
      }
    }

    // Find deleted entities
    for (const [id] of oldEntities) {
      if (!newEntities.has(id)) {
        delta.entities.deleted.push(id);
      }
    }

    // Create maps for relationships
    const oldRels = new Map(oldState.relationships.map(r => [r.id, r]));
    const newRels = new Map(newState.relationships.map(r => [r.id, r]));

    // Find added relationships
    for (const [id, newRel] of newRels) {
      if (!oldRels.has(id)) {
        delta.relationships.added.push(newRel);
      }
    }

    // Find deleted relationships
    for (const [id] of oldRels) {
      if (!newRels.has(id)) {
        delta.relationships.deleted.push(id);
      }
    }

    return delta;
  }

  /**
   * Apply delta to current database state
   * @see REQ-YL-IO-004
   */
  async applyDelta(
    delta: Delta,
    options: { dryRun?: boolean } = {}
  ): Promise<MergeResult> {
    const result: MergeResult = {
      success: true,
      entitiesAdded: 0,
      entitiesUpdated: 0,
      entitiesSkipped: 0,
      relationshipsAdded: 0,
      relationshipsSkipped: 0,
      conflicts: [],
    };

    // Delete relationships first (foreign key constraints)
    for (const relId of delta.relationships.deleted) {
      if (!options.dryRun) {
        this.db.deleteRelationship(relId);
      }
    }

    // Delete entities
    for (const entityId of delta.entities.deleted) {
      if (!options.dryRun) {
        this.db.deleteEntity(entityId);
      }
    }

    // Add entities
    for (const entity of delta.entities.added) {
      if (!options.dryRun) {
        this.db.insertEntity(entity);
      }
      result.entitiesAdded++;
    }

    // Update entities
    for (const entity of delta.entities.updated) {
      if (!options.dryRun) {
        this.db.updateEntity(entity.id, entity);
      }
      result.entitiesUpdated++;
    }

    // Add relationships
    for (const rel of delta.relationships.added) {
      const sourceExists = this.db.getEntity(rel.sourceId);
      const targetExists = this.db.getEntity(rel.targetId);

      if (!sourceExists || !targetExists) {
        result.relationshipsSkipped++;
        result.conflicts.push({
          type: 'relationship',
          id: rel.id,
          reason: `Missing ${!sourceExists ? 'source' : 'target'} entity`,
        });
        continue;
      }

      if (!options.dryRun) {
        this.db.insertRelationship(rel);
      }
      result.relationshipsAdded++;
    }

    return result;
  }

  /**
   * Sync with another YATA Local instance
   * @see REQ-YL-IO-004
   */
  async syncWith(
    other: YataDatabase,
    since: Date
  ): Promise<MergeResult> {
    // Get changes from other database
    const otherChanges = other.getChangesSince(since);

    const result: MergeResult = {
      success: true,
      entitiesAdded: 0,
      entitiesUpdated: 0,
      entitiesSkipped: 0,
      relationshipsAdded: 0,
      relationshipsSkipped: 0,
      conflicts: [],
    };

    // Apply entity changes
    for (const entity of otherChanges.entities.added) {
      const existing = this.db.getEntity(entity.id);
      if (existing) {
        // Conflict: choose newer
        if (entity.updatedAt > existing.updatedAt) {
          this.db.updateEntity(entity.id, entity);
          result.entitiesUpdated++;
        } else {
          result.entitiesSkipped++;
        }
      } else {
        this.db.insertEntity(entity);
        result.entitiesAdded++;
      }
    }

    for (const entity of otherChanges.entities.updated) {
      const existing = this.db.getEntity(entity.id);
      if (existing) {
        if (entity.updatedAt > existing.updatedAt) {
          this.db.updateEntity(entity.id, entity);
          result.entitiesUpdated++;
        } else {
          result.entitiesSkipped++;
        }
      } else {
        this.db.insertEntity(entity);
        result.entitiesAdded++;
      }
    }

    for (const entityId of otherChanges.entities.deleted) {
      this.db.deleteEntity(entityId);
    }

    // Apply relationship changes
    for (const rel of otherChanges.relationships.added) {
      const sourceExists = this.db.getEntity(rel.sourceId);
      const targetExists = this.db.getEntity(rel.targetId);

      if (sourceExists && targetExists) {
        this.db.insertRelationship(rel);
        result.relationshipsAdded++;
      } else {
        result.relationshipsSkipped++;
      }
    }

    for (const relId of otherChanges.relationships.deleted) {
      this.db.deleteRelationship(relId);
    }

    return result;
  }

  /**
   * Check if entity has changed
   */
  private entityChanged(oldEntity: Entity, newEntity: Entity): boolean {
    return (
      oldEntity.name !== newEntity.name ||
      oldEntity.namespace !== newEntity.namespace ||
      oldEntity.type !== newEntity.type ||
      oldEntity.filePath !== newEntity.filePath ||
      oldEntity.line !== newEntity.line ||
      oldEntity.description !== newEntity.description ||
      JSON.stringify(oldEntity.metadata) !== JSON.stringify(newEntity.metadata)
    );
  }

  /**
   * Escape string for RDF N-Triples format
   */
  private escapeRdfString(str: string): string {
    return str
      .replace(/\\/g, '\\\\')
      .replace(/"/g, '\\"')
      .replace(/\n/g, '\\n')
      .replace(/\r/g, '\\r')
      .replace(/\t/g, '\\t');
  }
}
