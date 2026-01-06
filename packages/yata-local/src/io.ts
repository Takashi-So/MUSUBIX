/**
 * YATA Local - Import/Export Module
 *
 * @packageDocumentation
 * @module @nahisaho/yata-local/io
 *
 * @see REQ-YL-IO-001 ~ REQ-YL-IO-004
 * @see REQ-YI-EXP-001 ~ REQ-YI-EXP-003 (v1.7.0 Enhanced)
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
 * Enhanced JSON export format (v1.7.0)
 * @see REQ-YI-EXP-001
 */
export interface EnhancedJsonExport {
  version: '2.0';
  exportedAt: string;
  namespace?: string;
  incremental: boolean;
  since?: string;
  stats: {
    entityCount: number;
    relationshipCount: number;
    exportTimeMs: number;
  };
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
 * Enhanced export options (v1.7.0)
 * @see REQ-YI-EXP-001
 */
export interface ExportOptions {
  /** Export format */
  format: 'json' | 'rdf' | 'graphml';
  /** Filter by namespace */
  namespace?: string;
  /** Include metadata in export */
  includeMetadata?: boolean;
  /** Incremental export since date */
  since?: Date;
  /** Output file path (optional) */
  outputPath?: string;
}

/**
 * Enhanced import options (v1.7.0)
 * @see REQ-YI-EXP-002
 */
export interface ImportOptions {
  /** Import format */
  format: 'json' | 'rdf' | 'graphml';
  /** Merge strategy for conflicts */
  mergeStrategy: 'skip' | 'overwrite' | 'merge';
  /** Dry run without actual changes */
  dryRun?: boolean;
}

/**
 * Export result (v1.7.0)
 * @see REQ-YI-EXP-001
 */
export interface ExportResult {
  success: boolean;
  format: 'json' | 'rdf' | 'graphml';
  entityCount: number;
  relationshipCount: number;
  fileSize: number;
  exportTimeMs: number;
  outputPath?: string;
  content?: string;
}

/**
 * Import result (v1.7.0)
 * @see REQ-YI-EXP-002
 */
export interface ImportResult {
  success: boolean;
  format: 'json' | 'rdf' | 'graphml';
  entitiesCreated: number;
  entitiesUpdated: number;
  entitiesSkipped: number;
  relationshipsCreated: number;
  relationshipsSkipped: number;
  errors: Array<{ id: string; reason: string }>;
  importTimeMs: number;
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

  // ============================================================
  // Enhanced Export API (v1.7.0)
  // @see REQ-YI-EXP-001, REQ-YI-EXP-002, REQ-YI-EXP-003
  // ============================================================

  /**
   * Unified export API supporting multiple formats
   * Performance target: 30 seconds for up to 100,000 entities
   *
   * @param options - Export options
   * @returns Export result with content or file path
   *
   * @see REQ-YI-EXP-001
   */
  async export(options: ExportOptions): Promise<ExportResult> {
    const startTime = Date.now();

    // Get entities (filtered by namespace if specified)
    let entities: Entity[];
    if (options.namespace) {
      const result = this.db.queryEntities({ namespace: options.namespace }, 100000);
      entities = result.entities;
    } else {
      const result = this.db.queryEntities({}, 100000);
      entities = result.entities;
    }

    // Filter by date if incremental
    if (options.since) {
      const sinceDate = options.since;
      entities = entities.filter(e => e.updatedAt >= sinceDate);
    }

    // Get relationships for filtered entities
    const entityIds = new Set(entities.map(e => e.id));
    const relationships: Relationship[] = [];
    const seenRels = new Set<string>();

    for (const entity of entities) {
      const rels = this.db.getRelationships(entity.id);
      for (const rel of rels) {
        if (!seenRels.has(rel.id) && entityIds.has(rel.sourceId) && entityIds.has(rel.targetId)) {
          seenRels.add(rel.id);
          relationships.push(rel);
        }
      }
    }

    let content: string;

    switch (options.format) {
      case 'json':
        content = this.formatAsEnhancedJson(entities, relationships, options, startTime);
        break;
      case 'rdf':
        content = this.formatAsRdf(entities, relationships, options);
        break;
      case 'graphml':
        content = this.formatAsGraphML(entities, relationships, options);
        break;
      default:
        throw new Error(`Unsupported export format: ${options.format}`);
    }

    const exportTimeMs = Date.now() - startTime;
    const fileSize = Buffer.byteLength(content, 'utf-8');

    // Write to file if path specified
    if (options.outputPath) {
      await fs.writeFile(options.outputPath, content);
    }

    return {
      success: true,
      format: options.format,
      entityCount: entities.length,
      relationshipCount: relationships.length,
      fileSize,
      exportTimeMs,
      outputPath: options.outputPath,
      content: options.outputPath ? undefined : content,
    };
  }

  /**
   * Unified import API supporting multiple formats
   *
   * @param input - File path or content string
   * @param options - Import options
   * @returns Import result with statistics
   *
   * @see REQ-YI-EXP-002
   */
  async import(
    input: string,
    options: ImportOptions
  ): Promise<ImportResult> {
    const startTime = Date.now();

    // Read file if input is a path
    let content: string;
    try {
      await fs.access(input);
      content = await fs.readFile(input, 'utf-8');
    } catch {
      // Treat as content string
      content = input;
    }

    let result: ImportResult;

    switch (options.format) {
      case 'json':
        result = await this.importFromEnhancedJson(content, options);
        break;
      case 'graphml':
        result = await this.importFromGraphML(content, options);
        break;
      case 'rdf':
        result = await this.importFromRdfContent(content, options);
        break;
      default:
        throw new Error(`Unsupported import format: ${options.format}`);
    }

    result.importTimeMs = Date.now() - startTime;
    return result;
  }

  /**
   * Export incremental changes since a specific date
   *
   * @param since - Export changes since this date
   * @param options - Export options
   * @returns Export result
   *
   * @see REQ-YI-EXP-003
   */
  async exportIncremental(
    since: Date,
    options: Omit<ExportOptions, 'since'> = { format: 'json' }
  ): Promise<ExportResult> {
    return this.export({ ...options, since });
  }

  // ============================================================
  // Format Helpers
  // ============================================================

  /**
   * Format as enhanced JSON (v2.0)
   */
  private formatAsEnhancedJson(
    entities: Entity[],
    relationships: Relationship[],
    options: ExportOptions,
    startTime: number
  ): string {
    const exportData: EnhancedJsonExport = {
      version: '2.0',
      exportedAt: new Date().toISOString(),
      namespace: options.namespace,
      incremental: !!options.since,
      since: options.since?.toISOString(),
      stats: {
        entityCount: entities.length,
        relationshipCount: relationships.length,
        exportTimeMs: Date.now() - startTime,
      },
      entities,
      relationships,
    };

    return JSON.stringify(exportData, null, 2);
  }

  /**
   * Format as RDF (N-Triples)
   */
  private formatAsRdf(
    entities: Entity[],
    relationships: Relationship[],
    options: ExportOptions
  ): string {
    const baseUri = 'http://yata.local/';
    const includeMetadata = options.includeMetadata ?? true;
    const triples: string[] = [];

    // Entity triples
    for (const entity of entities) {
      const subject = `<${baseUri}entity/${encodeURIComponent(entity.id)}>`;

      triples.push(`${subject} <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <${baseUri}type/${entity.type}> .`);
      triples.push(`${subject} <http://www.w3.org/2000/01/rdf-schema#label> "${this.escapeRdfString(entity.name)}" .`);

      if (entity.namespace) {
        triples.push(`${subject} <${baseUri}namespace> "${this.escapeRdfString(entity.namespace)}" .`);
      }

      if (entity.filePath) {
        triples.push(`${subject} <${baseUri}filePath> "${this.escapeRdfString(entity.filePath)}" .`);
      }

      if (entity.description) {
        triples.push(`${subject} <http://www.w3.org/2000/01/rdf-schema#comment> "${this.escapeRdfString(entity.description)}" .`);
      }

      if (includeMetadata && Object.keys(entity.metadata).length > 0) {
        triples.push(`${subject} <${baseUri}metadata> "${this.escapeRdfString(JSON.stringify(entity.metadata))}" .`);
      }
    }

    // Relationship triples
    for (const rel of relationships) {
      const subject = `<${baseUri}entity/${encodeURIComponent(rel.sourceId)}>`;
      const predicate = `<${baseUri}rel/${rel.type}>`;
      const object = `<${baseUri}entity/${encodeURIComponent(rel.targetId)}>`;

      triples.push(`${subject} ${predicate} ${object} .`);
    }

    return triples.join('\n');
  }

  /**
   * Format as GraphML
   * @see REQ-YI-EXP-001
   */
  private formatAsGraphML(
    entities: Entity[],
    relationships: Relationship[],
    options: ExportOptions
  ): string {
    const includeMetadata = options.includeMetadata ?? true;
    const lines: string[] = [];

    // XML header
    lines.push('<?xml version="1.0" encoding="UTF-8"?>');
    lines.push('<graphml xmlns="http://graphml.graphdrawing.org/xmlns"');
    lines.push('         xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"');
    lines.push('         xsi:schemaLocation="http://graphml.graphdrawing.org/xmlns');
    lines.push('         http://graphml.graphdrawing.org/xmlns/1.0/graphml.xsd">');

    // Define node attributes
    lines.push('  <key id="type" for="node" attr.name="type" attr.type="string"/>');
    lines.push('  <key id="name" for="node" attr.name="name" attr.type="string"/>');
    lines.push('  <key id="namespace" for="node" attr.name="namespace" attr.type="string"/>');
    lines.push('  <key id="filePath" for="node" attr.name="filePath" attr.type="string"/>');
    lines.push('  <key id="description" for="node" attr.name="description" attr.type="string"/>');
    if (includeMetadata) {
      lines.push('  <key id="metadata" for="node" attr.name="metadata" attr.type="string"/>');
    }

    // Define edge attributes
    lines.push('  <key id="relType" for="edge" attr.name="type" attr.type="string"/>');
    lines.push('  <key id="weight" for="edge" attr.name="weight" attr.type="double"/>');

    // Graph element
    lines.push('  <graph id="G" edgedefault="directed">');

    // Nodes (entities)
    for (const entity of entities) {
      lines.push(`    <node id="${this.escapeXml(entity.id)}">`);
      lines.push(`      <data key="type">${this.escapeXml(entity.type)}</data>`);
      lines.push(`      <data key="name">${this.escapeXml(entity.name)}</data>`);
      lines.push(`      <data key="namespace">${this.escapeXml(entity.namespace)}</data>`);
      if (entity.filePath) {
        lines.push(`      <data key="filePath">${this.escapeXml(entity.filePath)}</data>`);
      }
      if (entity.description) {
        lines.push(`      <data key="description">${this.escapeXml(entity.description)}</data>`);
      }
      if (includeMetadata && Object.keys(entity.metadata).length > 0) {
        lines.push(`      <data key="metadata">${this.escapeXml(JSON.stringify(entity.metadata))}</data>`);
      }
      lines.push('    </node>');
    }

    // Edges (relationships)
    for (const rel of relationships) {
      lines.push(`    <edge id="${this.escapeXml(rel.id)}" source="${this.escapeXml(rel.sourceId)}" target="${this.escapeXml(rel.targetId)}">`);
      lines.push(`      <data key="relType">${this.escapeXml(rel.type)}</data>`);
      lines.push(`      <data key="weight">${rel.weight}</data>`);
      lines.push('    </edge>');
    }

    lines.push('  </graph>');
    lines.push('</graphml>');

    return lines.join('\n');
  }

  /**
   * Escape XML special characters
   */
  private escapeXml(str: string): string {
    return str
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&apos;');
  }

  /**
   * Import from enhanced JSON content
   */
  private async importFromEnhancedJson(
    content: string,
    options: ImportOptions
  ): Promise<ImportResult> {
    const data = JSON.parse(content) as JsonExport | EnhancedJsonExport;
    const result: ImportResult = {
      success: true,
      format: 'json',
      entitiesCreated: 0,
      entitiesUpdated: 0,
      entitiesSkipped: 0,
      relationshipsCreated: 0,
      relationshipsSkipped: 0,
      errors: [],
      importTimeMs: 0,
    };

    // Process entities
    for (const rawEntity of data.entities) {
      // Convert date strings to Date objects
      const entity: Entity = {
        ...rawEntity,
        createdAt: rawEntity.createdAt instanceof Date ? rawEntity.createdAt : new Date(rawEntity.createdAt as unknown as string),
        updatedAt: rawEntity.updatedAt instanceof Date ? rawEntity.updatedAt : new Date(rawEntity.updatedAt as unknown as string),
      };

      const existing = this.db.getEntity(entity.id);

      if (existing) {
        switch (options.mergeStrategy) {
          case 'skip':
            result.entitiesSkipped++;
            break;
          case 'overwrite':
            if (!options.dryRun) {
              this.db.updateEntity(entity.id, entity);
            }
            result.entitiesUpdated++;
            break;
          case 'merge':
            if (!options.dryRun) {
              // Merge metadata
              const merged = {
                ...entity,
                metadata: { ...existing.metadata, ...entity.metadata },
              };
              this.db.updateEntity(entity.id, merged);
            }
            result.entitiesUpdated++;
            break;
        }
      } else {
        if (!options.dryRun) {
          this.db.insertEntity(entity);
        }
        result.entitiesCreated++;
      }
    }

    // Process relationships
    for (const rawRel of data.relationships) {
      // Convert date strings to Date objects
      const rel: Relationship = {
        ...rawRel,
        createdAt: rawRel.createdAt instanceof Date ? rawRel.createdAt : new Date(rawRel.createdAt as unknown as string),
      };

      const sourceExists = this.db.getEntity(rel.sourceId);
      const targetExists = this.db.getEntity(rel.targetId);

      if (!sourceExists || !targetExists) {
        result.relationshipsSkipped++;
        result.errors.push({
          id: rel.id,
          reason: `Missing ${!sourceExists ? 'source' : 'target'} entity`,
        });
        continue;
      }

      const existingRels = this.db.getRelationships(rel.sourceId, 'out');
      const exists = existingRels.some(r => r.id === rel.id);

      if (exists) {
        result.relationshipsSkipped++;
      } else {
        if (!options.dryRun) {
          this.db.insertRelationship(rel);
        }
        result.relationshipsCreated++;
      }
    }

    return result;
  }

  /**
   * Import from GraphML content
   * @see REQ-YI-EXP-002
   */
  private async importFromGraphML(
    content: string,
    options: ImportOptions
  ): Promise<ImportResult> {
    const result: ImportResult = {
      success: true,
      format: 'graphml',
      entitiesCreated: 0,
      entitiesUpdated: 0,
      entitiesSkipped: 0,
      relationshipsCreated: 0,
      relationshipsSkipped: 0,
      errors: [],
      importTimeMs: 0,
    };

    // Simple XML parsing (regex-based for portability)
    const nodeRegex = /<node id="([^"]+)"[^>]*>([\s\S]*?)<\/node>/g;
    const edgeRegex = /<edge id="([^"]+)" source="([^"]+)" target="([^"]+)"[^>]*>([\s\S]*?)<\/edge>/g;
    const dataRegex = /<data key="([^"]+)">([^<]*)<\/data>/g;

    // Parse nodes
    let nodeMatch;
    while ((nodeMatch = nodeRegex.exec(content)) !== null) {
      const id = this.unescapeXml(nodeMatch[1]);
      const nodeContent = nodeMatch[2];

      const attributes: Record<string, string> = {};
      let dataMatch;
      while ((dataMatch = dataRegex.exec(nodeContent)) !== null) {
        attributes[dataMatch[1]] = this.unescapeXml(dataMatch[2]);
      }

      const entity: Entity = {
        id,
        type: (attributes['type'] || 'unknown') as Entity['type'],
        name: attributes['name'] || id,
        namespace: attributes['namespace'] || '',
        filePath: attributes['filePath'],
        description: attributes['description'],
        metadata: attributes['metadata'] ? JSON.parse(attributes['metadata']) : {},
        createdAt: new Date(),
        updatedAt: new Date(),
      };

      const existing = this.db.getEntity(id);

      if (existing) {
        switch (options.mergeStrategy) {
          case 'skip':
            result.entitiesSkipped++;
            break;
          case 'overwrite':
          case 'merge':
            if (!options.dryRun) {
              this.db.updateEntity(id, entity);
            }
            result.entitiesUpdated++;
            break;
        }
      } else {
        if (!options.dryRun) {
          this.db.insertEntity(entity);
        }
        result.entitiesCreated++;
      }
    }

    // Parse edges
    let edgeMatch;
    while ((edgeMatch = edgeRegex.exec(content)) !== null) {
      const id = this.unescapeXml(edgeMatch[1]);
      const sourceId = this.unescapeXml(edgeMatch[2]);
      const targetId = this.unescapeXml(edgeMatch[3]);
      const edgeContent = edgeMatch[4];

      const attributes: Record<string, string> = {};
      let dataMatch;
      while ((dataMatch = dataRegex.exec(edgeContent)) !== null) {
        attributes[dataMatch[1]] = this.unescapeXml(dataMatch[2]);
      }

      const rel: Relationship = {
        id,
        sourceId,
        targetId,
        type: (attributes['relType'] || 'related') as Relationship['type'],
        weight: parseFloat(attributes['weight'] || '1.0'),
        metadata: {},
        createdAt: new Date(),
      };

      const sourceExists = this.db.getEntity(sourceId);
      const targetExists = this.db.getEntity(targetId);

      if (!sourceExists || !targetExists) {
        result.relationshipsSkipped++;
        result.errors.push({
          id,
          reason: `Missing ${!sourceExists ? 'source' : 'target'} entity`,
        });
        continue;
      }

      if (!options.dryRun) {
        try {
          this.db.insertRelationship(rel);
          result.relationshipsCreated++;
        } catch {
          result.relationshipsSkipped++;
        }
      } else {
        result.relationshipsCreated++;
      }
    }

    return result;
  }

  /**
   * Import from RDF content (N-Triples)
   */
  private async importFromRdfContent(
    content: string,
    options: ImportOptions
  ): Promise<ImportResult> {
    const result: ImportResult = {
      success: true,
      format: 'rdf',
      entitiesCreated: 0,
      entitiesUpdated: 0,
      entitiesSkipped: 0,
      relationshipsCreated: 0,
      relationshipsSkipped: 0,
      errors: [],
      importTimeMs: 0,
    };

    // Parse N-Triples
    const lines = content.split('\n').filter(line => line.trim() && !line.startsWith('#'));
    const tripleRegex = /<([^>]+)>\s+<([^>]+)>\s+(?:<([^>]+)>|"([^"]*)"(?:\^\^<[^>]+>)?)\s*\./;

    const entityMap = new Map<string, Partial<Entity>>();

    for (const line of lines) {
      const match = tripleRegex.exec(line);
      if (!match) continue;

      const subject = match[1];
      const predicate = match[2];
      const objectUri = match[3];
      const objectLiteral = match[4];

      // Extract entity ID from URI
      const entityIdMatch = subject.match(/entity\/([^/]+)$/);
      if (!entityIdMatch) continue;

      const entityId = decodeURIComponent(entityIdMatch[1]);

      if (!entityMap.has(entityId)) {
        entityMap.set(entityId, {
          id: entityId,
          metadata: {},
          createdAt: new Date(),
          updatedAt: new Date(),
        });
      }

      const entity = entityMap.get(entityId)!;

      // Handle predicates
      if (predicate.includes('type') && objectUri) {
        const typeMatch = objectUri.match(/type\/([^/]+)$/);
        if (typeMatch) {
          entity.type = typeMatch[1] as Entity['type'];
        }
      } else if (predicate.includes('label')) {
        entity.name = objectLiteral || '';
      } else if (predicate.includes('namespace')) {
        entity.namespace = objectLiteral || '';
      } else if (predicate.includes('filePath')) {
        entity.filePath = objectLiteral;
      } else if (predicate.includes('comment')) {
        entity.description = objectLiteral;
      }
    }

    // Import entities
    for (const [id, partialEntity] of entityMap) {
      const entity: Entity = {
        id,
        type: partialEntity.type || 'unknown',
        name: partialEntity.name || id,
        namespace: partialEntity.namespace || '',
        filePath: partialEntity.filePath,
        description: partialEntity.description,
        metadata: partialEntity.metadata || {},
        createdAt: partialEntity.createdAt || new Date(),
        updatedAt: partialEntity.updatedAt || new Date(),
      } as Entity;

      const existing = this.db.getEntity(id);

      if (existing) {
        switch (options.mergeStrategy) {
          case 'skip':
            result.entitiesSkipped++;
            break;
          case 'overwrite':
          case 'merge':
            if (!options.dryRun) {
              this.db.updateEntity(id, entity);
            }
            result.entitiesUpdated++;
            break;
        }
      } else {
        if (!options.dryRun) {
          this.db.insertEntity(entity);
        }
        result.entitiesCreated++;
      }
    }

    return result;
  }

  /**
   * Unescape XML special characters
   */
  private unescapeXml(str: string): string {
    return str
      .replace(/&amp;/g, '&')
      .replace(/&lt;/g, '<')
      .replace(/&gt;/g, '>')
      .replace(/&quot;/g, '"')
      .replace(/&apos;/g, "'");
  }
}
