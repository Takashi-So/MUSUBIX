/**
 * @musubix/knowledge - Git-Native Knowledge Store
 * 
 * File-based knowledge graph management for MUSUBIX v3.0
 * 
 * @packageDocumentation
 */

// ============================================================
// Entity Types
// ============================================================

/**
 * Entity types in the knowledge graph
 */
export type EntityType =
  | 'requirement'
  | 'design'
  | 'task'
  | 'code'
  | 'decision'
  | 'pattern'
  | 'constraint';

/**
 * Relation types between entities
 */
export type RelationType =
  | 'implements'
  | 'depends_on'
  | 'traces_to'
  | 'related_to'
  | 'derives_from'
  | 'conflicts_with';

/**
 * Entity in the knowledge graph
 */
export interface Entity {
  /** Unique identifier (e.g., "REQ-001", "DES-001") */
  id: string;
  /** Entity type */
  type: EntityType;
  /** Display name */
  name: string;
  /** Optional description */
  description?: string;
  /** Additional properties */
  properties: Record<string, unknown>;
  /** Tags for categorization */
  tags: string[];
  /** Creation timestamp (ISO 8601) */
  createdAt: string;
  /** Last update timestamp (ISO 8601) */
  updatedAt: string;
}

/**
 * Relation between entities
 */
export interface Relation {
  /** Unique identifier */
  id: string;
  /** Source entity ID */
  source: string;
  /** Target entity ID */
  target: string;
  /** Relation type */
  type: RelationType;
  /** Additional properties */
  properties?: Record<string, unknown>;
}

/**
 * Knowledge graph structure
 */
export interface KnowledgeGraph {
  /** Schema version */
  version: '1.0.0';
  /** Metadata */
  metadata: {
    lastModified: string;
    entityCount: number;
    relationCount: number;
  };
  /** Entities by ID */
  entities: Record<string, Entity>;
  /** Relations */
  relations: Relation[];
}

// ============================================================
// Query Types
// ============================================================

/**
 * Filter for querying entities
 */
export interface QueryFilter {
  /** Filter by entity type */
  type?: EntityType | EntityType[];
  /** Filter by tags (AND) */
  tags?: string[];
  /** Filter by property values */
  properties?: Record<string, unknown>;
  /** Text search in name/description */
  text?: string;
  /** Maximum results */
  limit?: number;
  /** Offset for pagination */
  offset?: number;
}

/**
 * Options for search
 */
export interface SearchOptions {
  /** Fields to search */
  fields?: ('name' | 'description' | 'tags')[];
  /** Case sensitive search */
  caseSensitive?: boolean;
  /** Maximum results */
  limit?: number;
}

/**
 * Options for graph traversal
 */
export interface TraverseOptions {
  /** Maximum depth */
  depth?: number;
  /** Relation types to follow */
  relationTypes?: RelationType[];
  /** Direction */
  direction?: 'out' | 'in' | 'both';
}

// ============================================================
// Knowledge Store Interface
// ============================================================

/**
 * Knowledge Store interface
 */
export interface KnowledgeStore {
  // CRUD operations
  getEntity(id: string): Promise<Entity | undefined>;
  putEntity(entity: Entity): Promise<void>;
  deleteEntity(id: string): Promise<boolean>;
  
  // Relation operations
  addRelation(relation: Relation): Promise<void>;
  removeRelation(id: string): Promise<boolean>;
  getRelations(entityId: string, direction?: 'in' | 'out' | 'both'): Promise<Relation[]>;
  
  // Query
  query(filter: QueryFilter): Promise<Entity[]>;
  search(text: string, options?: SearchOptions): Promise<Entity[]>;
  
  // Graph operations
  getSubgraph(rootId: string, depth: number): Promise<KnowledgeGraph>;
  traverse(startId: string, options?: TraverseOptions): Promise<Entity[]>;
  
  // Persistence
  save(): Promise<void>;
  load(): Promise<void>;
  
  // Stats
  getStats(): { entityCount: number; relationCount: number; types: Record<EntityType, number> };
}

// ============================================================
// Factory Function
// ============================================================

/**
 * Create a new knowledge store
 */
export function createKnowledgeStore(basePath: string): KnowledgeStore {
  return new FileKnowledgeStore(basePath);
}

// ============================================================
// Implementation
// ============================================================

import * as fs from 'node:fs/promises';
import * as path from 'node:path';

/**
 * File-based knowledge store implementation
 */
export class FileKnowledgeStore implements KnowledgeStore {
  private basePath: string;
  private graph: KnowledgeGraph;
  private loaded: boolean = false;

  constructor(basePath: string) {
    this.basePath = basePath;
    this.graph = this.createEmptyGraph();
  }

  private createEmptyGraph(): KnowledgeGraph {
    return {
      version: '1.0.0',
      metadata: {
        lastModified: new Date().toISOString(),
        entityCount: 0,
        relationCount: 0,
      },
      entities: {},
      relations: [],
    };
  }

  private getGraphPath(): string {
    return path.join(this.basePath, 'graph.json');
  }

  async load(): Promise<void> {
    try {
      const content = await fs.readFile(this.getGraphPath(), 'utf-8');
      this.graph = JSON.parse(content) as KnowledgeGraph;
      this.loaded = true;
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code === 'ENOENT') {
        this.graph = this.createEmptyGraph();
        this.loaded = true;
      } else {
        throw error;
      }
    }
  }

  async save(): Promise<void> {
    await fs.mkdir(this.basePath, { recursive: true });
    this.graph.metadata.lastModified = new Date().toISOString();
    this.graph.metadata.entityCount = Object.keys(this.graph.entities).length;
    this.graph.metadata.relationCount = this.graph.relations.length;
    await fs.writeFile(
      this.getGraphPath(),
      JSON.stringify(this.graph, null, 2),
      'utf-8'
    );
  }

  async getEntity(id: string): Promise<Entity | undefined> {
    if (!this.loaded) await this.load();
    return this.graph.entities[id];
  }

  async putEntity(entity: Entity): Promise<void> {
    if (!this.loaded) await this.load();
    
    const now = new Date().toISOString();
    const existing = this.graph.entities[entity.id];
    
    this.graph.entities[entity.id] = {
      ...entity,
      createdAt: existing?.createdAt ?? now,
      updatedAt: now,
    };
  }

  async deleteEntity(id: string): Promise<boolean> {
    if (!this.loaded) await this.load();
    
    if (!this.graph.entities[id]) {
      return false;
    }
    
    delete this.graph.entities[id];
    // Remove related relations
    this.graph.relations = this.graph.relations.filter(
      r => r.source !== id && r.target !== id
    );
    return true;
  }

  async addRelation(relation: Relation): Promise<void> {
    if (!this.loaded) await this.load();
    
    // Validate entities exist
    if (!this.graph.entities[relation.source]) {
      throw new Error(`Source entity not found: ${relation.source}`);
    }
    if (!this.graph.entities[relation.target]) {
      throw new Error(`Target entity not found: ${relation.target}`);
    }
    
    // Check for duplicates
    const exists = this.graph.relations.some(
      r => r.source === relation.source && 
           r.target === relation.target && 
           r.type === relation.type
    );
    
    if (!exists) {
      this.graph.relations.push(relation);
    }
  }

  async removeRelation(id: string): Promise<boolean> {
    if (!this.loaded) await this.load();
    
    const index = this.graph.relations.findIndex(r => r.id === id);
    if (index === -1) return false;
    
    this.graph.relations.splice(index, 1);
    return true;
  }

  async getRelations(entityId: string, direction: 'in' | 'out' | 'both' = 'both'): Promise<Relation[]> {
    if (!this.loaded) await this.load();
    
    return this.graph.relations.filter(r => {
      if (direction === 'out') return r.source === entityId;
      if (direction === 'in') return r.target === entityId;
      return r.source === entityId || r.target === entityId;
    });
  }

  async query(filter: QueryFilter): Promise<Entity[]> {
    if (!this.loaded) await this.load();
    
    let results = Object.values(this.graph.entities);
    
    // Filter by type
    if (filter.type) {
      const types = Array.isArray(filter.type) ? filter.type : [filter.type];
      results = results.filter(e => types.includes(e.type));
    }
    
    // Filter by tags
    if (filter.tags && filter.tags.length > 0) {
      results = results.filter(e => 
        filter.tags!.every(tag => e.tags.includes(tag))
      );
    }
    
    // Filter by text
    if (filter.text) {
      const searchText = filter.text.toLowerCase();
      results = results.filter(e =>
        e.name.toLowerCase().includes(searchText) ||
        e.description?.toLowerCase().includes(searchText)
      );
    }
    
    // Apply pagination
    const offset = filter.offset ?? 0;
    const limit = filter.limit ?? results.length;
    
    return results.slice(offset, offset + limit);
  }

  async search(text: string, options?: SearchOptions): Promise<Entity[]> {
    if (!this.loaded) await this.load();
    
    const searchText = options?.caseSensitive ? text : text.toLowerCase();
    const fields = options?.fields ?? ['name', 'description', 'tags'];
    
    let results = Object.values(this.graph.entities).filter(e => {
      for (const field of fields) {
        if (field === 'name') {
          const value = options?.caseSensitive ? e.name : e.name.toLowerCase();
          if (value.includes(searchText)) return true;
        }
        if (field === 'description' && e.description) {
          const value = options?.caseSensitive ? e.description : e.description.toLowerCase();
          if (value.includes(searchText)) return true;
        }
        if (field === 'tags') {
          const matched = e.tags.some(tag => {
            const value = options?.caseSensitive ? tag : tag.toLowerCase();
            return value.includes(searchText);
          });
          if (matched) return true;
        }
      }
      return false;
    });
    
    if (options?.limit) {
      results = results.slice(0, options.limit);
    }
    
    return results;
  }

  async getSubgraph(rootId: string, depth: number): Promise<KnowledgeGraph> {
    if (!this.loaded) await this.load();
    
    const visited = new Set<string>();
    const entities: Record<string, Entity> = {};
    const relations: Relation[] = [];
    
    const traverse = async (id: string, currentDepth: number) => {
      if (currentDepth > depth || visited.has(id)) return;
      visited.add(id);
      
      const entity = this.graph.entities[id];
      if (!entity) return;
      
      entities[id] = entity;
      
      const rels = await this.getRelations(id, 'both');
      for (const rel of rels) {
        if (!relations.some(r => r.id === rel.id)) {
          relations.push(rel);
        }
        const nextId = rel.source === id ? rel.target : rel.source;
        await traverse(nextId, currentDepth + 1);
      }
    };
    
    await traverse(rootId, 0);
    
    return {
      version: '1.0.0',
      metadata: {
        lastModified: new Date().toISOString(),
        entityCount: Object.keys(entities).length,
        relationCount: relations.length,
      },
      entities,
      relations,
    };
  }

  async traverse(startId: string, options?: TraverseOptions): Promise<Entity[]> {
    if (!this.loaded) await this.load();
    
    const depth = options?.depth ?? 3;
    const direction = options?.direction ?? 'both';
    const relationTypes = options?.relationTypes;
    
    const visited = new Set<string>();
    const results: Entity[] = [];
    
    const visit = async (id: string, currentDepth: number) => {
      if (currentDepth > depth || visited.has(id)) return;
      visited.add(id);
      
      const entity = this.graph.entities[id];
      if (!entity) return;
      
      results.push(entity);
      
      const rels = await this.getRelations(id, direction);
      for (const rel of rels) {
        if (relationTypes && !relationTypes.includes(rel.type)) continue;
        const nextId = rel.source === id ? rel.target : rel.source;
        await visit(nextId, currentDepth + 1);
      }
    };
    
    await visit(startId, 0);
    
    return results;
  }

  getStats(): { entityCount: number; relationCount: number; types: Record<EntityType, number> } {
    const types: Record<EntityType, number> = {
      requirement: 0,
      design: 0,
      task: 0,
      code: 0,
      decision: 0,
      pattern: 0,
      constraint: 0,
    };
    
    for (const entity of Object.values(this.graph.entities)) {
      types[entity.type]++;
    }
    
    return {
      entityCount: Object.keys(this.graph.entities).length,
      relationCount: this.graph.relations.length,
      types,
    };
  }
}
