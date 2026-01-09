/**
 * @nahisaho/musubix-codegraph - SQLite Storage Implementation
 *
 * Persistent SQLite-based storage adapter for CodeGraph
 *
 * @see REQ-CG-API-005
 * @see DES-CG-006
 * @see TSK-CG-052
 */

import type {
  StorageAdapter,
  StorageStats,
  Entity,
  Relation,
  GraphQuery,
  RelationType,
} from '../types.js';
import * as fs from 'fs/promises';
import * as path from 'path';

// Better-sqlite3 dynamic import type
type Database = {
  prepare(sql: string): Statement;
  exec(sql: string): void;
  close(): void;
  transaction<T>(fn: () => T): () => T;
};

type Statement = {
  run(...params: unknown[]): { changes: number; lastInsertRowid: number | bigint };
  get(...params: unknown[]): unknown;
  all(...params: unknown[]): unknown[];
};

/**
 * SQLite storage adapter
 *
 * Stores entities and relations in SQLite database for persistence.
 *
 * @example
 * ```typescript
 * const storage = new SQLiteStorage('.codegraph/index.db');
 * await storage.initialize();
 *
 * await storage.saveEntity(entity);
 * const retrieved = await storage.getEntity(entity.id);
 * ```
 */
export class SQLiteStorage implements StorageAdapter {
  private dbPath: string;
  private db: Database | null = null;
  private initialized = false;

  constructor(dbPath: string = '.codegraph/index.db') {
    this.dbPath = dbPath;
  }

  /**
   * Initialize the database
   */
  async initialize(): Promise<void> {
    if (this.initialized) return;

    // Ensure directory exists
    const dir = path.dirname(this.dbPath);
    await fs.mkdir(dir, { recursive: true });

    // Dynamic import of better-sqlite3
    try {
      const BetterSqlite3 = (await import('better-sqlite3')).default;
      this.db = new BetterSqlite3(this.dbPath) as unknown as Database;

      // Create tables
      this.db.exec(`
        CREATE TABLE IF NOT EXISTS entities (
          id TEXT PRIMARY KEY,
          name TEXT NOT NULL,
          type TEXT NOT NULL,
          language TEXT,
          file_path TEXT,
          start_line INTEGER,
          end_line INTEGER,
          source_code TEXT,
          docstring TEXT,
          signature TEXT,
          qualified_name TEXT,
          namespace TEXT,
          community_id TEXT,
          metadata TEXT,
          created_at TEXT DEFAULT CURRENT_TIMESTAMP,
          updated_at TEXT DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS relations (
          id TEXT PRIMARY KEY,
          source_id TEXT NOT NULL,
          target_id TEXT NOT NULL,
          type TEXT NOT NULL,
          weight REAL DEFAULT 1.0,
          metadata TEXT,
          created_at TEXT DEFAULT CURRENT_TIMESTAMP,
          FOREIGN KEY (source_id) REFERENCES entities(id) ON DELETE CASCADE,
          FOREIGN KEY (target_id) REFERENCES entities(id) ON DELETE CASCADE
        );

        CREATE INDEX IF NOT EXISTS idx_entities_name ON entities(name);
        CREATE INDEX IF NOT EXISTS idx_entities_type ON entities(type);
        CREATE INDEX IF NOT EXISTS idx_entities_file_path ON entities(file_path);
        CREATE INDEX IF NOT EXISTS idx_relations_source ON relations(source_id);
        CREATE INDEX IF NOT EXISTS idx_relations_target ON relations(target_id);
        CREATE INDEX IF NOT EXISTS idx_relations_type ON relations(type);
      `);

      this.initialized = true;
    } catch (error) {
      throw new Error(`Failed to initialize SQLite: ${error instanceof Error ? error.message : String(error)}`);
    }
  }

  /**
   * Close the database connection
   */
  async close(): Promise<void> {
    if (this.db) {
      this.db.close();
      this.db = null;
    }
    this.initialized = false;
  }

  // =========================================================================
  // Entity Operations
  // =========================================================================

  /**
   * Save an entity
   */
  async saveEntity(entity: Entity): Promise<void> {
    this.ensureInitialized();

    const stmt = this.db!.prepare(`
      INSERT OR REPLACE INTO entities (
        id, name, type, language, file_path, start_line, end_line,
        source_code, docstring, signature, qualified_name, namespace,
        community_id, metadata, updated_at
      ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
    `);

    stmt.run(
      entity.id,
      entity.name,
      entity.type,
      entity.language ?? null,
      entity.filePath ?? null,
      entity.startLine ?? null,
      entity.endLine ?? null,
      entity.sourceCode ?? null,
      entity.docstring ?? null,
      entity.signature ?? null,
      entity.qualifiedName ?? null,
      entity.namespace ?? null,
      entity.communityId ?? null,
      entity.metadata ? JSON.stringify(entity.metadata) : '{}'
    );
  }

  /**
   * Get an entity by ID
   */
  async getEntity(id: string): Promise<Entity | null> {
    this.ensureInitialized();

    const stmt = this.db!.prepare('SELECT * FROM entities WHERE id = ?');
    const row = stmt.get(id) as EntityRow | undefined;

    return row ? this.rowToEntity(row) : null;
  }

  /**
   * Query entities
   */
  async queryEntities(query: GraphQuery): Promise<Entity[]> {
    this.ensureInitialized();

    const conditions: string[] = ['1=1'];
    const params: unknown[] = [];

    // Filter by entity types
    if (query.entityTypes && query.entityTypes.length > 0) {
      const placeholders = query.entityTypes.map(() => '?').join(',');
      conditions.push(`type IN (${placeholders})`);
      params.push(...query.entityTypes);
    }

    // Filter by file path
    if (query.filePath) {
      conditions.push('LOWER(file_path) = LOWER(?)');
      params.push(query.filePath);
    }

    // Filter by namespace
    if (query.namespace) {
      conditions.push('namespace = ?');
      params.push(query.namespace);
    }

    // Filter by name pattern
    if (query.namePattern) {
      conditions.push('name GLOB ?');
      params.push(query.namePattern);
    }

    // Text search
    if (query.textSearch) {
      conditions.push(`(
        name LIKE ? OR
        id LIKE ? OR
        docstring LIKE ?
      )`);
      const searchPattern = `%${query.textSearch}%`;
      params.push(searchPattern, searchPattern, searchPattern);
    }

    let sql = `SELECT * FROM entities WHERE ${conditions.join(' AND ')}`;

    // Apply limit
    if (query.limit && query.limit > 0) {
      sql += ` LIMIT ?`;
      params.push(query.limit);
    }

    // Apply offset
    if (query.offset && query.offset > 0) {
      sql += ` OFFSET ?`;
      params.push(query.offset);
    }

    const stmt = this.db!.prepare(sql);
    const rows = stmt.all(...params) as EntityRow[];

    return rows.map(row => this.rowToEntity(row));
  }

  /**
   * Delete an entity
   */
  async deleteEntity(id: string): Promise<void> {
    this.ensureInitialized();

    // Delete relations first (SQLite CASCADE should handle this, but be explicit)
    const deleteRelations = this.db!.prepare(
      'DELETE FROM relations WHERE source_id = ? OR target_id = ?'
    );
    deleteRelations.run(id, id);

    // Delete entity
    const deleteEntity = this.db!.prepare('DELETE FROM entities WHERE id = ?');
    deleteEntity.run(id);
  }

  // =========================================================================
  // Relation Operations
  // =========================================================================

  /**
   * Save a relation
   */
  async saveRelation(relation: Relation): Promise<void> {
    this.ensureInitialized();

    const stmt = this.db!.prepare(`
      INSERT OR REPLACE INTO relations (id, source_id, target_id, type, weight, metadata)
      VALUES (?, ?, ?, ?, ?, ?)
    `);

    stmt.run(
      relation.id,
      relation.sourceId,
      relation.targetId,
      relation.type,
      relation.weight,
      relation.metadata ? JSON.stringify(relation.metadata) : '{}'
    );
  }

  /**
   * Get relations for an entity
   */
  async getRelations(
    entityId: string,
    direction: 'in' | 'out' | 'both' = 'both'
  ): Promise<Relation[]> {
    this.ensureInitialized();

    let sql: string;
    let params: string[];

    switch (direction) {
      case 'out':
        sql = 'SELECT * FROM relations WHERE source_id = ?';
        params = [entityId];
        break;
      case 'in':
        sql = 'SELECT * FROM relations WHERE target_id = ?';
        params = [entityId];
        break;
      default:
        sql = 'SELECT * FROM relations WHERE source_id = ? OR target_id = ?';
        params = [entityId, entityId];
    }

    const stmt = this.db!.prepare(sql);
    const rows = stmt.all(...params) as RelationRow[];

    return rows.map(row => this.rowToRelation(row));
  }

  /**
   * Delete a relation
   */
  async deleteRelation(id: string): Promise<void> {
    this.ensureInitialized();

    const stmt = this.db!.prepare('DELETE FROM relations WHERE id = ?');
    stmt.run(id);
  }

  // =========================================================================
  // Bulk Operations
  // =========================================================================

  /**
   * Bulk save entities and relations
   */
  async bulkSave(entities: Entity[], relations: Relation[]): Promise<void> {
    this.ensureInitialized();

    const saveEntitiesAndRelations = this.db!.transaction(() => {
      for (const entity of entities) {
        const stmt = this.db!.prepare(`
          INSERT OR REPLACE INTO entities (
            id, name, type, language, file_path, start_line, end_line,
            source_code, docstring, signature, qualified_name, namespace,
            community_id, metadata, updated_at
          ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
        `);
        stmt.run(
          entity.id,
          entity.name,
          entity.type,
          entity.language ?? null,
          entity.filePath ?? null,
          entity.startLine ?? null,
          entity.endLine ?? null,
          entity.sourceCode ?? null,
          entity.docstring ?? null,
          entity.signature ?? null,
          entity.qualifiedName ?? null,
          entity.namespace ?? null,
          entity.communityId ?? null,
          entity.metadata ? JSON.stringify(entity.metadata) : '{}'
        );
      }

      for (const relation of relations) {
        const stmt = this.db!.prepare(`
          INSERT OR REPLACE INTO relations (id, source_id, target_id, type, weight, metadata)
          VALUES (?, ?, ?, ?, ?, ?)
        `);
        stmt.run(
          relation.id,
          relation.sourceId,
          relation.targetId,
          relation.type,
          relation.weight,
          relation.metadata ? JSON.stringify(relation.metadata) : '{}'
        );
      }
    });

    saveEntitiesAndRelations();
  }

  /**
   * Clear all data
   */
  async clear(): Promise<void> {
    this.ensureInitialized();

    this.db!.exec(`
      DELETE FROM relations;
      DELETE FROM entities;
    `);
  }

  // =========================================================================
  // Statistics
  // =========================================================================

  /**
   * Get storage statistics
   */
  async getStats(): Promise<StorageStats> {
    this.ensureInitialized();

    const entityCount = this.db!.prepare('SELECT COUNT(*) as count FROM entities').get() as { count: number };
    const relationCount = this.db!.prepare('SELECT COUNT(*) as count FROM relations').get() as { count: number };
    const fileCount = this.db!.prepare('SELECT COUNT(DISTINCT file_path) as count FROM entities WHERE file_path IS NOT NULL').get() as { count: number };

    return {
      entityCount: entityCount.count,
      relationCount: relationCount.count,
      fileCount: fileCount.count,
    };
  }

  // =========================================================================
  // Helper Methods
  // =========================================================================

  private ensureInitialized(): void {
    if (!this.initialized || !this.db) {
      throw new Error('SQLite storage not initialized. Call initialize() first.');
    }
  }

  private rowToEntity(row: EntityRow): Entity {
    return {
      id: row.id,
      name: row.name,
      type: row.type as Entity['type'],
      language: row.language as Entity['language'] ?? undefined,
      filePath: row.file_path ?? undefined,
      startLine: row.start_line ?? undefined,
      endLine: row.end_line ?? undefined,
      sourceCode: row.source_code ?? undefined,
      docstring: row.docstring ?? undefined,
      signature: row.signature ?? undefined,
      qualifiedName: row.qualified_name ?? undefined,
      namespace: row.namespace ?? undefined,
      communityId: row.community_id ?? undefined,
      metadata: row.metadata ? JSON.parse(row.metadata) : {},
    };
  }

  private rowToRelation(row: RelationRow): Relation {
    return {
      id: row.id,
      sourceId: row.source_id,
      targetId: row.target_id,
      type: row.type as RelationType,
      weight: row.weight ?? 1.0,
      metadata: row.metadata ? JSON.parse(row.metadata) : {},
    };
  }

  /**
   * Check if storage is initialized
   */
  isInitialized(): boolean {
    return this.initialized;
  }

  /**
   * Get database path
   */
  getDatabasePath(): string {
    return this.dbPath;
  }
}

// Type definitions for database rows
interface EntityRow {
  id: string;
  name: string;
  type: string;
  language: string | null;
  file_path: string | null;
  start_line: number | null;
  end_line: number | null;
  source_code: string | null;
  docstring: string | null;
  signature: string | null;
  qualified_name: string | null;
  namespace: string | null;
  community_id: string | null;
  metadata: string | null;
  created_at: string;
  updated_at: string;
}

interface RelationRow {
  id: string;
  source_id: string;
  target_id: string;
  type: string;
  weight: number | null;
  metadata: string | null;
  created_at: string;
}
