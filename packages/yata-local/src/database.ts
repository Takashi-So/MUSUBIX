/**
 * YATA Local - SQLite Database Layer
 *
 * @packageDocumentation
 * @module @nahisaho/yata-local/database
 *
 * @see REQ-YL-STORE-001
 * @see REQ-YL-STORE-002
 * @see REQ-WSL-003
 * @see REQ-NFR-001
 */

import type Database from 'better-sqlite3';
import type {
  DatabaseConfig,
  Entity,
  EntityType,
  Relationship,
  RelationType,
  GraphStats,
  LearnedPattern,
  PatternCategory,
  PatternQueryOptions,
  LearningCycle,
  LearningCycleInput,
  LearningStats,
  LocalKGPR,
  LocalKGPRInput,
  LocalKGPRReview,
  LocalKGPRReviewInput,
  KGPRStatusLocal,
} from './types.js';
import { DEFAULT_DB_CONFIG } from './types.js';

/**
 * SQL schema for knowledge graph
 * @see REQ-YL-STORE-002
 */
const SCHEMA = `
-- Entities table
CREATE TABLE IF NOT EXISTS entities (
  id TEXT PRIMARY KEY,
  type TEXT NOT NULL,
  name TEXT NOT NULL,
  namespace TEXT NOT NULL DEFAULT '',
  file_path TEXT,
  line INTEGER,
  description TEXT,
  metadata TEXT NOT NULL DEFAULT '{}',
  created_at TEXT NOT NULL,
  updated_at TEXT NOT NULL
);

-- Relationships table
CREATE TABLE IF NOT EXISTS relationships (
  id TEXT PRIMARY KEY,
  source_id TEXT NOT NULL,
  target_id TEXT NOT NULL,
  type TEXT NOT NULL,
  weight REAL NOT NULL DEFAULT 1.0,
  metadata TEXT NOT NULL DEFAULT '{}',
  created_at TEXT NOT NULL,
  FOREIGN KEY (source_id) REFERENCES entities(id) ON DELETE CASCADE,
  FOREIGN KEY (target_id) REFERENCES entities(id) ON DELETE CASCADE
);

-- Indexes for fast queries
CREATE INDEX IF NOT EXISTS idx_entities_type ON entities(type);
CREATE INDEX IF NOT EXISTS idx_entities_name ON entities(name);
CREATE INDEX IF NOT EXISTS idx_entities_namespace ON entities(namespace);
CREATE INDEX IF NOT EXISTS idx_entities_file_path ON entities(file_path);
CREATE INDEX IF NOT EXISTS idx_entities_updated ON entities(updated_at);

CREATE INDEX IF NOT EXISTS idx_relationships_source ON relationships(source_id);
CREATE INDEX IF NOT EXISTS idx_relationships_target ON relationships(target_id);
CREATE INDEX IF NOT EXISTS idx_relationships_type ON relationships(type);

-- Full-text search virtual table
CREATE VIRTUAL TABLE IF NOT EXISTS entities_fts USING fts5(
  id,
  name,
  namespace,
  description,
  content='entities',
  content_rowid='rowid'
);

-- Triggers to keep FTS in sync
CREATE TRIGGER IF NOT EXISTS entities_ai AFTER INSERT ON entities BEGIN
  INSERT INTO entities_fts(id, name, namespace, description)
  VALUES (new.id, new.name, new.namespace, new.description);
END;

CREATE TRIGGER IF NOT EXISTS entities_ad AFTER DELETE ON entities BEGIN
  INSERT INTO entities_fts(entities_fts, id, name, namespace, description)
  VALUES ('delete', old.id, old.name, old.namespace, old.description);
END;

CREATE TRIGGER IF NOT EXISTS entities_au AFTER UPDATE ON entities BEGIN
  INSERT INTO entities_fts(entities_fts, id, name, namespace, description)
  VALUES ('delete', old.id, old.name, old.namespace, old.description);
  INSERT INTO entities_fts(id, name, namespace, description)
  VALUES (new.id, new.name, new.namespace, new.description);
END;

-- Change tracking table
CREATE TABLE IF NOT EXISTS change_log (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  entity_id TEXT,
  relationship_id TEXT,
  operation TEXT NOT NULL,
  timestamp TEXT NOT NULL,
  data TEXT
);

CREATE INDEX IF NOT EXISTS idx_change_log_timestamp ON change_log(timestamp);

-- Patterns table for Wake-Sleep learning
-- @see REQ-WSL-003
-- @see TSK-NFR-003
CREATE TABLE IF NOT EXISTS patterns (
  id TEXT PRIMARY KEY,
  name TEXT NOT NULL,
  category TEXT NOT NULL DEFAULT 'code',
  content TEXT NOT NULL,
  ast TEXT,
  confidence REAL NOT NULL DEFAULT 0.5,
  occurrences INTEGER NOT NULL DEFAULT 1,
  last_used_at TEXT,
  usage_count INTEGER NOT NULL DEFAULT 0,
  source TEXT,
  metadata TEXT NOT NULL DEFAULT '{}',
  created_at TEXT NOT NULL,
  updated_at TEXT NOT NULL
);

-- Pattern indexes for performance
-- @see REQ-NFR-001
CREATE INDEX IF NOT EXISTS idx_patterns_category ON patterns(category);
CREATE INDEX IF NOT EXISTS idx_patterns_confidence ON patterns(confidence);
CREATE INDEX IF NOT EXISTS idx_patterns_last_used ON patterns(last_used_at);
CREATE INDEX IF NOT EXISTS idx_patterns_name ON patterns(name);

-- Learning cycles table for tracking Wake-Sleep cycles
-- @see REQ-WSL-005
-- @see TSK-NFR-004
CREATE TABLE IF NOT EXISTS learning_cycles (
  id TEXT PRIMARY KEY,
  wake_extracted INTEGER NOT NULL DEFAULT 0,
  wake_observed_files INTEGER NOT NULL DEFAULT 0,
  sleep_clustered INTEGER NOT NULL DEFAULT 0,
  sleep_decayed INTEGER NOT NULL DEFAULT 0,
  duration_ms INTEGER NOT NULL DEFAULT 0,
  metadata TEXT NOT NULL DEFAULT '{}',
  completed_at TEXT NOT NULL
);

CREATE INDEX IF NOT EXISTS idx_learning_cycles_completed ON learning_cycles(completed_at);

-- KGPR tracking table
-- @see REQ-KGPR-001
-- @see TSK-KGPR-004
CREATE TABLE IF NOT EXISTS kgprs (
  id TEXT PRIMARY KEY,
  title TEXT NOT NULL,
  description TEXT,
  status TEXT NOT NULL DEFAULT 'draft',
  author TEXT NOT NULL DEFAULT 'local',
  namespace TEXT NOT NULL DEFAULT '*',
  diff_json TEXT NOT NULL DEFAULT '{}',
  privacy_level TEXT NOT NULL DEFAULT 'strict',
  entity_types TEXT NOT NULL DEFAULT '[]',
  created_at TEXT NOT NULL,
  updated_at TEXT NOT NULL,
  submitted_at TEXT,
  reviewed_at TEXT,
  merged_at TEXT,
  closed_at TEXT
);

CREATE INDEX IF NOT EXISTS idx_kgprs_status ON kgprs(status);
CREATE INDEX IF NOT EXISTS idx_kgprs_author ON kgprs(author);
CREATE INDEX IF NOT EXISTS idx_kgprs_namespace ON kgprs(namespace);

-- KGPR reviews table
-- @see REQ-KGPR-003
CREATE TABLE IF NOT EXISTS kgpr_reviews (
  id TEXT PRIMARY KEY,
  kgpr_id TEXT NOT NULL,
  reviewer TEXT NOT NULL,
  action TEXT NOT NULL,
  comment TEXT,
  created_at TEXT NOT NULL,
  FOREIGN KEY (kgpr_id) REFERENCES kgprs(id) ON DELETE CASCADE
);

CREATE INDEX IF NOT EXISTS idx_kgpr_reviews_kgpr ON kgpr_reviews(kgpr_id);
`;

/**
 * Database layer for YATA Local
 */
export class YataDatabase {
  private db: Database.Database | null = null;
  private config: DatabaseConfig;

  constructor(config: Partial<DatabaseConfig> = {}) {
    this.config = { ...DEFAULT_DB_CONFIG, ...config };
  }

  /**
   * Open database connection
   * @see REQ-YL-STORE-001
   */
  async open(): Promise<void> {
    // Dynamic import for better-sqlite3
    const BetterSqlite3 = (await import('better-sqlite3')).default;
    
    this.db = new BetterSqlite3(this.config.path);

    // Configure database
    if (this.config.walMode) {
      this.db.pragma('journal_mode = WAL');
    }
    if (this.config.mmapSize > 0) {
      this.db.pragma(`mmap_size = ${this.config.mmapSize}`);
    }
    if (this.config.cacheSize > 0) {
      this.db.pragma(`cache_size = -${this.config.cacheSize}`);
    }
    if (this.config.foreignKeys) {
      this.db.pragma('foreign_keys = ON');
    }

    // Create schema
    this.db.exec(SCHEMA);
  }

  /**
   * Close database connection
   */
  async close(): Promise<void> {
    if (this.db) {
      this.db.close();
      this.db = null;
    }
  }

  /**
   * Check if database is open
   */
  isOpen(): boolean {
    return this.db !== null;
  }

  /**
   * Get database instance (throws if not open)
   * Made public for advanced query use cases
   */
  getDb(): Database.Database {
    if (!this.db) {
      throw new Error('Database is not open. Call open() first.');
    }
    return this.db;
  }

  // Entity operations

  /**
   * Insert entity
   * @see REQ-YL-STORE-003
   */
  insertEntity(entity: Entity): void {
    const db = this.getDb();
    const stmt = db.prepare(`
      INSERT INTO entities (id, type, name, namespace, file_path, line, description, metadata, created_at, updated_at)
      VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    `);
    stmt.run(
      entity.id,
      entity.type,
      entity.name,
      entity.namespace,
      entity.filePath ?? null,
      entity.line ?? null,
      entity.description ?? null,
      JSON.stringify(entity.metadata),
      entity.createdAt.toISOString(),
      entity.updatedAt.toISOString()
    );

    // Log change
    this.logChange(entity.id, null, 'insert', entity);
  }

  /**
   * Insert multiple entities in transaction
   * @see REQ-YL-STORE-005
   */
  insertEntities(entities: Entity[]): void {
    const db = this.getDb();
    const stmt = db.prepare(`
      INSERT INTO entities (id, type, name, namespace, file_path, line, description, metadata, created_at, updated_at)
      VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    `);

    const insertMany = db.transaction((items: Entity[]) => {
      for (const entity of items) {
        stmt.run(
          entity.id,
          entity.type,
          entity.name,
          entity.namespace,
          entity.filePath ?? null,
          entity.line ?? null,
          entity.description ?? null,
          JSON.stringify(entity.metadata),
          entity.createdAt.toISOString(),
          entity.updatedAt.toISOString()
        );
      }
    });

    insertMany(entities);
  }

  /**
   * Get entity by ID
   */
  getEntity(id: string): Entity | null {
    const db = this.getDb();
    const stmt = db.prepare('SELECT * FROM entities WHERE id = ?');
    const row = stmt.get(id) as EntityRow | undefined;
    return row ? this.rowToEntity(row) : null;
  }

  /**
   * Update entity
   * @see REQ-YL-UPDATE-002
   */
  updateEntity(id: string, updates: Partial<Entity>): void {
    const db = this.getDb();
    const existing = this.getEntity(id);
    if (!existing) {
      throw new Error(`Entity not found: ${id}`);
    }

    const updated = { ...existing, ...updates, updatedAt: new Date() };
    const stmt = db.prepare(`
      UPDATE entities SET
        type = ?, name = ?, namespace = ?, file_path = ?, line = ?,
        description = ?, metadata = ?, updated_at = ?
      WHERE id = ?
    `);
    stmt.run(
      updated.type,
      updated.name,
      updated.namespace,
      updated.filePath ?? null,
      updated.line ?? null,
      updated.description ?? null,
      JSON.stringify(updated.metadata),
      updated.updatedAt.toISOString(),
      id
    );

    this.logChange(id, null, 'update', updated);
  }

  /**
   * Delete entity
   * @see REQ-YL-UPDATE-003
   */
  deleteEntity(id: string): void {
    const db = this.getDb();
    const stmt = db.prepare('DELETE FROM entities WHERE id = ?');
    stmt.run(id);
    this.logChange(id, null, 'delete', null);
  }

  /**
   * Delete entities by file path
   */
  deleteEntitiesByFile(filePath: string): number {
    const db = this.getDb();
    const stmt = db.prepare('DELETE FROM entities WHERE file_path = ?');
    const result = stmt.run(filePath);
    return result.changes;
  }

  // Relationship operations

  /**
   * Insert relationship
   * @see REQ-YL-STORE-004
   */
  insertRelationship(rel: Relationship): void {
    const db = this.getDb();
    const stmt = db.prepare(`
      INSERT INTO relationships (id, source_id, target_id, type, weight, metadata, created_at)
      VALUES (?, ?, ?, ?, ?, ?, ?)
    `);
    stmt.run(
      rel.id,
      rel.sourceId,
      rel.targetId,
      rel.type,
      rel.weight,
      JSON.stringify(rel.metadata),
      rel.createdAt.toISOString()
    );

    this.logChange(null, rel.id, 'insert', rel);
  }

  /**
   * Get relationships for entity
   */
  getRelationships(entityId: string, direction: 'in' | 'out' | 'both' = 'both'): Relationship[] {
    const db = this.getDb();
    let sql: string;
    
    if (direction === 'out') {
      sql = 'SELECT * FROM relationships WHERE source_id = ?';
    } else if (direction === 'in') {
      sql = 'SELECT * FROM relationships WHERE target_id = ?';
    } else {
      sql = 'SELECT * FROM relationships WHERE source_id = ? OR target_id = ?';
    }

    const stmt = db.prepare(sql);
    const rows = direction === 'both'
      ? stmt.all(entityId, entityId) as RelationshipRow[]
      : stmt.all(entityId) as RelationshipRow[];

    return rows.map(row => this.rowToRelationship(row));
  }

  /**
   * Delete relationship
   */
  deleteRelationship(id: string): void {
    const db = this.getDb();
    const stmt = db.prepare('DELETE FROM relationships WHERE id = ?');
    stmt.run(id);
    this.logChange(null, id, 'delete', null);
  }

  // Query operations

  /**
   * Query entities with filters
   * @see REQ-YL-QUERY-001
   */
  queryEntities(
    filters: {
      type?: EntityType | EntityType[];
      name?: string;
      namePattern?: string;
      namespace?: string;
    },
    limit = 100,
    offset = 0
  ): { entities: Entity[]; totalCount: number } {
    const db = this.getDb();
    const conditions: string[] = [];
    const params: unknown[] = [];

    if (filters.type) {
      if (Array.isArray(filters.type)) {
        conditions.push(`type IN (${filters.type.map(() => '?').join(', ')})`);
        params.push(...filters.type);
      } else {
        conditions.push('type = ?');
        params.push(filters.type);
      }
    }

    if (filters.name) {
      conditions.push('name = ?');
      params.push(filters.name);
    }

    if (filters.namePattern) {
      conditions.push('name LIKE ?');
      params.push(filters.namePattern.replace(/\*/g, '%'));
    }

    if (filters.namespace) {
      conditions.push('namespace = ?');
      params.push(filters.namespace);
    }

    const whereClause = conditions.length > 0 ? `WHERE ${conditions.join(' AND ')}` : '';

    // Get total count
    const countStmt = db.prepare(`SELECT COUNT(*) as count FROM entities ${whereClause}`);
    const countResult = countStmt.get(...params) as { count: number };

    // Get paginated results
    const stmt = db.prepare(`SELECT * FROM entities ${whereClause} LIMIT ? OFFSET ?`);
    const rows = stmt.all(...params, limit, offset) as EntityRow[];

    return {
      entities: rows.map(row => this.rowToEntity(row)),
      totalCount: countResult.count,
    };
  }

  /**
   * Full-text search
   * @see REQ-YL-QUERY-005
   */
  searchEntities(text: string, limit = 100): Entity[] {
    const db = this.getDb();
    const stmt = db.prepare(`
      SELECT e.* FROM entities e
      JOIN entities_fts fts ON e.id = fts.id
      WHERE entities_fts MATCH ?
      LIMIT ?
    `);
    const rows = stmt.all(text, limit) as EntityRow[];
    return rows.map(row => this.rowToEntity(row));
  }

  /**
   * Get changes since timestamp
   * @see REQ-YL-UPDATE-005
   */
  getChangesSince(since: Date): {
    entities: { added: Entity[]; updated: Entity[]; deleted: string[] };
    relationships: { added: Relationship[]; deleted: string[] };
  } {
    const db = this.getDb();
    const stmt = db.prepare(`
      SELECT * FROM change_log WHERE timestamp > ? ORDER BY id
    `);
    const rows = stmt.all(since.toISOString()) as ChangeLogRow[];

    const result = {
      entities: { added: [] as Entity[], updated: [] as Entity[], deleted: [] as string[] },
      relationships: { added: [] as Relationship[], deleted: [] as string[] },
    };

    for (const row of rows) {
      if (row.entity_id) {
        if (row.operation === 'insert') {
          const entity = this.getEntity(row.entity_id);
          if (entity) result.entities.added.push(entity);
        } else if (row.operation === 'update') {
          const entity = this.getEntity(row.entity_id);
          if (entity) result.entities.updated.push(entity);
        } else if (row.operation === 'delete') {
          result.entities.deleted.push(row.entity_id);
        }
      } else if (row.relationship_id) {
        if (row.operation === 'insert' && row.data) {
          result.relationships.added.push(JSON.parse(row.data) as Relationship);
        } else if (row.operation === 'delete') {
          result.relationships.deleted.push(row.relationship_id);
        }
      }
    }

    return result;
  }

  /**
   * Get graph statistics
   */
  getStats(): GraphStats {
    const db = this.getDb();
    
    // Entity count
    const entityCount = (db.prepare('SELECT COUNT(*) as count FROM entities').get() as { count: number }).count;
    
    // Entities by type
    const typeRows = db.prepare('SELECT type, COUNT(*) as count FROM entities GROUP BY type').all() as { type: string; count: number }[];
    const entitiesByType: Record<string, number> = {};
    for (const row of typeRows) {
      entitiesByType[row.type] = row.count;
    }

    // Relationship count
    const relationshipCount = (db.prepare('SELECT COUNT(*) as count FROM relationships').get() as { count: number }).count;

    // Relationships by type
    const relTypeRows = db.prepare('SELECT type, COUNT(*) as count FROM relationships GROUP BY type').all() as { type: string; count: number }[];
    const relationshipsByType: Record<string, number> = {};
    for (const row of relTypeRows) {
      relationshipsByType[row.type] = row.count;
    }

    // Database size (approximate)
    const pageCount = (db.prepare('PRAGMA page_count').get() as { page_count: number }).page_count;
    const pageSize = (db.prepare('PRAGMA page_size').get() as { page_size: number }).page_size;
    const databaseSize = pageCount * pageSize;

    // Last modified
    const lastModifiedRow = db.prepare('SELECT MAX(updated_at) as last FROM entities').get() as { last: string | null };
    const lastModified = lastModifiedRow.last ? new Date(lastModifiedRow.last) : new Date();

    return {
      entityCount,
      entitiesByType: entitiesByType as Record<EntityType, number>,
      relationshipCount,
      relationshipsByType: relationshipsByType as Record<RelationType, number>,
      databaseSize,
      lastModified,
    };
  }

  // ============================================================
  // Pattern Operations (TSK-NFR-003, TSK-WSL-003)
  // @see REQ-WSL-003
  // ============================================================

  /**
   * Insert a learned pattern
   * @see REQ-WSL-001
   */
  insertPattern(pattern: LearnedPattern): void {
    const db = this.getDb();
    const stmt = db.prepare(`
      INSERT INTO patterns (id, name, category, content, ast, confidence, occurrences, last_used_at, usage_count, source, metadata, created_at, updated_at)
      VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    `);
    stmt.run(
      pattern.id,
      pattern.name,
      pattern.category,
      pattern.content,
      pattern.ast ? JSON.stringify(pattern.ast) : null,
      pattern.confidence,
      pattern.occurrences,
      pattern.lastUsedAt?.toISOString() ?? null,
      pattern.usageCount,
      pattern.source ?? null,
      JSON.stringify(pattern.metadata),
      pattern.createdAt.toISOString(),
      pattern.updatedAt.toISOString()
    );
  }

  /**
   * Get a pattern by ID
   */
  getPattern(id: string): LearnedPattern | null {
    const db = this.getDb();
    const stmt = db.prepare('SELECT * FROM patterns WHERE id = ?');
    const row = stmt.get(id) as PatternRow | undefined;
    return row ? this.rowToPattern(row) : null;
  }

  /**
   * Update a pattern
   */
  updatePattern(pattern: LearnedPattern): void {
    const db = this.getDb();
    const stmt = db.prepare(`
      UPDATE patterns SET
        name = ?, category = ?, content = ?, ast = ?, confidence = ?,
        occurrences = ?, last_used_at = ?, usage_count = ?, source = ?,
        metadata = ?, updated_at = ?
      WHERE id = ?
    `);
    stmt.run(
      pattern.name,
      pattern.category,
      pattern.content,
      pattern.ast ? JSON.stringify(pattern.ast) : null,
      pattern.confidence,
      pattern.occurrences,
      pattern.lastUsedAt?.toISOString() ?? null,
      pattern.usageCount,
      pattern.source ?? null,
      JSON.stringify(pattern.metadata),
      pattern.updatedAt.toISOString(),
      pattern.id
    );
  }

  /**
   * Upsert a pattern (insert or update)
   * @see REQ-WSL-002
   */
  upsertPattern(pattern: LearnedPattern): void {
    const existing = this.getPattern(pattern.id);
    if (existing) {
      this.updatePattern(pattern);
    } else {
      this.insertPattern(pattern);
    }
  }

  /**
   * Delete a pattern
   */
  deletePattern(id: string): boolean {
    const db = this.getDb();
    const stmt = db.prepare('DELETE FROM patterns WHERE id = ?');
    const result = stmt.run(id);
    return result.changes > 0;
  }

  /**
   * Query patterns with options
   * @see REQ-WSL-003
   */
  queryPatterns(options: PatternQueryOptions = {}): LearnedPattern[] {
    const db = this.getDb();
    const conditions: string[] = [];
    const params: unknown[] = [];

    if (options.category) {
      conditions.push('category = ?');
      params.push(options.category);
    }

    if (options.minConfidence !== undefined) {
      conditions.push('confidence >= ?');
      params.push(options.minConfidence);
    }

    const whereClause = conditions.length > 0 ? `WHERE ${conditions.join(' AND ')}` : '';
    const sortBy = options.sortBy ?? 'created_at';
    const sortOrder = options.sortOrder ?? 'desc';
    const limit = options.limit ?? 100;
    const offset = options.offset ?? 0;

    const sql = `
      SELECT * FROM patterns
      ${whereClause}
      ORDER BY ${sortBy} ${sortOrder}
      LIMIT ? OFFSET ?
    `;
    params.push(limit, offset);

    const stmt = db.prepare(sql);
    const rows = stmt.all(...params) as PatternRow[];
    return rows.map(row => this.rowToPattern(row));
  }

  /**
   * Get patterns that haven't been used recently
   * @see REQ-WSL-003
   */
  getUnusedPatterns(monthsThreshold: number = 6): LearnedPattern[] {
    const db = this.getDb();
    const thresholdDate = new Date();
    thresholdDate.setMonth(thresholdDate.getMonth() - monthsThreshold);

    const stmt = db.prepare(`
      SELECT * FROM patterns
      WHERE last_used_at IS NULL OR last_used_at < ?
      ORDER BY last_used_at ASC
    `);
    const rows = stmt.all(thresholdDate.toISOString()) as PatternRow[];
    return rows.map(row => this.rowToPattern(row));
  }

  /**
   * Get low confidence patterns
   * @see REQ-WSL-003
   */
  getLowConfidencePatterns(threshold: number = 0.3): LearnedPattern[] {
    const db = this.getDb();
    const stmt = db.prepare(`
      SELECT * FROM patterns
      WHERE confidence < ?
      ORDER BY confidence ASC
    `);
    const rows = stmt.all(threshold) as PatternRow[];
    return rows.map(row => this.rowToPattern(row));
  }

  /**
   * Mark pattern as used (update lastUsedAt)
   * @see REQ-WSL-003
   */
  markPatternUsed(id: string): void {
    const db = this.getDb();
    const stmt = db.prepare(`
      UPDATE patterns SET
        last_used_at = ?,
        usage_count = usage_count + 1,
        updated_at = ?
      WHERE id = ?
    `);
    const now = new Date().toISOString();
    stmt.run(now, now, id);
  }

  /**
   * Decay pattern confidence
   * @see REQ-WSL-003
   */
  decayPatternConfidence(id: string, factor: number): void {
    const db = this.getDb();
    const stmt = db.prepare(`
      UPDATE patterns SET
        confidence = confidence * ?,
        updated_at = ?
      WHERE id = ?
    `);
    stmt.run(factor, new Date().toISOString(), id);
  }

  /**
   * Get pattern count
   */
  getPatternCount(): number {
    const db = this.getDb();
    const result = db.prepare('SELECT COUNT(*) as count FROM patterns').get() as { count: number };
    return result.count;
  }

  // ============================================================
  // Learning Cycle Operations (TSK-NFR-004)
  // @see REQ-WSL-005
  // ============================================================

  /**
   * Log a learning cycle
   * @see REQ-WSL-005
   */
  logLearningCycle(cycle: LearningCycleInput): LearningCycle {
    const db = this.getDb();
    const id = `LC-${Date.now().toString(36)}-${Math.random().toString(36).substring(2, 6)}`;
    const now = new Date();

    const stmt = db.prepare(`
      INSERT INTO learning_cycles (id, wake_extracted, wake_observed_files, sleep_clustered, sleep_decayed, duration_ms, metadata, completed_at)
      VALUES (?, ?, ?, ?, ?, ?, ?, ?)
    `);
    stmt.run(
      id,
      cycle.wakeExtracted,
      cycle.wakeObservedFiles,
      cycle.sleepClustered,
      cycle.sleepDecayed,
      cycle.durationMs,
      JSON.stringify(cycle.metadata ?? {}),
      now.toISOString()
    );

    return {
      id,
      wakeExtracted: cycle.wakeExtracted,
      wakeObservedFiles: cycle.wakeObservedFiles,
      sleepClustered: cycle.sleepClustered,
      sleepDecayed: cycle.sleepDecayed,
      durationMs: cycle.durationMs,
      metadata: cycle.metadata ?? {},
      completedAt: now,
    };
  }

  /**
   * Get recent learning cycles
   * @see REQ-WSL-005
   */
  getRecentLearningCycles(limit: number = 10): LearningCycle[] {
    const db = this.getDb();
    const stmt = db.prepare(`
      SELECT * FROM learning_cycles
      ORDER BY completed_at DESC
      LIMIT ?
    `);
    const rows = stmt.all(limit) as LearningCycleRow[];
    return rows.map(row => this.rowToLearningCycle(row));
  }

  /**
   * Get learning statistics
   * @see REQ-WSL-005
   */
  getLearningStats(): LearningStats {
    const db = this.getDb();

    // Pattern count
    const totalPatterns = this.getPatternCount();

    // Patterns by category
    const categoryRows = db.prepare('SELECT category, COUNT(*) as count FROM patterns GROUP BY category').all() as { category: string; count: number }[];
    const patternsByCategory: Record<string, number> = {};
    for (const row of categoryRows) {
      patternsByCategory[row.category] = row.count;
    }

    // Average confidence
    const avgResult = db.prepare('SELECT AVG(confidence) as avg FROM patterns').get() as { avg: number | null };
    const averageConfidence = avgResult.avg ?? 0;

    // Total cycles
    const totalCycles = (db.prepare('SELECT COUNT(*) as count FROM learning_cycles').get() as { count: number }).count;

    // Last cycle
    const lastCycleRow = db.prepare('SELECT MAX(completed_at) as last FROM learning_cycles').get() as { last: string | null };
    const lastCycleAt = lastCycleRow.last ? new Date(lastCycleRow.last) : undefined;

    return {
      totalPatterns,
      patternsByCategory: patternsByCategory as Record<PatternCategory, number>,
      averageConfidence,
      totalCycles,
      lastCycleAt,
    };
  }

  // ============================================================
  // KGPR Local Operations (TSK-KGPR-004)
  // @see REQ-KGPR-001
  // ============================================================

  /**
   * Insert a local KGPR record
   */
  insertKGPR(kgpr: LocalKGPRInput): void {
    const db = this.getDb();
    const stmt = db.prepare(`
      INSERT INTO kgprs (id, title, description, status, author, namespace, diff_json, privacy_level, entity_types, created_at, updated_at, submitted_at)
      VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    `);
    stmt.run(
      kgpr.id,
      kgpr.title,
      kgpr.description ?? null,
      kgpr.status,
      kgpr.author,
      kgpr.namespace ?? '*',
      kgpr.diffJson,
      kgpr.privacyLevel,
      kgpr.entityTypesJson ?? '[]',
      kgpr.createdAt,
      kgpr.updatedAt ?? kgpr.createdAt,
      kgpr.submittedAt ?? null
    );
  }

  /**
   * Get a KGPR by ID
   */
  getKGPR(id: string): LocalKGPR | null {
    const db = this.getDb();
    const stmt = db.prepare('SELECT * FROM kgprs WHERE id = ?');
    const row = stmt.get(id) as KGPRRow | undefined;
    return row ? this.rowToKGPR(row) : null;
  }

  /**
   * Update KGPR status
   */
  updateKGPRStatus(id: string, status: KGPRStatusLocal, timestamp?: Date): void {
    const db = this.getDb();
    const now = timestamp ?? new Date();
    
    let timestampField = '';
    switch (status) {
      case 'open': timestampField = 'submitted_at'; break;
      case 'approved':
      case 'changes_requested': timestampField = 'reviewed_at'; break;
      case 'merged': timestampField = 'merged_at'; break;
      case 'closed': timestampField = 'closed_at'; break;
    }

    if (timestampField) {
      const stmt = db.prepare(`UPDATE kgprs SET status = ?, ${timestampField} = ? WHERE id = ?`);
      stmt.run(status, now.toISOString(), id);
    } else {
      const stmt = db.prepare('UPDATE kgprs SET status = ? WHERE id = ?');
      stmt.run(status, id);
    }
  }

  /**
   * List KGPRs with optional filters
   */
  listKGPRs(options?: { status?: KGPRStatusLocal; namespace?: string; limit?: number; offset?: number }): LocalKGPR[] {
    const db = this.getDb();
    let sql = 'SELECT * FROM kgprs WHERE 1=1';
    const params: unknown[] = [];
    
    if (options?.status) {
      sql += ' AND status = ?';
      params.push(options.status);
    }
    if (options?.namespace) {
      sql += ' AND namespace LIKE ?';
      params.push(`${options.namespace}%`);
    }
    sql += ' ORDER BY created_at DESC';
    if (options?.limit) {
      sql += ' LIMIT ?';
      params.push(options.limit);
      if (options?.offset) {
        sql += ' OFFSET ?';
        params.push(options.offset);
      }
    }
    
    const stmt = db.prepare(sql);
    const rows = stmt.all(...params) as KGPRRow[];
    return rows.map(row => this.rowToKGPR(row));
  }

  /**
   * Insert a KGPR review
   */
  insertKGPRReview(review: LocalKGPRReviewInput): void {
    const db = this.getDb();
    const stmt = db.prepare(`
      INSERT INTO kgpr_reviews (id, kgpr_id, reviewer, action, comment, created_at)
      VALUES (?, ?, ?, ?, ?, ?)
    `);
    stmt.run(
      review.id,
      review.kgprId,
      review.reviewer,
      review.action,
      review.comment ?? null,
      review.createdAt
    );
  }

  /**
   * Get reviews for a KGPR
   */
  getKGPRReviews(kgprId: string): LocalKGPRReview[] {
    const db = this.getDb();
    const stmt = db.prepare('SELECT * FROM kgpr_reviews WHERE kgpr_id = ? ORDER BY created_at DESC');
    const rows = stmt.all(kgprId) as KGPRReviewRow[];
    return rows.map(row => ({
      id: row.id,
      kgprId: row.kgpr_id,
      reviewer: row.reviewer,
      action: row.action as 'approve' | 'changes_requested' | 'commented',
      comment: row.comment ?? undefined,
      createdAt: new Date(row.created_at),
    }));
  }

  // ============================================================
  // Transaction Support (TSK-NFR-002)
  // @see REQ-NFR-002
  // ============================================================

  /**
   * Execute operations within a transaction
   * @see REQ-NFR-002
   */
  withTransaction<T>(fn: () => T): T {
    const db = this.getDb();
    db.exec('BEGIN TRANSACTION');
    try {
      const result = fn();
      db.exec('COMMIT');
      return result;
    } catch (error) {
      db.exec('ROLLBACK');
      throw error;
    }
  }

  /**
   * Execute async operations within a transaction
   * @see REQ-NFR-002
   */
  async withTransactionAsync<T>(fn: () => Promise<T>): Promise<T> {
    const db = this.getDb();
    db.exec('BEGIN TRANSACTION');
    try {
      const result = await fn();
      db.exec('COMMIT');
      return result;
    } catch (error) {
      db.exec('ROLLBACK');
      throw error;
    }
  }

  // Helper methods

  private rowToEntity(row: EntityRow): Entity {
    return {
      id: row.id,
      type: row.type as EntityType,
      name: row.name,
      namespace: row.namespace,
      filePath: row.file_path ?? undefined,
      line: row.line ?? undefined,
      description: row.description ?? undefined,
      metadata: JSON.parse(row.metadata),
      createdAt: new Date(row.created_at),
      updatedAt: new Date(row.updated_at),
    };
  }

  private rowToRelationship(row: RelationshipRow): Relationship {
    return {
      id: row.id,
      sourceId: row.source_id,
      targetId: row.target_id,
      type: row.type as RelationType,
      weight: row.weight,
      metadata: JSON.parse(row.metadata),
      createdAt: new Date(row.created_at),
    };
  }

  private logChange(entityId: string | null, relationshipId: string | null, operation: string, data: unknown): void {
    const db = this.getDb();
    const stmt = db.prepare(`
      INSERT INTO change_log (entity_id, relationship_id, operation, timestamp, data)
      VALUES (?, ?, ?, ?, ?)
    `);
    stmt.run(
      entityId,
      relationshipId,
      operation,
      new Date().toISOString(),
      data ? JSON.stringify(data) : null
    );
  }

  private rowToPattern(row: PatternRow): LearnedPattern {
    return {
      id: row.id,
      name: row.name,
      category: row.category as PatternCategory,
      content: row.content,
      ast: row.ast ? JSON.parse(row.ast) : undefined,
      confidence: row.confidence,
      occurrences: row.occurrences,
      lastUsedAt: row.last_used_at ? new Date(row.last_used_at) : undefined,
      usageCount: row.usage_count,
      source: row.source ?? undefined,
      metadata: JSON.parse(row.metadata),
      createdAt: new Date(row.created_at),
      updatedAt: new Date(row.updated_at),
    };
  }

  private rowToLearningCycle(row: LearningCycleRow): LearningCycle {
    return {
      id: row.id,
      wakeExtracted: row.wake_extracted,
      wakeObservedFiles: row.wake_observed_files,
      sleepClustered: row.sleep_clustered,
      sleepDecayed: row.sleep_decayed,
      durationMs: row.duration_ms,
      metadata: JSON.parse(row.metadata),
      completedAt: new Date(row.completed_at),
    };
  }

  private rowToKGPR(row: KGPRRow): LocalKGPR {
    return {
      id: row.id,
      title: row.title,
      description: row.description ?? undefined,
      status: row.status as KGPRStatusLocal,
      author: row.author,
      namespace: row.namespace,
      diffJson: row.diff_json,
      privacyLevel: row.privacy_level as 'strict' | 'moderate' | 'none',
      entityTypesJson: row.entity_types,
      createdAt: new Date(row.created_at),
      updatedAt: new Date(row.updated_at),
      submittedAt: row.submitted_at ? new Date(row.submitted_at) : undefined,
      reviewedAt: row.reviewed_at ? new Date(row.reviewed_at) : undefined,
      mergedAt: row.merged_at ? new Date(row.merged_at) : undefined,
      closedAt: row.closed_at ? new Date(row.closed_at) : undefined,
    };
  }
}

// Row types for SQLite results
interface EntityRow {
  id: string;
  type: string;
  name: string;
  namespace: string;
  file_path: string | null;
  line: number | null;
  description: string | null;
  metadata: string;
  created_at: string;
  updated_at: string;
}

interface RelationshipRow {
  id: string;
  source_id: string;
  target_id: string;
  type: string;
  weight: number;
  metadata: string;
  created_at: string;
}

interface ChangeLogRow {
  id: number;
  entity_id: string | null;
  relationship_id: string | null;
  operation: string;
  timestamp: string;
  data: string | null;
}

interface PatternRow {
  id: string;
  name: string;
  category: string;
  content: string;
  ast: string | null;
  confidence: number;
  occurrences: number;
  last_used_at: string | null;
  usage_count: number;
  source: string | null;
  metadata: string;
  created_at: string;
  updated_at: string;
}

interface LearningCycleRow {
  id: string;
  wake_extracted: number;
  wake_observed_files: number;
  sleep_clustered: number;
  sleep_decayed: number;
  duration_ms: number;
  metadata: string;
  completed_at: string;
}

interface KGPRRow {
  id: string;
  title: string;
  description: string | null;
  status: string;
  author: string;
  namespace: string;
  diff_json: string;
  privacy_level: string;
  entity_types: string;
  created_at: string;
  updated_at: string;
  submitted_at: string | null;
  reviewed_at: string | null;
  merged_at: string | null;
  closed_at: string | null;
}

interface KGPRReviewRow {
  id: string;
  kgpr_id: string;
  reviewer: string;
  action: string;
  comment: string | null;
  created_at: string;
}
