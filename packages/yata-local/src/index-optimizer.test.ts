/**
 * Index Optimizer Tests
 *
 * @see REQ-YI-IDX-001
 * @see REQ-YI-IDX-002
 * @see REQ-YI-IDX-003
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import BetterSqlite3 from 'better-sqlite3';
import type Database from 'better-sqlite3';
import {
  IndexOptimizer,
  IndexAnalysisResult,
  IndexRecommendation,
  QueryStats,
  QUERY_LOG_SCHEMA,
} from './index-optimizer.js';

// Test schema (minimal for testing)
const TEST_SCHEMA = `
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

CREATE TABLE IF NOT EXISTS patterns (
  id TEXT PRIMARY KEY,
  name TEXT NOT NULL,
  category TEXT NOT NULL DEFAULT 'code',
  content TEXT NOT NULL,
  confidence REAL NOT NULL DEFAULT 0.5,
  occurrences INTEGER NOT NULL DEFAULT 1,
  created_at TEXT NOT NULL,
  updated_at TEXT NOT NULL
);

-- Existing single-column indexes
CREATE INDEX IF NOT EXISTS idx_entities_type ON entities(type);
CREATE INDEX IF NOT EXISTS idx_entities_name ON entities(name);
CREATE INDEX IF NOT EXISTS idx_entities_namespace ON entities(namespace);
CREATE INDEX IF NOT EXISTS idx_relationships_source ON relationships(source_id);
CREATE INDEX IF NOT EXISTS idx_relationships_target ON relationships(target_id);
CREATE INDEX IF NOT EXISTS idx_relationships_type ON relationships(type);
`;

describe('IndexOptimizer', () => {
  let db: Database.Database;
  let optimizer: IndexOptimizer;

  beforeEach(() => {
    // Create in-memory database for testing
    db = new BetterSqlite3(':memory:');
    db.exec(TEST_SCHEMA);
    optimizer = new IndexOptimizer(db);
  });

  afterEach(() => {
    db.close();
  });

  describe('analyzeIndexes (REQ-YI-IDX-001)', () => {
    it('should return analysis result with existing indexes', async () => {
      const result = await optimizer.analyzeIndexes();

      expect(result).toBeDefined();
      expect(result.indexes).toBeInstanceOf(Array);
      expect(result.recommendations).toBeInstanceOf(Array);
      expect(result.analyzedAt).toBeDefined();
      expect(result.analysisTimeMs).toBeGreaterThanOrEqual(0);
    });

    it('should detect existing indexes', async () => {
      const result = await optimizer.analyzeIndexes();

      // Should find the indexes we created
      const indexNames = result.indexes.map(i => i.name);
      expect(indexNames).toContain('idx_entities_type');
      expect(indexNames).toContain('idx_entities_name');
      expect(indexNames).toContain('idx_relationships_source');
    });

    it('should recommend composite indexes', async () => {
      const result = await optimizer.analyzeIndexes();

      // Should recommend composite indexes for common patterns
      const createRecommendations = result.recommendations.filter(
        r => r.type === 'create'
      );
      expect(createRecommendations.length).toBeGreaterThan(0);

      // Check for namespace+type composite index recommendation
      const namespaceTypeRec = createRecommendations.find(
        r =>
          r.table === 'entities' &&
          r.columns.includes('namespace') &&
          r.columns.includes('type')
      );
      expect(namespaceTypeRec).toBeDefined();
    });

    it('should complete analysis within 5 seconds for empty database', async () => {
      const result = await optimizer.analyzeIndexes();

      // Empty database should be very fast
      expect(result.analysisTimeMs).toBeLessThan(5000);
    });

    it('should include entity and relationship counts', async () => {
      // Insert test data
      const now = new Date().toISOString();
      db.prepare(
        `INSERT INTO entities (id, type, name, namespace, created_at, updated_at) VALUES (?, ?, ?, ?, ?, ?)`
      ).run('E1', 'class', 'TestClass', 'test-ns', now, now);

      const result = await optimizer.analyzeIndexes();

      expect(result.entityCount).toBe(1);
      expect(result.relationshipCount).toBe(0);
    });

    it('should respect maxRecommendations option', async () => {
      const result = await optimizer.analyzeIndexes({ maxRecommendations: 2 });

      expect(result.recommendations.length).toBeLessThanOrEqual(2);
    });

    it('should respect minImprovementThreshold option', async () => {
      const result = await optimizer.analyzeIndexes({ minImprovementThreshold: 50 });

      for (const rec of result.recommendations) {
        expect(rec.estimatedImprovement).toBeGreaterThanOrEqual(50);
      }
    });
  });

  describe('createCompositeIndex (REQ-YI-IDX-002)', () => {
    it('should create composite index on valid table and columns', () => {
      const sql = optimizer.createCompositeIndex('entities', ['namespace', 'type']);

      expect(sql).toContain('CREATE');
      expect(sql).toContain('idx_entities_namespace_type');
      expect(sql).toContain('namespace');
      expect(sql).toContain('type');

      // Verify index was created
      const indexes = db.prepare(`PRAGMA index_list('entities')`).all() as Array<{
        name: string;
      }>;
      const indexNames = indexes.map(i => i.name);
      expect(indexNames).toContain('idx_entities_namespace_type');
    });

    it('should allow custom index name', () => {
      const sql = optimizer.createCompositeIndex('entities', ['type', 'updated_at'], {
        name: 'my_custom_index',
      });

      expect(sql).toContain('my_custom_index');
    });

    it('should create unique index when specified', () => {
      const sql = optimizer.createCompositeIndex('entities', ['id', 'namespace'], {
        unique: true,
      });

      expect(sql).toContain('UNIQUE');
    });

    it('should return SQL without executing when execute=false', () => {
      const sql = optimizer.createCompositeIndex(
        'entities',
        ['namespace', 'file_path'],
        { execute: false }
      );

      expect(sql).toBeDefined();

      // Verify index was NOT created
      const indexes = db.prepare(`PRAGMA index_list('entities')`).all() as Array<{
        name: string;
      }>;
      const indexNames = indexes.map(i => i.name);
      expect(indexNames).not.toContain('idx_entities_namespace_file_path');
    });

    it('should throw error for non-existent table', () => {
      expect(() => {
        optimizer.createCompositeIndex('non_existent_table', ['col1']);
      }).toThrow("Table 'non_existent_table' does not exist");
    });

    it('should throw error for non-existent column', () => {
      expect(() => {
        optimizer.createCompositeIndex('entities', ['non_existent_column']);
      }).toThrow("Column 'non_existent_column' does not exist");
    });
  });

  describe('applyRecommendations', () => {
    it('should apply create recommendations', async () => {
      const result = await optimizer.analyzeIndexes();
      const createRecs = result.recommendations.filter(r => r.type === 'create');

      const applied = optimizer.applyRecommendations(createRecs);

      expect(applied.length).toBeGreaterThan(0);

      // Verify new indexes exist in respective tables
      const allIndexNames: string[] = [];
      for (const table of ['entities', 'relationships', 'patterns']) {
        const indexes = db.prepare(`PRAGMA index_list('${table}')`).all() as Array<{
          name: string;
        }>;
        allIndexNames.push(...indexes.map(i => i.name));
      }

      for (const name of applied) {
        expect(allIndexNames).toContain(name);
      }
    });
  });

  describe('Query Monitoring (REQ-YI-IDX-003)', () => {
    beforeEach(() => {
      optimizer.enableMonitoring();
    });

    it('should enable monitoring and create query_log table', () => {
      expect(optimizer.isMonitoringEnabled()).toBe(true);

      const tables = db
        .prepare(`SELECT name FROM sqlite_master WHERE type='table' AND name='query_log'`)
        .all();
      expect(tables.length).toBe(1);
    });

    it('should log queries when monitoring is enabled', () => {
      optimizer.logQuery('SELECT * FROM entities WHERE type = ?', 15, 100, [
        'idx_entities_type',
      ]);

      const logs = db.prepare('SELECT * FROM query_log').all();
      expect(logs.length).toBe(1);
    });

    it('should aggregate query statistics', () => {
      // Log multiple executions of the same query pattern
      optimizer.logQuery('SELECT * FROM entities WHERE type = ?', 10);
      optimizer.logQuery('SELECT * FROM entities WHERE type = ?', 20);
      optimizer.logQuery('SELECT * FROM entities WHERE type = ?', 15);

      const stats = optimizer.getQueryStats();

      expect(stats.length).toBe(1);
      expect(stats[0].executionCount).toBe(3);
      expect(stats[0].avgTimeMs).toBe(15); // (10+20+15)/3
      expect(stats[0].minTimeMs).toBe(10);
      expect(stats[0].maxTimeMs).toBe(20);
    });

    it('should identify slow queries', () => {
      optimizer.logQuery('SELECT * FROM entities', 50);
      optimizer.logQuery('SELECT * FROM relationships', 150);
      optimizer.logQuery('SELECT * FROM patterns', 200);

      const slowQueries = optimizer.getSlowQueries(100);

      expect(slowQueries.length).toBe(2);
      expect(slowQueries[0].avgTimeMs).toBe(200);
      expect(slowQueries[1].avgTimeMs).toBe(150);
    });

    it('should clear query log', () => {
      optimizer.logQuery('SELECT 1', 1);
      optimizer.logQuery('SELECT 2', 2);

      const deleted = optimizer.clearQueryLog(0);

      expect(deleted).toBe(2);

      const logs = db.prepare('SELECT * FROM query_log').all();
      expect(logs.length).toBe(0);
    });

    it('should disable monitoring', () => {
      optimizer.disableMonitoring();
      expect(optimizer.isMonitoringEnabled()).toBe(false);

      // Logging should be no-op when disabled
      optimizer.logQuery('SELECT * FROM entities', 10);

      const logs = db.prepare('SELECT * FROM query_log').all();
      expect(logs.length).toBe(0);
    });
  });

  describe('getDatabaseStats', () => {
    it('should return database statistics', () => {
      const now = new Date().toISOString();

      // Insert test data
      db.prepare(
        `INSERT INTO entities (id, type, name, namespace, created_at, updated_at) VALUES (?, ?, ?, ?, ?, ?)`
      ).run('E1', 'class', 'Test', 'ns', now, now);
      db.prepare(
        `INSERT INTO entities (id, type, name, namespace, created_at, updated_at) VALUES (?, ?, ?, ?, ?, ?)`
      ).run('E2', 'method', 'Test2', 'ns', now, now);
      db.prepare(
        `INSERT INTO relationships (id, source_id, target_id, type, created_at) VALUES (?, ?, ?, ?, ?)`
      ).run('R1', 'E1', 'E2', 'contains', now);

      const stats = optimizer.getDatabaseStats();

      expect(stats.entityCount).toBe(2);
      expect(stats.relationshipCount).toBe(1);
      expect(stats.indexCount).toBeGreaterThan(0);
      expect(stats.dbSizeBytes).toBeGreaterThanOrEqual(0);
    });
  });

  describe('runAnalyze', () => {
    it('should run ANALYZE without error', () => {
      expect(() => {
        optimizer.runAnalyze();
      }).not.toThrow();
    });
  });

  describe('Performance Test (REQ-YI-IDX-001)', () => {
    it('should analyze 1000 entities within acceptable time', async () => {
      const now = new Date().toISOString();

      // Insert 1000 entities
      const insertStmt = db.prepare(
        `INSERT INTO entities (id, type, name, namespace, created_at, updated_at) VALUES (?, ?, ?, ?, ?, ?)`
      );

      const insertMany = db.transaction(() => {
        for (let i = 0; i < 1000; i++) {
          const type = i % 5 === 0 ? 'class' : i % 3 === 0 ? 'method' : 'variable';
          insertStmt.run(`E${i}`, type, `Entity${i}`, 'test-namespace', now, now);
        }
      });

      insertMany();

      const result = await optimizer.analyzeIndexes();

      // Should complete within 1 second for 1000 entities
      expect(result.analysisTimeMs).toBeLessThan(1000);
      expect(result.entityCount).toBe(1000);
    });
  });
});
