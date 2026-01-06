/**
 * Index Optimizer for YATA Local
 *
 * Analyzes database indexes and provides optimization recommendations.
 *
 * @packageDocumentation
 * @module @nahisaho/yata-local/index-optimizer
 *
 * @see REQ-YI-IDX-001 - Index Analysis
 * @see REQ-YI-IDX-002 - Composite Index Generation
 * @see REQ-YI-IDX-003 - Query Performance Monitoring
 * @see DES-YATA-IMPROVEMENTS-001 - Design Document
 */

import type Database from 'better-sqlite3';

// ============================================================
// Types
// ============================================================

/**
 * Information about a database index
 */
export interface IndexInfo {
  /** Index name */
  name: string;
  /** Table name */
  table: string;
  /** Columns in the index */
  columns: string[];
  /** Whether the index is unique */
  unique: boolean;
  /** Estimated number of rows */
  rowCount: number;
  /** SQLite internal sequential number */
  seq: number;
}

/**
 * Index recommendation
 */
export interface IndexRecommendation {
  /** Recommendation type */
  type: 'create' | 'drop' | 'modify';
  /** Target table */
  table: string;
  /** Columns to index */
  columns: string[];
  /** Reason for recommendation */
  reason: string;
  /** Estimated improvement percentage */
  estimatedImprovement: number;
  /** SQL statement to execute */
  sql: string;
  /** Priority (1-5, 1 is highest) */
  priority: number;
}

/**
 * Query statistics from monitoring
 */
export interface QueryStats {
  /** Query pattern (normalized) */
  queryPattern: string;
  /** Query hash for grouping */
  queryHash: string;
  /** Average execution time in milliseconds */
  avgTimeMs: number;
  /** Minimum execution time */
  minTimeMs: number;
  /** Maximum execution time */
  maxTimeMs: number;
  /** Total execution count */
  executionCount: number;
  /** Average rows examined */
  avgRowsExamined: number;
  /** Indexes used (if available) */
  indexesUsed: string[];
  /** Last execution timestamp */
  lastExecuted: string;
}

/**
 * Complete index analysis result
 * @see REQ-YI-IDX-001
 */
export interface IndexAnalysisResult {
  /** List of existing indexes */
  indexes: IndexInfo[];
  /** Optimization recommendations */
  recommendations: IndexRecommendation[];
  /** Query statistics (if monitoring enabled) */
  queryStats: QueryStats[];
  /** Analysis timestamp */
  analyzedAt: string;
  /** Analysis duration in milliseconds */
  analysisTimeMs: number;
  /** Database file path */
  databasePath: string;
  /** Total entities count */
  entityCount: number;
  /** Total relationships count */
  relationshipCount: number;
}

/**
 * Options for index analysis
 */
export interface AnalysisOptions {
  /** Include query statistics */
  includeQueryStats?: boolean;
  /** Maximum recommendations to return */
  maxRecommendations?: number;
  /** Minimum improvement threshold for recommendations */
  minImprovementThreshold?: number;
}

/**
 * Options for creating composite index
 */
export interface CompositeIndexOptions {
  /** Index name (auto-generated if not provided) */
  name?: string;
  /** Whether to create unique index */
  unique?: boolean;
  /** Execute immediately or return SQL only */
  execute?: boolean;
}

// ============================================================
// Constants
// ============================================================

/**
 * Common query patterns that benefit from composite indexes
 */
const COMPOSITE_INDEX_PATTERNS: Array<{
  table: string;
  columns: string[];
  reason: string;
  improvement: number;
}> = [
  {
    table: 'entities',
    columns: ['namespace', 'type'],
    reason: 'Frequent filtering by namespace and type together',
    improvement: 40,
  },
  {
    table: 'entities',
    columns: ['type', 'updated_at'],
    reason: 'Recent entities by type query optimization',
    improvement: 35,
  },
  {
    table: 'relationships',
    columns: ['source_id', 'type'],
    reason: 'Outgoing relationships by type lookup',
    improvement: 45,
  },
  {
    table: 'relationships',
    columns: ['target_id', 'type'],
    reason: 'Incoming relationships by type lookup',
    improvement: 45,
  },
  {
    table: 'patterns',
    columns: ['category', 'confidence'],
    reason: 'High-confidence patterns by category query',
    improvement: 30,
  },
];

/**
 * Schema for query logging table
 * @see REQ-YI-IDX-003
 */
export const QUERY_LOG_SCHEMA = `
-- Query log table for performance monitoring
CREATE TABLE IF NOT EXISTS query_log (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  query_hash TEXT NOT NULL,
  query_pattern TEXT NOT NULL,
  execution_time_ms INTEGER NOT NULL,
  rows_examined INTEGER,
  indexes_used TEXT,
  timestamp TEXT NOT NULL
);

CREATE INDEX IF NOT EXISTS idx_query_log_hash ON query_log(query_hash);
CREATE INDEX IF NOT EXISTS idx_query_log_timestamp ON query_log(timestamp);
CREATE INDEX IF NOT EXISTS idx_query_log_time ON query_log(execution_time_ms);
`;

// ============================================================
// IndexOptimizer Class
// ============================================================

/**
 * Index Optimizer for YATA Local database
 *
 * Provides index analysis, recommendations, and monitoring capabilities.
 *
 * @example
 * ```typescript
 * const optimizer = new IndexOptimizer(db);
 * const result = await optimizer.analyzeIndexes();
 * console.log(result.recommendations);
 * ```
 *
 * @see REQ-YI-IDX-001
 * @see REQ-YI-IDX-002
 * @see REQ-YI-IDX-003
 */
export class IndexOptimizer {
  private db: Database.Database;
  private monitoringEnabled: boolean = false;

  constructor(db: Database.Database) {
    this.db = db;
  }

  // ============================================================
  // Index Analysis (REQ-YI-IDX-001)
  // ============================================================

  /**
   * Analyze database indexes and generate recommendations
   *
   * Performance target: Complete within 5 seconds for up to 100,000 entities
   *
   * @param options - Analysis options
   * @returns Index analysis result with recommendations
   *
   * @see REQ-YI-IDX-001
   */
  async analyzeIndexes(options: AnalysisOptions = {}): Promise<IndexAnalysisResult> {
    const startTime = Date.now();
    const {
      includeQueryStats = true,
      maxRecommendations = 10,
      minImprovementThreshold = 10,
    } = options;

    // Get existing indexes
    const indexes = this.getExistingIndexes();

    // Get table statistics
    const entityCount = this.getTableRowCount('entities');
    const relationshipCount = this.getTableRowCount('relationships');

    // Generate recommendations
    const allRecommendations = this.generateRecommendations(indexes);
    const recommendations = allRecommendations
      .filter(r => r.estimatedImprovement >= minImprovementThreshold)
      .slice(0, maxRecommendations);

    // Get query statistics if available and requested
    let queryStats: QueryStats[] = [];
    if (includeQueryStats && this.isQueryLogTableExists()) {
      queryStats = this.getQueryStats();
    }

    const analysisTimeMs = Date.now() - startTime;

    return {
      indexes,
      recommendations,
      queryStats,
      analyzedAt: new Date().toISOString(),
      analysisTimeMs,
      databasePath: this.db.name,
      entityCount,
      relationshipCount,
    };
  }

  /**
   * Get all existing indexes in the database
   */
  private getExistingIndexes(): IndexInfo[] {
    const tables = ['entities', 'relationships', 'patterns', 'learning_cycles', 'kgprs', 'change_log'];
    const indexes: IndexInfo[] = [];

    for (const table of tables) {
      try {
        const tableIndexes = this.db
          .prepare(`PRAGMA index_list('${table}')`)
          .all() as Array<{ name: string; unique: number; seq: number }>;

        for (const idx of tableIndexes) {
          // Skip auto-indexes
          if (idx.name.startsWith('sqlite_autoindex')) continue;

          const columns = this.db
            .prepare(`PRAGMA index_info('${idx.name}')`)
            .all() as Array<{ name: string }>;

          // Get row count estimate
          let rowCount = 0;
          try {
            const stat = this.db
              .prepare(`SELECT stat FROM sqlite_stat1 WHERE tbl = ? AND idx = ?`)
              .get(table, idx.name) as { stat: string } | undefined;
            if (stat) {
              rowCount = parseInt(stat.stat.split(' ')[0], 10);
            }
          } catch {
            // sqlite_stat1 may not exist if ANALYZE hasn't been run
          }

          indexes.push({
            name: idx.name,
            table,
            columns: columns.map(c => c.name),
            unique: idx.unique === 1,
            rowCount,
            seq: idx.seq,
          });
        }
      } catch {
        // Table may not exist
      }
    }

    return indexes;
  }

  /**
   * Generate index recommendations based on analysis
   */
  private generateRecommendations(existingIndexes: IndexInfo[]): IndexRecommendation[] {
    const recommendations: IndexRecommendation[] = [];
    const existingIndexSet = new Set(
      existingIndexes.map(idx => `${idx.table}:${idx.columns.join(',')}`)
    );

    // Check for missing composite indexes
    for (const pattern of COMPOSITE_INDEX_PATTERNS) {
      const key = `${pattern.table}:${pattern.columns.join(',')}`;
      if (!existingIndexSet.has(key)) {
        const indexName = `idx_${pattern.table}_${pattern.columns.join('_')}`;
        recommendations.push({
          type: 'create',
          table: pattern.table,
          columns: pattern.columns,
          reason: pattern.reason,
          estimatedImprovement: pattern.improvement,
          sql: `CREATE INDEX IF NOT EXISTS ${indexName} ON ${pattern.table}(${pattern.columns.join(', ')})`,
          priority: pattern.improvement >= 40 ? 1 : pattern.improvement >= 30 ? 2 : 3,
        });
      }
    }

    // Check for potentially unused indexes based on query patterns
    // This is a heuristic - actual usage requires monitoring data
    const coreIndexes = new Set([
      'idx_entities_type',
      'idx_entities_name',
      'idx_entities_namespace',
      'idx_relationships_source',
      'idx_relationships_target',
    ]);

    for (const idx of existingIndexes) {
      if (!coreIndexes.has(idx.name) && idx.rowCount === 0) {
        recommendations.push({
          type: 'drop',
          table: idx.table,
          columns: idx.columns,
          reason: 'Index appears unused (no recorded statistics)',
          estimatedImprovement: 5,
          sql: `DROP INDEX IF EXISTS ${idx.name}`,
          priority: 5,
        });
      }
    }

    // Sort by priority and improvement
    return recommendations.sort((a, b) => {
      if (a.priority !== b.priority) return a.priority - b.priority;
      return b.estimatedImprovement - a.estimatedImprovement;
    });
  }

  /**
   * Get row count for a table
   */
  private getTableRowCount(table: string): number {
    try {
      const result = this.db
        .prepare(`SELECT COUNT(*) as count FROM ${table}`)
        .get() as { count: number };
      return result.count;
    } catch {
      return 0;
    }
  }

  // ============================================================
  // Composite Index Creation (REQ-YI-IDX-002)
  // ============================================================

  /**
   * Create a composite index on the specified table and columns
   *
   * @param table - Table name
   * @param columns - Column names for the composite index
   * @param options - Creation options
   * @returns SQL statement (and executes if options.execute is true)
   *
   * @see REQ-YI-IDX-002
   */
  createCompositeIndex(
    table: string,
    columns: string[],
    options: CompositeIndexOptions = {}
  ): string {
    const { name, unique = false, execute = true } = options;

    // Generate index name if not provided
    const indexName = name || `idx_${table}_${columns.join('_')}`;

    // Validate table exists
    const tableExists = this.db
      .prepare(`SELECT name FROM sqlite_master WHERE type='table' AND name=?`)
      .get(table);

    if (!tableExists) {
      throw new Error(`Table '${table}' does not exist`);
    }

    // Validate columns exist
    const tableInfo = this.db
      .prepare(`PRAGMA table_info('${table}')`)
      .all() as Array<{ name: string }>;
    const existingColumns = new Set(tableInfo.map(c => c.name));

    for (const col of columns) {
      if (!existingColumns.has(col)) {
        throw new Error(`Column '${col}' does not exist in table '${table}'`);
      }
    }

    // Generate SQL
    const uniqueKeyword = unique ? 'UNIQUE ' : '';
    const sql = `CREATE ${uniqueKeyword}INDEX IF NOT EXISTS ${indexName} ON ${table}(${columns.join(', ')})`;

    // Execute if requested
    if (execute) {
      this.db.exec(sql);
    }

    return sql;
  }

  /**
   * Apply all recommended indexes
   *
   * @param recommendations - List of recommendations to apply
   * @returns Applied index names
   */
  applyRecommendations(recommendations: IndexRecommendation[]): string[] {
    const applied: string[] = [];

    for (const rec of recommendations) {
      if (rec.type === 'create') {
        try {
          this.db.exec(rec.sql);
          const indexName = `idx_${rec.table}_${rec.columns.join('_')}`;
          applied.push(indexName);
        } catch (error) {
          // Index might already exist
          console.warn(`Warning: Could not apply index: ${rec.sql}`, error);
        }
      }
    }

    // Run ANALYZE to update statistics
    if (applied.length > 0) {
      this.db.exec('ANALYZE');
    }

    return applied;
  }

  // ============================================================
  // Query Performance Monitoring (REQ-YI-IDX-003)
  // ============================================================

  /**
   * Enable query performance monitoring
   *
   * Creates query_log table if it doesn't exist.
   *
   * @see REQ-YI-IDX-003
   */
  enableMonitoring(): void {
    this.db.exec(QUERY_LOG_SCHEMA);
    this.monitoringEnabled = true;
  }

  /**
   * Disable query performance monitoring
   */
  disableMonitoring(): void {
    this.monitoringEnabled = false;
  }

  /**
   * Check if monitoring is enabled
   */
  isMonitoringEnabled(): boolean {
    return this.monitoringEnabled;
  }

  /**
   * Log a query execution for monitoring
   *
   * @param queryPattern - Normalized query pattern
   * @param executionTimeMs - Execution time in milliseconds
   * @param rowsExamined - Number of rows examined (optional)
   * @param indexesUsed - List of indexes used (optional)
   */
  logQuery(
    queryPattern: string,
    executionTimeMs: number,
    rowsExamined?: number,
    indexesUsed?: string[]
  ): void {
    if (!this.monitoringEnabled || !this.isQueryLogTableExists()) return;

    const queryHash = this.hashQuery(queryPattern);
    const timestamp = new Date().toISOString();

    this.db
      .prepare(
        `INSERT INTO query_log (query_hash, query_pattern, execution_time_ms, rows_examined, indexes_used, timestamp)
         VALUES (?, ?, ?, ?, ?, ?)`
      )
      .run(
        queryHash,
        queryPattern,
        executionTimeMs,
        rowsExamined ?? null,
        indexesUsed ? JSON.stringify(indexesUsed) : null,
        timestamp
      );
  }

  /**
   * Get query statistics from monitoring data
   *
   * @param limit - Maximum number of query patterns to return
   * @returns Aggregated query statistics
   */
  getQueryStats(limit: number = 50): QueryStats[] {
    if (!this.isQueryLogTableExists()) return [];

    const stats = this.db
      .prepare(
        `SELECT 
           query_hash,
           query_pattern,
           AVG(execution_time_ms) as avg_time,
           MIN(execution_time_ms) as min_time,
           MAX(execution_time_ms) as max_time,
           COUNT(*) as exec_count,
           AVG(rows_examined) as avg_rows,
           MAX(timestamp) as last_executed
         FROM query_log
         GROUP BY query_hash
         ORDER BY avg_time DESC
         LIMIT ?`
      )
      .all(limit) as Array<{
        query_hash: string;
        query_pattern: string;
        avg_time: number;
        min_time: number;
        max_time: number;
        exec_count: number;
        avg_rows: number | null;
        last_executed: string;
      }>;

    return stats.map(s => ({
      queryPattern: s.query_pattern,
      queryHash: s.query_hash,
      avgTimeMs: Math.round(s.avg_time * 100) / 100,
      minTimeMs: s.min_time,
      maxTimeMs: s.max_time,
      executionCount: s.exec_count,
      avgRowsExamined: s.avg_rows ? Math.round(s.avg_rows) : 0,
      indexesUsed: [], // Would need to aggregate from individual logs
      lastExecuted: s.last_executed,
    }));
  }

  /**
   * Get slow queries (queries exceeding threshold)
   *
   * @param thresholdMs - Minimum execution time to consider slow
   * @param limit - Maximum results to return
   * @returns Slow query entries
   */
  getSlowQueries(
    thresholdMs: number = 100,
    limit: number = 20
  ): QueryStats[] {
    if (!this.isQueryLogTableExists()) return [];

    const stats = this.db
      .prepare(
        `SELECT 
           query_hash,
           query_pattern,
           AVG(execution_time_ms) as avg_time,
           MIN(execution_time_ms) as min_time,
           MAX(execution_time_ms) as max_time,
           COUNT(*) as exec_count,
           AVG(rows_examined) as avg_rows,
           MAX(timestamp) as last_executed
         FROM query_log
         GROUP BY query_hash
         HAVING avg_time >= ?
         ORDER BY avg_time DESC
         LIMIT ?`
      )
      .all(thresholdMs, limit) as Array<{
        query_hash: string;
        query_pattern: string;
        avg_time: number;
        min_time: number;
        max_time: number;
        exec_count: number;
        avg_rows: number | null;
        last_executed: string;
      }>;

    return stats.map(s => ({
      queryPattern: s.query_pattern,
      queryHash: s.query_hash,
      avgTimeMs: Math.round(s.avg_time * 100) / 100,
      minTimeMs: s.min_time,
      maxTimeMs: s.max_time,
      executionCount: s.exec_count,
      avgRowsExamined: s.avg_rows ? Math.round(s.avg_rows) : 0,
      indexesUsed: [],
      lastExecuted: s.last_executed,
    }));
  }

  /**
   * Clear query log (older than specified days)
   *
   * @param olderThanDays - Delete logs older than this many days (0 = all)
   * @returns Number of deleted entries
   */
  clearQueryLog(olderThanDays: number = 30): number {
    if (!this.isQueryLogTableExists()) return 0;

    if (olderThanDays === 0) {
      const result = this.db.prepare('DELETE FROM query_log').run();
      return result.changes;
    }

    const cutoffDate = new Date();
    cutoffDate.setDate(cutoffDate.getDate() - olderThanDays);
    const cutoffIso = cutoffDate.toISOString();

    const result = this.db
      .prepare('DELETE FROM query_log WHERE timestamp < ?')
      .run(cutoffIso);

    return result.changes;
  }

  // ============================================================
  // Helper Methods
  // ============================================================

  /**
   * Check if query_log table exists
   */
  private isQueryLogTableExists(): boolean {
    const result = this.db
      .prepare(`SELECT name FROM sqlite_master WHERE type='table' AND name='query_log'`)
      .get();
    return !!result;
  }

  /**
   * Generate a hash for query pattern grouping
   */
  private hashQuery(query: string): string {
    // Simple hash for grouping similar queries
    let hash = 0;
    const normalized = query
      .toLowerCase()
      .replace(/\s+/g, ' ')
      .replace(/\d+/g, '?')
      .replace(/'[^']*'/g, '?')
      .trim();

    for (let i = 0; i < normalized.length; i++) {
      const char = normalized.charCodeAt(i);
      hash = (hash << 5) - hash + char;
      hash = hash & hash; // Convert to 32-bit integer
    }

    return Math.abs(hash).toString(16).padStart(8, '0');
  }

  /**
   * Run ANALYZE to update SQLite statistics
   */
  runAnalyze(): void {
    this.db.exec('ANALYZE');
  }

  /**
   * Get database statistics summary
   */
  getDatabaseStats(): {
    entityCount: number;
    relationshipCount: number;
    patternCount: number;
    indexCount: number;
    dbSizeBytes: number;
  } {
    const entityCount = this.getTableRowCount('entities');
    const relationshipCount = this.getTableRowCount('relationships');
    const patternCount = this.getTableRowCount('patterns');
    
    const indexes = this.getExistingIndexes();

    // Get database size
    let dbSizeBytes = 0;
    try {
      const pageCount = (this.db.prepare('PRAGMA page_count').get() as { page_count: number }).page_count;
      const pageSize = (this.db.prepare('PRAGMA page_size').get() as { page_size: number }).page_size;
      dbSizeBytes = pageCount * pageSize;
    } catch {
      // Fallback
    }

    return {
      entityCount,
      relationshipCount,
      patternCount,
      indexCount: indexes.length,
      dbSizeBytes,
    };
  }
}
