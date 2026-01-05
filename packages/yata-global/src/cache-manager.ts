/**
 * YATA Global - Cache Manager
 *
 * Local caching for offline support and performance
 *
 * @packageDocumentation
 * @module @nahisaho/yata-global
 *
 * @see REQ-YG-SYNC-003
 */

import Database from 'better-sqlite3';
import type {
  FrameworkKnowledge,
  SharedPattern,
  SyncConfig,
} from './types.js';

/**
 * SQLite schema for cache
 */
const CACHE_SCHEMA = `
  -- Frameworks cache
  CREATE TABLE IF NOT EXISTS frameworks (
    id TEXT PRIMARY KEY,
    data TEXT NOT NULL,
    expires_at INTEGER,
    created_at INTEGER NOT NULL DEFAULT (strftime('%s', 'now') * 1000)
  );

  -- Patterns cache
  CREATE TABLE IF NOT EXISTS patterns (
    id TEXT PRIMARY KEY,
    data TEXT NOT NULL,
    expires_at INTEGER,
    created_at INTEGER NOT NULL DEFAULT (strftime('%s', 'now') * 1000)
  );

  -- Generic key-value cache
  CREATE TABLE IF NOT EXISTS cache (
    key TEXT PRIMARY KEY,
    value TEXT NOT NULL,
    expires_at INTEGER,
    created_at INTEGER NOT NULL DEFAULT (strftime('%s', 'now') * 1000)
  );

  -- Sync metadata
  CREATE TABLE IF NOT EXISTS sync_meta (
    key TEXT PRIMARY KEY,
    value TEXT NOT NULL,
    updated_at INTEGER NOT NULL DEFAULT (strftime('%s', 'now') * 1000)
  );

  -- Indexes
  CREATE INDEX IF NOT EXISTS idx_frameworks_expires ON frameworks(expires_at);
  CREATE INDEX IF NOT EXISTS idx_patterns_expires ON patterns(expires_at);
  CREATE INDEX IF NOT EXISTS idx_cache_expires ON cache(expires_at);
`;

/**
 * Cache manager for offline support
 */
export class CacheManager {
  private db: Database.Database;
  private config: SyncConfig;
  private defaultTtl: number = 3600 * 1000; // 1 hour in ms

  constructor(dbPath: string, config: SyncConfig) {
    this.db = new Database(dbPath);
    this.config = config;

    // Enable WAL mode for better performance
    this.db.pragma('journal_mode = WAL');

    // Initialize schema
    this.db.exec(CACHE_SCHEMA);
  }

  /**
   * Close database connection
   */
  close(): void {
    this.db.close();
  }

  // ========================================
  // Framework Cache
  // ========================================

  /**
   * Cache a framework
   */
  cacheFramework(framework: FrameworkKnowledge, ttl?: number): void {
    const expiresAt = ttl ? Date.now() + ttl : Date.now() + this.defaultTtl;
    const stmt = this.db.prepare(`
      INSERT OR REPLACE INTO frameworks (id, data, expires_at, created_at)
      VALUES (?, ?, ?, ?)
    `);
    stmt.run(framework.id, JSON.stringify(framework), expiresAt, Date.now());
  }

  /**
   * Cache multiple frameworks
   */
  cacheFrameworks(frameworks: FrameworkKnowledge[], ttl?: number): void {
    const expiresAt = ttl ? Date.now() + ttl : Date.now() + this.defaultTtl;
    const stmt = this.db.prepare(`
      INSERT OR REPLACE INTO frameworks (id, data, expires_at, created_at)
      VALUES (?, ?, ?, ?)
    `);

    const insert = this.db.transaction((fws: FrameworkKnowledge[]) => {
      for (const fw of fws) {
        stmt.run(fw.id, JSON.stringify(fw), expiresAt, Date.now());
      }
    });

    insert(frameworks);
  }

  /**
   * Get cached framework
   */
  getFramework(id: string): FrameworkKnowledge | null {
    const stmt = this.db.prepare(`
      SELECT data FROM frameworks
      WHERE id = ? AND (expires_at IS NULL OR expires_at > ?)
    `);
    const row = stmt.get(id, Date.now()) as { data: string } | undefined;
    return row ? this.parseFramework(row.data) : null;
  }

  /**
   * Get all cached frameworks
   */
  getAllFrameworks(): FrameworkKnowledge[] {
    const stmt = this.db.prepare(`
      SELECT data FROM frameworks
      WHERE expires_at IS NULL OR expires_at > ?
    `);
    const rows = stmt.all(Date.now()) as { data: string }[];
    return rows.map(row => this.parseFramework(row.data)).filter((f): f is FrameworkKnowledge => f !== null);
  }

  /**
   * Parse framework JSON with date conversion
   */
  private parseFramework(json: string): FrameworkKnowledge | null {
    try {
      const data = JSON.parse(json);
      return {
        ...data,
        updatedAt: new Date(data.updatedAt),
        createdAt: new Date(data.createdAt),
      };
    } catch {
      return null;
    }
  }

  // ========================================
  // Pattern Cache
  // ========================================

  /**
   * Cache a pattern
   */
  cachePattern(pattern: SharedPattern, ttl?: number): void {
    const expiresAt = ttl ? Date.now() + ttl : Date.now() + this.defaultTtl;
    const stmt = this.db.prepare(`
      INSERT OR REPLACE INTO patterns (id, data, expires_at, created_at)
      VALUES (?, ?, ?, ?)
    `);
    stmt.run(pattern.id, JSON.stringify(pattern), expiresAt, Date.now());
  }

  /**
   * Cache multiple patterns
   */
  cachePatterns(patterns: SharedPattern[], ttl?: number): void {
    const expiresAt = ttl ? Date.now() + ttl : Date.now() + this.defaultTtl;
    const stmt = this.db.prepare(`
      INSERT OR REPLACE INTO patterns (id, data, expires_at, created_at)
      VALUES (?, ?, ?, ?)
    `);

    const insert = this.db.transaction((ps: SharedPattern[]) => {
      for (const p of ps) {
        stmt.run(p.id, JSON.stringify(p), expiresAt, Date.now());
      }
    });

    insert(patterns);
  }

  /**
   * Get cached pattern
   */
  getPattern(id: string): SharedPattern | null {
    const stmt = this.db.prepare(`
      SELECT data FROM patterns
      WHERE id = ? AND (expires_at IS NULL OR expires_at > ?)
    `);
    const row = stmt.get(id, Date.now()) as { data: string } | undefined;
    return row ? this.parsePattern(row.data) : null;
  }

  /**
   * Get all cached patterns
   */
  getAllPatterns(): SharedPattern[] {
    const stmt = this.db.prepare(`
      SELECT data FROM patterns
      WHERE expires_at IS NULL OR expires_at > ?
    `);
    const rows = stmt.all(Date.now()) as { data: string }[];
    return rows.map(row => this.parsePattern(row.data)).filter((p): p is SharedPattern => p !== null);
  }

  /**
   * Parse pattern JSON with date conversion
   */
  private parsePattern(json: string): SharedPattern | null {
    try {
      const data = JSON.parse(json);
      return {
        ...data,
        updatedAt: new Date(data.updatedAt),
        createdAt: new Date(data.createdAt),
      };
    } catch {
      return null;
    }
  }

  // ========================================
  // Generic Cache
  // ========================================

  /**
   * Set generic cache value
   */
  set<T>(key: string, value: T, ttl?: number): void {
    const expiresAt = ttl ? Date.now() + ttl : null;
    const stmt = this.db.prepare(`
      INSERT OR REPLACE INTO cache (key, value, expires_at, created_at)
      VALUES (?, ?, ?, ?)
    `);
    stmt.run(key, JSON.stringify(value), expiresAt, Date.now());
  }

  /**
   * Get generic cache value
   */
  get<T>(key: string): T | null {
    const stmt = this.db.prepare(`
      SELECT value FROM cache
      WHERE key = ? AND (expires_at IS NULL OR expires_at > ?)
    `);
    const row = stmt.get(key, Date.now()) as { value: string } | undefined;
    if (!row) return null;
    try {
      return JSON.parse(row.value) as T;
    } catch {
      return null;
    }
  }

  /**
   * Delete cache entry
   */
  delete(key: string): boolean {
    const stmt = this.db.prepare('DELETE FROM cache WHERE key = ?');
    const result = stmt.run(key);
    return result.changes > 0;
  }

  /**
   * Check if key exists and is valid
   */
  has(key: string): boolean {
    const stmt = this.db.prepare(`
      SELECT 1 FROM cache
      WHERE key = ? AND (expires_at IS NULL OR expires_at > ?)
    `);
    return stmt.get(key, Date.now()) !== undefined;
  }

  // ========================================
  // Sync Metadata
  // ========================================

  /**
   * Set sync metadata
   */
  setSyncMeta(key: string, value: string): void {
    const stmt = this.db.prepare(`
      INSERT OR REPLACE INTO sync_meta (key, value, updated_at)
      VALUES (?, ?, ?)
    `);
    stmt.run(key, value, Date.now());
  }

  /**
   * Get sync metadata
   */
  getSyncMeta(key: string): string | null {
    const stmt = this.db.prepare('SELECT value FROM sync_meta WHERE key = ?');
    const row = stmt.get(key) as { value: string } | undefined;
    return row?.value ?? null;
  }

  /**
   * Get last sync timestamp
   */
  getLastSyncTime(): Date | null {
    const value = this.getSyncMeta('last_sync');
    return value ? new Date(parseInt(value, 10)) : null;
  }

  /**
   * Set last sync timestamp
   */
  setLastSyncTime(time: Date): void {
    this.setSyncMeta('last_sync', time.getTime().toString());
  }

  // ========================================
  // Cache Management
  // ========================================

  /**
   * Clear expired entries
   */
  clearExpired(): number {
    const now = Date.now();
    let cleared = 0;

    const tables = ['frameworks', 'patterns', 'cache'];
    for (const table of tables) {
      const stmt = this.db.prepare(`DELETE FROM ${table} WHERE expires_at IS NOT NULL AND expires_at <= ?`);
      const result = stmt.run(now);
      cleared += result.changes;
    }

    return cleared;
  }

  /**
   * Clear all cache
   */
  clearAll(): void {
    this.db.exec(`
      DELETE FROM frameworks;
      DELETE FROM patterns;
      DELETE FROM cache;
    `);
  }

  /**
   * Get cache size in bytes
   */
  getCacheSize(): number {
    const stmt = this.db.prepare(`
      SELECT page_count * page_size as size FROM pragma_page_count(), pragma_page_size()
    `);
    const row = stmt.get() as { size: number } | undefined;
    return row?.size ?? 0;
  }

  /**
   * Get cache statistics
   */
  getStats(): {
    frameworkCount: number;
    patternCount: number;
    cacheEntries: number;
    sizeBytes: number;
  } {
    const fwCount = this.db.prepare('SELECT COUNT(*) as count FROM frameworks WHERE expires_at IS NULL OR expires_at > ?').get(Date.now()) as { count: number };
    const pCount = this.db.prepare('SELECT COUNT(*) as count FROM patterns WHERE expires_at IS NULL OR expires_at > ?').get(Date.now()) as { count: number };
    const cacheCount = this.db.prepare('SELECT COUNT(*) as count FROM cache WHERE expires_at IS NULL OR expires_at > ?').get(Date.now()) as { count: number };

    return {
      frameworkCount: fwCount.count,
      patternCount: pCount.count,
      cacheEntries: cacheCount.count,
      sizeBytes: this.getCacheSize(),
    };
  }

  /**
   * Enforce maximum cache size
   */
  enforceMaxSize(): void {
    const currentSize = this.getCacheSize();
    if (currentSize <= this.config.maxCacheSize) return;

    // Clear expired first
    this.clearExpired();

    // If still too large, clear oldest entries
    if (this.getCacheSize() > this.config.maxCacheSize) {
      // Delete oldest 20% of cache entries
      const tables = ['frameworks', 'patterns', 'cache'];
      for (const table of tables) {
        const countStmt = this.db.prepare(`SELECT COUNT(*) as count FROM ${table}`);
        const { count } = countStmt.get() as { count: number };
        const toDelete = Math.ceil(count * 0.2);

        if (toDelete > 0) {
          const deleteStmt = this.db.prepare(`
            DELETE FROM ${table}
            WHERE rowid IN (
              SELECT rowid FROM ${table}
              ORDER BY created_at ASC
              LIMIT ?
            )
          `);
          deleteStmt.run(toDelete);
        }
      }
    }
  }
}
