/**
 * YATA Local - Main Entry Point
 *
 * SQLite-based local knowledge graph storage for AI coding assistants.
 *
 * @packageDocumentation
 * @module @nahisaho/yata-local
 *
 * @example
 * ```typescript
 * import { createYataLocal } from '@nahisaho/yata-local';
 *
 * const yata = createYataLocal({ path: './knowledge.db' });
 * await yata.open();
 *
 * // Add entities
 * const classId = await yata.addEntity({
 *   type: 'class',
 *   name: 'UserService',
 *   namespace: 'app.services',
 *   filePath: 'src/services/user.ts',
 * });
 *
 * // Query graph
 * const result = await yata.query({
 *   entityFilters: { types: ['class', 'interface'] },
 *   textSearch: 'User',
 * });
 *
 * await yata.close();
 * ```
 */

import { randomUUID } from 'crypto';
import type {
  DatabaseConfig,
  Entity,
  EntityType,
  Relationship,
  RelationType,
  GraphQuery,
  QueryResult,
  QueryOptions,
  Path,
  Subgraph,
  GraphPattern,
  PatternMatch,
  InferenceRule,
  Constraint,
  ValidationResult,
  Delta,
  MergeResult,
  GraphStats,
} from './types.js';
import { DEFAULT_DB_CONFIG } from './types.js';
import { YataDatabase } from './database.js';
import { QueryEngine } from './query-engine.js';
import { ReasoningEngine, type InferenceResult } from './reasoning.js';
import { IoModule, type JsonExport, type RdfExportOptions } from './io.js';

/**
 * YATA Local implementation
 */
export class YataLocal {
  private db: YataDatabase;
  private queryEngine!: QueryEngine;
  private reasoningEngine!: ReasoningEngine;
  private ioModule!: IoModule;
  private config: DatabaseConfig;

  constructor(config: Partial<DatabaseConfig> = {}) {
    this.config = { ...DEFAULT_DB_CONFIG, ...config };
    this.db = new YataDatabase(this.config);
  }

  /**
   * Open database connection
   */
  async open(config?: Partial<DatabaseConfig>): Promise<void> {
    if (config) {
      this.config = { ...this.config, ...config };
      this.db = new YataDatabase(this.config);
    }
    await this.db.open();

    // Initialize engines
    this.queryEngine = new QueryEngine(this.db);
    this.reasoningEngine = new ReasoningEngine(this.db, this.queryEngine);
    this.ioModule = new IoModule(this.db);
  }

  /**
   * Close database connection
   */
  async close(): Promise<void> {
    await this.db.close();
  }

  /**
   * Check if database is open
   */
  isOpen(): boolean {
    return this.db.isOpen();
  }

  // Entity Operations

  /**
   * Add entity to graph
   * @see REQ-YL-UPDATE-001
   */
  async addEntity(
    entity: Omit<Entity, 'id' | 'createdAt' | 'updatedAt'>
  ): Promise<string> {
    const id = randomUUID();
    const now = new Date();

    const fullEntity: Entity = {
      ...entity,
      id,
      metadata: entity.metadata ?? {},
      createdAt: now,
      updatedAt: now,
    };

    this.db.insertEntity(fullEntity);
    return id;
  }

  /**
   * Add multiple entities in batch
   */
  async addEntities(
    entities: Array<Omit<Entity, 'id' | 'createdAt' | 'updatedAt'>>
  ): Promise<string[]> {
    const now = new Date();
    const fullEntities: Entity[] = entities.map(e => ({
      ...e,
      id: randomUUID(),
      metadata: e.metadata ?? {},
      createdAt: now,
      updatedAt: now,
    }));

    this.db.insertEntities(fullEntities);
    return fullEntities.map(e => e.id);
  }

  /**
   * Get entity by ID
   */
  async getEntity(id: string): Promise<Entity | null> {
    return this.db.getEntity(id);
  }

  /**
   * Update entity
   * @see REQ-YL-UPDATE-002
   */
  async updateEntity(
    id: string,
    updates: Partial<Omit<Entity, 'id' | 'createdAt'>>
  ): Promise<void> {
    this.db.updateEntity(id, updates);
  }

  /**
   * Delete entity
   * @see REQ-YL-UPDATE-003
   */
  async deleteEntity(id: string): Promise<void> {
    this.db.deleteEntity(id);
  }

  /**
   * Delete entities by file path
   */
  async deleteEntitiesByFile(filePath: string): Promise<number> {
    return this.db.deleteEntitiesByFile(filePath);
  }

  // High-Level Query APIs (P0 Enhancement)

  /**
   * Get all entities by type
   * @see REQ-YL-QUERY-001
   */
  async getEntitiesByType(type: EntityType): Promise<Entity[]> {
    const result = this.db.queryEntities({ type }, 10000, 0);
    return result.entities;
  }

  /**
   * Get all entities by namespace
   * @see REQ-YL-QUERY-001
   */
  async getEntitiesByNamespace(namespace: string): Promise<Entity[]> {
    const result = this.db.queryEntities({ namespace }, 10000, 0);
    return result.entities;
  }

  /**
   * Get entities by metadata.entityKind
   * @see REQ-YL-QUERY-001
   */
  async getEntitiesByKind(kind: string): Promise<Entity[]> {
    const db = this.db.getDb();
    const stmt = db.prepare(`
      SELECT * FROM entities 
      WHERE json_extract(metadata, '$.entityKind') = ?
      ORDER BY created_at DESC
    `);
    const rows = stmt.all(kind) as Array<{
      id: string;
      type: EntityType;
      name: string;
      namespace: string;
      file_path: string | null;
      line: number | null;
      description: string | null;
      metadata: string;
      created_at: string;
      updated_at: string;
    }>;
    return rows.map(row => ({
      id: row.id,
      type: row.type,
      name: row.name,
      namespace: row.namespace,
      filePath: row.file_path ?? undefined,
      line: row.line ?? undefined,
      description: row.description ?? undefined,
      metadata: JSON.parse(row.metadata),
      createdAt: new Date(row.created_at),
      updatedAt: new Date(row.updated_at),
    }));
  }

  /**
   * Get entity by name (first match)
   */
  async getEntityByName(name: string, namespace?: string): Promise<Entity | null> {
    const filters: { name: string; namespace?: string } = { name };
    if (namespace) filters.namespace = namespace;
    const result = this.db.queryEntities(filters, 1, 0);
    return result.entities[0] ?? null;
  }

  /**
   * Upsert entity (add or update)
   * @see REQ-YL-UPDATE-001
   */
  async upsertEntity(
    entity: Omit<Entity, 'id' | 'createdAt' | 'updatedAt'>,
    matchBy: 'name' | 'name-namespace' = 'name-namespace'
  ): Promise<{ id: string; created: boolean }> {
    const existing = await this.getEntityByName(
      entity.name,
      matchBy === 'name-namespace' ? entity.namespace : undefined
    );

    if (existing) {
      // Update existing
      await this.updateEntity(existing.id, {
        type: entity.type,
        filePath: entity.filePath,
        line: entity.line,
        description: entity.description,
        metadata: { ...existing.metadata, ...entity.metadata },
      });
      return { id: existing.id, created: false };
    } else {
      // Create new
      const id = await this.addEntity(entity);
      return { id, created: true };
    }
  }

  /**
   * Upsert multiple entities in transaction
   */
  async upsertEntities(
    entities: Array<Omit<Entity, 'id' | 'createdAt' | 'updatedAt'>>,
    matchBy: 'name' | 'name-namespace' = 'name-namespace'
  ): Promise<{ created: number; updated: number }> {
    let created = 0;
    let updated = 0;
    for (const entity of entities) {
      const result = await this.upsertEntity(entity, matchBy);
      if (result.created) created++;
      else updated++;
    }
    return { created, updated };
  }

  /**
   * Execute raw SQL query (for advanced use cases)
   */
  async rawQuery<T = unknown>(sql: string, params: unknown[] = []): Promise<T[]> {
    const db = this.db.getDb();
    const stmt = db.prepare(sql);
    return stmt.all(...params) as T[];
  }

  // Relationship Operations

  /**
   * Add relationship
   */
  async addRelationship(
    sourceId: string,
    targetId: string,
    type: RelationType,
    metadata?: Record<string, unknown>
  ): Promise<string> {
    const id = randomUUID();

    const rel: Relationship = {
      id,
      sourceId,
      targetId,
      type,
      weight: 1.0,
      metadata: metadata ?? {},
      createdAt: new Date(),
    };

    this.db.insertRelationship(rel);
    return id;
  }

  /**
   * Get relationships for entity
   */
  async getRelationships(
    entityId: string,
    direction?: 'in' | 'out' | 'both'
  ): Promise<Relationship[]> {
    return this.db.getRelationships(entityId, direction);
  }

  /**
   * Delete relationship
   */
  async deleteRelationship(id: string): Promise<void> {
    this.db.deleteRelationship(id);
  }

  // Query Operations

  /**
   * Execute graph query
   * @see REQ-YL-QUERY-001
   */
  async query(query: GraphQuery, options?: QueryOptions): Promise<QueryResult> {
    return this.queryEngine.query(query, options);
  }

  /**
   * Find path between entities
   * @see REQ-YL-QUERY-002
   */
  async findPath(
    startId: string,
    endId: string,
    options?: {
      maxDepth?: number;
      relationshipTypes?: RelationType[];
      direction?: 'forward' | 'backward' | 'both';
    }
  ): Promise<Path | null> {
    return this.queryEngine.findPath(startId, endId, options);
  }

  /**
   * Extract subgraph around entity
   * @see REQ-YL-QUERY-003
   */
  async extractSubgraph(
    rootId: string,
    options?: {
      depth?: number;
      entityTypes?: EntityType[];
      relationshipTypes?: RelationType[];
      direction?: 'in' | 'out' | 'both';
    }
  ): Promise<Subgraph> {
    return this.queryEngine.extractSubgraph(rootId, options);
  }

  /**
   * Match pattern in graph
   * @see REQ-YL-QUERY-004
   */
  async matchPattern(pattern: GraphPattern): Promise<PatternMatch[]> {
    return this.queryEngine.matchPattern(pattern);
  }

  /**
   * Full-text search
   * @see REQ-YL-QUERY-005
   */
  async search(text: string, limit?: number): Promise<Entity[]> {
    return this.db.searchEntities(text, limit);
  }

  /**
   * Traverse relationships
   */
  async traverse(
    startId: string,
    relationshipTypes: RelationType[],
    direction: 'forward' | 'backward',
    maxHops?: number
  ): Promise<Entity[]> {
    return this.queryEngine.traverse(startId, relationshipTypes, direction, maxHops);
  }

  /**
   * Get entity neighbors
   */
  async getNeighbors(
    entityId: string,
    options?: {
      direction?: 'in' | 'out' | 'both';
      relationshipTypes?: RelationType[];
      entityTypes?: EntityType[];
    }
  ): Promise<Array<{ entity: Entity; relationship: Relationship }>> {
    return this.queryEngine.getNeighbors(entityId, options);
  }

  // Reasoning Operations

  /**
   * Run inference
   * @see REQ-YL-REASON-001
   */
  async infer(options?: {
    rules?: string[];
    maxIterations?: number;
  }): Promise<InferenceResult> {
    return this.reasoningEngine.infer(options);
  }

  /**
   * Validate graph constraints
   * @see REQ-YL-REASON-003
   */
  async validate(options?: { constraints?: string[] }): Promise<ValidationResult> {
    return this.reasoningEngine.validate(options);
  }

  /**
   * Compute confidence score
   * @see REQ-YL-REASON-004
   */
  async computeConfidence(
    sourceId: string,
    targetId: string,
    relType: RelationType
  ): Promise<number> {
    return this.reasoningEngine.computeConfidence(sourceId, targetId, relType);
  }

  /**
   * Suggest relationships
   * @see REQ-YL-REASON-002
   */
  async suggestRelationships(
    entityId: string,
    options?: {
      maxSuggestions?: number;
      minConfidence?: number;
    }
  ): Promise<
    Array<{ targetId: string; type: RelationType; confidence: number; reason: string }>
  > {
    return this.reasoningEngine.suggestRelationships(entityId, options);
  }

  /**
   * Add custom inference rule
   */
  addInferenceRule(rule: InferenceRule): void {
    this.reasoningEngine.addRule(rule);
  }

  /**
   * Add custom constraint
   */
  addConstraint(constraint: Constraint): void {
    this.reasoningEngine.addConstraint(constraint);
  }

  /**
   * Get all inference rules
   */
  getInferenceRules(): InferenceRule[] {
    return this.reasoningEngine.getRules();
  }

  /**
   * Get all constraints
   */
  getConstraints(): Constraint[] {
    return this.reasoningEngine.getConstraints();
  }

  // Import/Export Operations

  /**
   * Export to JSON
   * @see REQ-YL-IO-001
   */
  async exportJson(filePath?: string): Promise<JsonExport> {
    return this.ioModule.exportToJson(filePath);
  }

  /**
   * Import from JSON
   * @see REQ-YL-IO-003
   */
  async importJson(
    input: string | JsonExport,
    options?: { merge?: boolean; dryRun?: boolean }
  ): Promise<MergeResult> {
    return this.ioModule.importFromJson(input, options);
  }

  /**
   * Export to RDF
   * @see REQ-YL-IO-001
   */
  async exportRdf(filePath?: string, options?: RdfExportOptions): Promise<string> {
    return this.ioModule.exportToRdf(filePath, options);
  }

  // ============================================================
  // Enhanced Export/Import API (v1.7.0)
  // @see REQ-YI-EXP-001, REQ-YI-EXP-002, REQ-YI-EXP-003
  // ============================================================

  /**
   * Unified export API supporting multiple formats (JSON, RDF, GraphML)
   * Performance target: 30 seconds for up to 100,000 entities
   *
   * @param options - Export options (format, namespace filter, output path)
   * @returns Export result with content or file path
   *
   * @see REQ-YI-EXP-001
   */
  async export(options: import('./io.js').ExportOptions): Promise<import('./io.js').ExportResult> {
    return this.ioModule.export(options);
  }

  /**
   * Unified import API supporting multiple formats
   *
   * @param input - File path or content string
   * @param options - Import options (format, merge strategy)
   * @returns Import result with statistics
   *
   * @see REQ-YI-EXP-002
   */
  async import(
    input: string,
    options: import('./io.js').ImportOptions
  ): Promise<import('./io.js').ImportResult> {
    return this.ioModule.import(input, options);
  }

  /**
   * Export incremental changes since a specific date
   *
   * @param since - Export changes since this date
   * @param options - Export options (format, output path)
   * @returns Export result with only changed entities
   *
   * @see REQ-YI-EXP-003
   */
  async exportIncremental(
    since: Date,
    options?: Omit<import('./io.js').ExportOptions, 'since'>
  ): Promise<import('./io.js').ExportResult> {
    return this.ioModule.exportIncremental(since, options);
  }

  /**
   * Compute delta between states
   * @see REQ-YL-IO-004
   */
  computeDelta(oldState: JsonExport, newState: JsonExport): Delta {
    return this.ioModule.computeDelta(oldState, newState);
  }

  /**
   * Apply delta
   * @see REQ-YL-IO-004
   */
  async applyDelta(
    delta: Delta,
    options?: { dryRun?: boolean }
  ): Promise<MergeResult> {
    return this.ioModule.applyDelta(delta, options);
  }

  /**
   * Get changes since timestamp
   * @see REQ-YL-UPDATE-005
   */
  async getChangesSince(since: Date): Promise<{
    entities: { added: Entity[]; updated: Entity[]; deleted: string[] };
    relationships: { added: Relationship[]; deleted: string[] };
  }> {
    return this.db.getChangesSince(since);
  }

  /**
   * Get graph statistics
   */
  async getStats(): Promise<GraphStats> {
    return this.db.getStats();
  }
}

/**
 * Factory function to create YataLocal instance
 */
export function createYataLocal(config?: Partial<DatabaseConfig>): YataLocal {
  return new YataLocal(config);
}

// Re-export types
export * from './types.js';
export { YataDatabase } from './database.js';
export { QueryEngine } from './query-engine.js';
export { ReasoningEngine, type InferenceResult } from './reasoning.js';
export {
  IoModule,
  type JsonExport,
  type RdfExportOptions,
  type EnhancedJsonExport,
  type ExportOptions,
  type ImportOptions,
  type ExportResult,
  type ImportResult,
} from './io.js';

// Auto-updater for MCP integration
export {
  KnowledgeGraphUpdater,
  createKnowledgeGraphUpdater,
  type ExtractedEntity,
  type ExtractedRelationship,
  type CodeAnalysisResult,
  type UpdateResult,
} from './auto-updater.js';

// YATA Bridge for MCP integration
export {
  YataBridge,
  createYataBridge,
  type YataBridgeConfig,
} from './yata-bridge.js';

// KGPR Module (v1.6.5 NEW!)
export {
  LocalKGPRManager,
  createLocalKGPRManager,
  LocalPrivacyFilter,
  createLocalPrivacyFilter,
  LocalDiffEngine,
  createLocalDiffEngine,
} from './kgpr/index.js';
export type {
  LocalKGPRInfo,
  LocalKGPRDiff,
  LocalKGPRReviewEntry,
  LocalEntityChange,
  LocalRelationshipChange,
  LocalDiffStats,
  CreateLocalKGPROptions,
  ListLocalKGPROptions,
  LocalPrivacyFilterConfig,
  KGSnapshot,
  DiffOptions,
} from './kgpr/types.js';

// Wake-Sleep Learning Module (v1.6.5 NEW!)
export {
  LocalWakeSleepCycle,
  createLocalWakeSleepCycle,
  LocalWakePhase,
  createLocalWakePhase,
  LocalSleepPhase,
  createLocalSleepPhase,
  LocalPatternCompressor,
  createLocalPatternCompressor,
  DEFAULT_WAKE_SLEEP_CONFIG,
} from './wake-sleep/index.js';
export type {
  LocalPatternCandidate,
  LocalPatternType,
  LocalPatternCluster,
  LocalConsolidatedPattern,
  WakeObserveOptions,
  WakeObserveResult,
  SleepClusterOptions,
  SleepClusterResult,
  CompressOptions,
  LocalLearningCycleResult,
  LocalLearningCycleMetadata,
  LearningCycleStatus,
  SimilarityMethod,
  WakeSleepConfig,
} from './wake-sleep/types.js';

// Index Optimizer Module (v1.7.0 NEW!)
// @see REQ-YI-IDX-001, REQ-YI-IDX-002, REQ-YI-IDX-003
export {
  IndexOptimizer,
  QUERY_LOG_SCHEMA,
} from './index-optimizer.js';
export type {
  IndexInfo,
  IndexRecommendation,
  QueryStats,
  IndexAnalysisResult,
  AnalysisOptions,
  CompositeIndexOptions,
} from './index-optimizer.js';

// Global Sync Module (v1.7.0 NEW!)
// @see REQ-YI-GLB-001, REQ-YI-GLB-002, REQ-YI-GLB-003
export {
  GlobalSyncManager,
  createGlobalSyncManager,
  DEFAULT_SYNC_CONFIG,
} from './sync.js';
export type {
  SyncConfig,
  SyncState,
  SyncStatus,
  SyncConflict,
  SyncResult,
  ChangeSet,
  SyncResponse,
} from './sync.js';
