/**
 * YATA Local KGPR Manager
 *
 * Manages Knowledge Graph Pull Requests in local storage
 *
 * @packageDocumentation
 * @module @nahisaho/yata-local/kgpr
 *
 * @see REQ-YL-EXT-KGPR-001
 */

import { randomUUID } from 'crypto';
import type { Entity, Relationship, EntityType, KGPRStatusLocal, PrivacyLevel, LocalKGPR } from '../types.js';
import type { YataDatabase } from '../database.js';
import type {
  LocalKGPRInfo,
  LocalKGPRDiff,
  LocalKGPRReviewEntry,
  CreateLocalKGPROptions,
  ListLocalKGPROptions,
  KGSnapshot,
} from './types.js';
import { LocalDiffEngine, createLocalDiffEngine } from './diff-engine.js';
import { createLocalPrivacyFilter } from './privacy-filter.js';

/**
 * KGPR Manager for local knowledge graphs
 *
 * @example
 * ```typescript
 * const manager = createLocalKGPRManager(db);
 *
 * // Create a KGPR
 * const kgpr = await manager.createKGPR({
 *   title: 'Add UserService patterns',
 *   description: 'Learned patterns from user authentication flow',
 *   namespace: 'app.services',
 *   privacyLevel: 'strict',
 * });
 *
 * // Preview diff
 * const diff = await manager.previewDiff(kgpr.id);
 *
 * // Submit for review
 * await manager.submitKGPR(kgpr.id);
 * ```
 */
export class LocalKGPRManager {
  private db: YataDatabase;
  private diffEngine: LocalDiffEngine;
  private snapshots: Map<string, KGSnapshot> = new Map();

  constructor(db: YataDatabase) {
    this.db = db;
    this.diffEngine = createLocalDiffEngine();
  }

  /**
   * Create a new KGPR
   *
   * @param options - Creation options
   * @returns Created KGPR info
   */
  async createKGPR(options: CreateLocalKGPROptions): Promise<LocalKGPRInfo> {
    const id = `KGPR-${Date.now()}-${randomUUID().substring(0, 8)}`;
    const now = new Date();

    // Get current entities and relationships
    const entities = await this.getEntities(options.namespace, options.entityTypes);
    const relationships = await this.getRelationships();

    // Generate diff from baseline (if provided) or full diff
    const baseline = options.baselineId ? this.snapshots.get(options.baselineId) ?? null : null;
    let diff = this.diffEngine.generateDiff(baseline, entities, relationships, {
      namespace: options.namespace,
      entityTypes: options.entityTypes,
    });

    // Apply privacy filter
    const privacyLevel: PrivacyLevel = options.privacyLevel || 'moderate';
    const privacyFilter = createLocalPrivacyFilter(privacyLevel);
    diff = privacyFilter.filterDiff(diff);

    const kgprInfo: LocalKGPRInfo = {
      id,
      title: options.title,
      description: options.description || '',
      status: 'draft',
      namespace: options.namespace || '*',
      diff,
      privacyLevel,
      entityTypes: options.entityTypes || [],
      reviews: [],
      createdAt: now,
      updatedAt: now,
    };

    // Save to database
    this.db.insertKGPR({
      id: kgprInfo.id,
      title: kgprInfo.title,
      description: kgprInfo.description,
      status: kgprInfo.status,
      author: options.author || 'local',
      namespace: kgprInfo.namespace,
      diffJson: JSON.stringify(kgprInfo.diff),
      privacyLevel: kgprInfo.privacyLevel,
      entityTypesJson: JSON.stringify(kgprInfo.entityTypes),
      createdAt: kgprInfo.createdAt.toISOString(),
      updatedAt: kgprInfo.updatedAt.toISOString(),
    });

    return kgprInfo;
  }

  /**
   * Get a KGPR by ID
   *
   * @param id - KGPR ID
   * @returns KGPR info or null if not found
   */
  async getKGPR(id: string): Promise<LocalKGPRInfo | null> {
    const kgpr = this.db.getKGPR(id);
    if (!kgpr) return null;

    const reviews = this.db.getKGPRReviews(id);

    return this.dbKGPRToInfo(kgpr, reviews);
  }

  /**
   * List KGPRs with filtering
   *
   * @param options - List options
   * @returns Array of KGPRs
   */
  async listKGPRs(options?: ListLocalKGPROptions): Promise<LocalKGPRInfo[]> {
    const kgprs = this.db.listKGPRs({
      status: Array.isArray(options?.status) ? options?.status[0] : options?.status,
      namespace: options?.namespace,
      limit: options?.limit,
      offset: options?.offset,
    });

    // Convert to LocalKGPRInfo format
    const results: LocalKGPRInfo[] = [];
    for (const kgpr of kgprs) {
      const reviews = this.db.getKGPRReviews(kgpr.id);
      results.push(this.dbKGPRToInfo(kgpr, reviews));
    }

    // Apply search filter if provided
    let filtered = results;
    if (options?.search) {
      const searchLower = options.search.toLowerCase();
      filtered = results.filter(
        (k) =>
          k.title.toLowerCase().includes(searchLower) ||
          k.description.toLowerCase().includes(searchLower)
      );
    }

    // Sort
    if (options?.sortBy) {
      const sortOrder = options.sortOrder === 'desc' ? -1 : 1;
      filtered.sort((a, b) => {
        switch (options.sortBy) {
          case 'created':
            return (a.createdAt.getTime() - b.createdAt.getTime()) * sortOrder;
          case 'updated':
            return (a.updatedAt.getTime() - b.updatedAt.getTime()) * sortOrder;
          case 'title':
            return a.title.localeCompare(b.title) * sortOrder;
          default:
            return 0;
        }
      });
    }

    return filtered;
  }

  /**
   * Preview diff for a KGPR (recalculate current state)
   *
   * @param id - KGPR ID
   * @returns Current diff
   */
  async previewDiff(id: string): Promise<LocalKGPRDiff | null> {
    const kgpr = await this.getKGPR(id);
    if (!kgpr) return null;

    // Get current state
    const entities = await this.getEntities(
      kgpr.namespace !== '*' ? kgpr.namespace : undefined,
      kgpr.entityTypes.length > 0 ? kgpr.entityTypes : undefined
    );
    const relationships = await this.getRelationships();

    // Generate fresh diff
    const diff = this.diffEngine.generateDiff(null, entities, relationships, {
      namespace: kgpr.namespace !== '*' ? kgpr.namespace : undefined,
      entityTypes: kgpr.entityTypes.length > 0 ? kgpr.entityTypes : undefined,
    });

    // Apply privacy filter
    const privacyFilter = createLocalPrivacyFilter(kgpr.privacyLevel);
    return privacyFilter.filterDiff(diff);
  }

  /**
   * Update KGPR status
   *
   * @param id - KGPR ID
   * @param status - New status
   */
  async updateStatus(id: string, status: KGPRStatusLocal): Promise<void> {
    this.db.updateKGPRStatus(id, status);
  }

  /**
   * Submit a KGPR for review
   *
   * @param id - KGPR ID
   */
  async submitKGPR(id: string): Promise<void> {
    const kgpr = await this.getKGPR(id);
    if (!kgpr) {
      throw new Error(`KGPR not found: ${id}`);
    }

    if (kgpr.status !== 'draft') {
      throw new Error(`Cannot submit KGPR in status: ${kgpr.status}`);
    }

    this.db.updateKGPRStatus(id, 'open');
  }

  /**
   * Add a review to a KGPR
   *
   * @param kgprId - KGPR ID
   * @param review - Review data
   */
  async addReview(
    kgprId: string,
    review: Omit<LocalKGPRReviewEntry, 'id' | 'kgprId' | 'createdAt'>
  ): Promise<LocalKGPRReviewEntry> {
    const kgpr = await this.getKGPR(kgprId);
    if (!kgpr) {
      throw new Error(`KGPR not found: ${kgprId}`);
    }

    const reviewEntry: LocalKGPRReviewEntry = {
      id: `REV-${Date.now()}-${randomUUID().substring(0, 8)}`,
      kgprId,
      reviewerId: review.reviewerId,
      status: review.status,
      comment: review.comment,
      createdAt: new Date(),
    };

    this.db.insertKGPRReview({
      id: reviewEntry.id,
      kgprId: reviewEntry.kgprId,
      reviewer: reviewEntry.reviewerId,
      action: reviewEntry.status,
      comment: reviewEntry.comment ?? null,
      createdAt: reviewEntry.createdAt.toISOString(),
    });

    // Update KGPR status based on review
    if (review.status === 'approved') {
      this.db.updateKGPRStatus(kgprId, 'approved');
    } else if (review.status === 'changes_requested') {
      this.db.updateKGPRStatus(kgprId, 'changes_requested');
    }

    return reviewEntry;
  }

  /**
   * Close a KGPR
   *
   * @param id - KGPR ID
   */
  async closeKGPR(id: string): Promise<void> {
    const kgpr = await this.getKGPR(id);
    if (!kgpr) {
      throw new Error(`KGPR not found: ${id}`);
    }

    this.db.updateKGPRStatus(id, 'merged');
  }

  /**
   * Create a snapshot of current KG state
   *
   * @param description - Snapshot description
   * @returns Snapshot ID
   */
  async createSnapshot(description?: string): Promise<string> {
    const entities = await this.getEntities();
    const relationships = await this.getRelationships();

    const snapshot = this.diffEngine.createSnapshot(
      entities,
      relationships,
      description
    );

    this.snapshots.set(snapshot.id, snapshot);
    return snapshot.id;
  }

  /**
   * Convert DB KGPR to LocalKGPRInfo
   */
  private dbKGPRToInfo(kgpr: LocalKGPR, reviews: Array<{ id: string; kgprId: string; reviewer: string; action: 'approve' | 'changes_requested' | 'commented'; comment?: string; createdAt: Date }>): LocalKGPRInfo {
    return {
      id: kgpr.id,
      title: kgpr.title,
      description: kgpr.description || '',
      status: kgpr.status,
      namespace: kgpr.namespace,
      diff: JSON.parse(kgpr.diffJson) as LocalKGPRDiff,
      privacyLevel: kgpr.privacyLevel,
      entityTypes: kgpr.entityTypesJson ? JSON.parse(kgpr.entityTypesJson) as EntityType[] : [],
      reviews: reviews.map(r => ({
        id: r.id,
        kgprId: r.kgprId,
        reviewerId: r.reviewer,
        status: r.action === 'approve' ? 'approved' : r.action,
        comment: r.comment,
        createdAt: r.createdAt,
      })),
      createdAt: kgpr.createdAt,
      updatedAt: kgpr.updatedAt,
      submittedAt: kgpr.submittedAt,
    };
  }

  /**
   * Get entities from the database
   */
  private async getEntities(
    namespace?: string,
    entityTypes?: EntityType[]
  ): Promise<Entity[]> {
    // Use query engine to get entities
    const db = this.db.getDb();
    if (!db) return [];

    let query = 'SELECT * FROM entities WHERE 1=1';
    const params: unknown[] = [];

    if (namespace) {
      query += ' AND namespace LIKE ?';
      params.push(`${namespace}%`);
    }

    if (entityTypes && entityTypes.length > 0) {
      query += ` AND type IN (${entityTypes.map(() => '?').join(',')})`;
      params.push(...entityTypes);
    }

    const rows = db.prepare(query).all(...params) as Array<{
      id: string;
      type: string;
      name: string;
      namespace: string;
      file_path: string | null;
      line: number | null;
      metadata: string | null;
      created_at: string;
      updated_at: string;
    }>;

    return rows.map((row) => ({
      id: row.id,
      type: row.type as EntityType,
      name: row.name,
      namespace: row.namespace,
      filePath: row.file_path || undefined,
      line: row.line || undefined,
      metadata: row.metadata ? JSON.parse(row.metadata) : undefined,
      createdAt: new Date(row.created_at),
      updatedAt: new Date(row.updated_at),
    }));
  }

  /**
   * Get relationships from the database
   */
  private async getRelationships(): Promise<Relationship[]> {
    const db = this.db.getDb();
    if (!db) return [];

    const rows = db.prepare('SELECT * FROM relationships').all() as Array<{
      id: string;
      type: string;
      source_id: string;
      target_id: string;
      weight: number;
      metadata: string | null;
      created_at: string;
    }>;

    return rows.map((row) => ({
      id: row.id,
      type: row.type as Relationship['type'],
      sourceId: row.source_id,
      targetId: row.target_id,
      weight: row.weight,
      metadata: row.metadata ? JSON.parse(row.metadata) : undefined,
      createdAt: new Date(row.created_at),
    }));
  }
}

/**
 * Create a new KGPR manager
 *
 * @param db - YataDatabase instance
 * @returns New KGPR manager
 */
export function createLocalKGPRManager(db: YataDatabase): LocalKGPRManager {
  return new LocalKGPRManager(db);
}
