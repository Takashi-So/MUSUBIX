/**
 * Knowledge Graph Pull Request (KGPR) - Manager
 *
 * Core logic for creating, managing, and merging KGPRs
 *
 * @packageDocumentation
 * @module @nahisaho/yata-global/kgpr
 *
 * @see REQ-KGPR-001
 */

import { EventEmitter } from 'events';
import type {
  KGPR,
  KGPRDiff,
  KGPRStatus,
  KGPRComment,
  KGPRReview,
  CreateKGPROptions,
  KGPRSubmitResult,
  ListKGPROptions,
  MergeKGPROptions,
  MergeKGPRResult,
  DuplicateWarning,
} from './types.js';
import {
  createPrivacyFilter,
} from './privacy-filter.js';
import type { ApiClient } from '../api-client.js';

/**
 * KGPR manager events
 */
export interface KGPRManagerEvents {
  'kgpr:created': { kgpr: KGPR };
  'kgpr:submitted': { kgprId: string };
  'kgpr:updated': { kgprId: string; status: KGPRStatus };
  'kgpr:merged': { kgprId: string };
  'kgpr:closed': { kgprId: string };
  'error': Error;
}

/**
 * Local knowledge graph interface (for reading from YATA Local)
 */
export interface LocalKnowledgeGraph {
  /** Query all entities */
  queryEntities(namespace?: string): Promise<Array<{
    id: string;
    name: string;
    type: string;
    namespace: string;
    filePath?: string;
    line?: number;
    metadata?: Record<string, unknown>;
  }>>;
  
  /** Query all relationships */
  queryRelationships(namespace?: string): Promise<Array<{
    id: string;
    sourceName: string;
    sourceNamespace: string;
    targetName: string;
    targetNamespace: string;
    type: string;
    metadata?: Record<string, unknown>;
  }>>;
  
  /** Get entities modified since timestamp */
  getModifiedSince?(since: Date): Promise<{
    entities: Array<{ entity: unknown; changeType: 'add' | 'update' | 'delete' }>;
    relationships: Array<{ relationship: unknown; changeType: 'add' | 'update' | 'delete' }>;
  }>;
}

/**
 * KGPR Manager
 */
export class KGPRManager extends EventEmitter {
  private apiClient: ApiClient | null;
  private localKG: LocalKnowledgeGraph | null = null;
  private drafts: Map<string, KGPR> = new Map();
  private userId: string;
  private userName: string;

  constructor(options: {
    apiClient?: ApiClient;
    userId?: string;
    userName?: string;
  } = {}) {
    super();
    this.apiClient = options.apiClient ?? null;
    this.userId = options.userId ?? 'local-user';
    this.userName = options.userName ?? 'Local User';
  }

  /**
   * Connect to local knowledge graph
   */
  connectLocalKG(localKG: LocalKnowledgeGraph): void {
    this.localKG = localKG;
  }

  /**
   * Generate unique KGPR ID
   */
  private generateId(): string {
    const timestamp = Date.now().toString(36);
    const random = Math.random().toString(36).substring(2, 8);
    return `KGPR-${timestamp}-${random}`;
  }

  /**
   * Create a new KGPR from local knowledge graph
   */
  async create(options: CreateKGPROptions): Promise<KGPR> {
    if (!this.localKG) {
      throw new Error('Local knowledge graph not connected');
    }

    const { title, description, sourceNamespace, labels, entityTypes, privacyLevel } = options;

    // Query local KG
    const entities = await this.localKG.queryEntities(sourceNamespace);
    const relationships = await this.localKG.queryRelationships(sourceNamespace);

    // Filter by entity types if specified
    const filteredEntities = entityTypes
      ? entities.filter((e) => entityTypes.includes(e.type))
      : entities;

    // Build diff (all as "add" for new KGPR)
    const diff: KGPRDiff = {
      entities: {
        added: filteredEntities.map((e) => ({
          changeType: 'add' as const,
          localId: e.id,
          name: e.name,
          entityType: e.type,
          namespace: e.namespace,
          filePath: e.filePath,
          line: e.line,
          metadata: e.metadata,
        })),
        updated: [],
        deleted: [],
      },
      relationships: {
        added: relationships.map((r) => ({
          changeType: 'add' as const,
          localId: r.id,
          sourceName: r.sourceName,
          sourceNamespace: r.sourceNamespace,
          targetName: r.targetName,
          targetNamespace: r.targetNamespace,
          relationshipType: r.type,
          metadata: r.metadata,
        })),
        updated: [],
        deleted: [],
      },
      stats: {
        entitiesAdded: filteredEntities.length,
        entitiesUpdated: 0,
        entitiesDeleted: 0,
        relationshipsAdded: relationships.length,
        relationshipsUpdated: 0,
        relationshipsDeleted: 0,
        totalChanges: filteredEntities.length + relationships.length,
      },
    };

    // Apply privacy filter
    const filter = createPrivacyFilter(privacyLevel ?? 'moderate');
    const filteredDiff = filter.filterDiff(diff);

    // Create KGPR
    const kgpr: KGPR = {
      id: this.generateId(),
      title,
      description: description ?? '',
      authorId: this.userId,
      authorName: this.userName,
      status: 'draft',
      sourceNamespace: sourceNamespace ?? 'default',
      diff: filteredDiff,
      labels: labels ?? [],
      reviews: [],
      comments: [],
      createdAt: new Date(),
      updatedAt: new Date(),
    };

    // Store as draft
    this.drafts.set(kgpr.id, kgpr);

    this.emit('kgpr:created', { kgpr });

    // Auto-submit if requested
    if (options.autoSubmit) {
      await this.submit(kgpr.id);
    }

    return kgpr;
  }

  /**
   * Get diff preview before creating KGPR
   */
  async previewDiff(options: {
    sourceNamespace?: string;
    entityTypes?: string[];
    privacyLevel?: 'strict' | 'moderate' | 'none';
  } = {}): Promise<KGPRDiff> {
    if (!this.localKG) {
      throw new Error('Local knowledge graph not connected');
    }

    const { sourceNamespace, entityTypes, privacyLevel } = options;

    // Query local KG
    const entities = await this.localKG.queryEntities(sourceNamespace);
    const relationships = await this.localKG.queryRelationships(sourceNamespace);

    // Filter by entity types if specified
    const filteredEntities = entityTypes
      ? entities.filter((e) => entityTypes.includes(e.type))
      : entities;

    // Build diff
    const diff: KGPRDiff = {
      entities: {
        added: filteredEntities.map((e) => ({
          changeType: 'add' as const,
          localId: e.id,
          name: e.name,
          entityType: e.type,
          namespace: e.namespace,
          filePath: e.filePath,
          line: e.line,
          metadata: e.metadata,
        })),
        updated: [],
        deleted: [],
      },
      relationships: {
        added: relationships.map((r) => ({
          changeType: 'add' as const,
          localId: r.id,
          sourceName: r.sourceName,
          sourceNamespace: r.sourceNamespace,
          targetName: r.targetName,
          targetNamespace: r.targetNamespace,
          relationshipType: r.type,
          metadata: r.metadata,
        })),
        updated: [],
        deleted: [],
      },
      stats: {
        entitiesAdded: filteredEntities.length,
        entitiesUpdated: 0,
        entitiesDeleted: 0,
        relationshipsAdded: relationships.length,
        relationshipsUpdated: 0,
        relationshipsDeleted: 0,
        totalChanges: filteredEntities.length + relationships.length,
      },
    };

    // Apply privacy filter
    const filter = createPrivacyFilter(privacyLevel ?? 'moderate');
    return filter.filterDiff(diff);
  }

  /**
   * Get a draft KGPR
   */
  getDraft(id: string): KGPR | undefined {
    return this.drafts.get(id);
  }

  /**
   * List all drafts
   */
  listDrafts(): KGPR[] {
    return Array.from(this.drafts.values());
  }

  /**
   * Update a draft KGPR
   */
  updateDraft(id: string, updates: Partial<Pick<KGPR, 'title' | 'description' | 'labels'>>): KGPR {
    const draft = this.drafts.get(id);
    if (!draft) {
      throw new Error(`Draft KGPR not found: ${id}`);
    }

    if (draft.status !== 'draft') {
      throw new Error(`Cannot update non-draft KGPR: ${id}`);
    }

    const updated: KGPR = {
      ...draft,
      ...updates,
      updatedAt: new Date(),
    };

    this.drafts.set(id, updated);
    return updated;
  }

  /**
   * Delete a draft KGPR
   */
  deleteDraft(id: string): boolean {
    return this.drafts.delete(id);
  }

  /**
   * Submit a KGPR to YATA Global
   */
  async submit(id: string): Promise<KGPRSubmitResult> {
    const draft = this.drafts.get(id);
    if (!draft) {
      return { success: false, error: `Draft KGPR not found: ${id}` };
    }

    if (!this.apiClient) {
      // Offline mode - just update status
      draft.status = 'open';
      draft.updatedAt = new Date();
      return {
        success: true,
        kgprId: id,
        kgprUrl: undefined,
        qualityScore: undefined,
        duplicateWarnings: [],
      };
    }

    try {
      // Submit to server
      const response = await this.apiClient.post<{
        id: string;
        url: string;
        qualityScore: number;
        duplicateWarnings: DuplicateWarning[];
      }>('/kgpr', {
        title: draft.title,
        description: draft.description,
        sourceNamespace: draft.sourceNamespace,
        diff: draft.diff,
        labels: draft.labels,
      });

      if (!response.success || !response.data) {
        return {
          success: false,
          error: response.error ?? 'Failed to submit KGPR',
        };
      }

      // Update draft with server response
      draft.id = response.data.id;
      draft.status = 'open';
      draft.qualityScore = response.data.qualityScore;
      draft.duplicateWarnings = response.data.duplicateWarnings;
      draft.updatedAt = new Date();

      // Remove from drafts (now on server)
      this.drafts.delete(id);

      this.emit('kgpr:submitted', { kgprId: response.data.id });

      return {
        success: true,
        kgprId: response.data.id,
        kgprUrl: response.data.url,
        qualityScore: response.data.qualityScore,
        duplicateWarnings: response.data.duplicateWarnings,
      };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Unknown error',
      };
    }
  }

  /**
   * List KGPRs from YATA Global
   */
  async list(options: ListKGPROptions = {}): Promise<{ kgprs: KGPR[]; total: number }> {
    if (!this.apiClient) {
      // Offline mode - return only local drafts
      const drafts = this.listDrafts();
      return { kgprs: drafts, total: drafts.length };
    }

    try {
      const params: Record<string, string | number> = {};
      if (options.status) {
        params.status = Array.isArray(options.status)
          ? options.status.join(',')
          : options.status;
      }
      if (options.authorId) params.authorId = options.authorId;
      if (options.labels) params.labels = options.labels.join(',');
      if (options.search) params.search = options.search;
      if (options.sortBy) params.sortBy = options.sortBy;
      if (options.sortOrder) params.sortOrder = options.sortOrder;
      if (options.limit) params.limit = options.limit;
      if (options.offset) params.offset = options.offset;

      const response = await this.apiClient.get<{ kgprs: KGPR[]; total: number }>(
        '/kgpr',
        params
      );

      if (!response.success || !response.data) {
        return { kgprs: [], total: 0 };
      }

      return response.data;
    } catch {
      return { kgprs: [], total: 0 };
    }
  }

  /**
   * Get a specific KGPR
   */
  async get(id: string): Promise<KGPR | null> {
    // Check drafts first
    const draft = this.drafts.get(id);
    if (draft) return draft;

    if (!this.apiClient) {
      return null;
    }

    try {
      const response = await this.apiClient.get<KGPR>(`/kgpr/${id}`);
      return response.success && response.data ? response.data : null;
    } catch {
      return null;
    }
  }

  /**
   * Add a comment to a KGPR
   */
  async addComment(
    kgprId: string,
    body: string,
    targetId?: string,
    targetType?: 'entity' | 'relationship'
  ): Promise<KGPRComment | null> {
    const comment: KGPRComment = {
      id: `comment-${Date.now()}`,
      authorId: this.userId,
      authorName: this.userName,
      body,
      targetId,
      targetType,
      createdAt: new Date(),
    };

    // Check if it's a local draft
    const draft = this.drafts.get(kgprId);
    if (draft) {
      draft.comments.push(comment);
      draft.updatedAt = new Date();
      return comment;
    }

    if (!this.apiClient) {
      return null;
    }

    try {
      const response = await this.apiClient.post<KGPRComment>(
        `/kgpr/${kgprId}/comments`,
        { body, targetId, targetType }
      );
      return response.success && response.data ? response.data : null;
    } catch {
      return null;
    }
  }

  /**
   * Submit a review for a KGPR
   */
  async submitReview(
    kgprId: string,
    status: 'approved' | 'changes_requested' | 'commented',
    body?: string
  ): Promise<KGPRReview | null> {
    if (!this.apiClient) {
      return null;
    }

    try {
      const response = await this.apiClient.post<KGPRReview>(
        `/kgpr/${kgprId}/reviews`,
        { status, body }
      );

      if (response.success && response.data) {
        this.emit('kgpr:updated', { kgprId, status: status === 'approved' ? 'approved' : 'changes_requested' });
        return response.data;
      }
      return null;
    } catch {
      return null;
    }
  }

  /**
   * Merge a KGPR into the global knowledge graph
   */
  async merge(kgprId: string, options: MergeKGPROptions = {}): Promise<MergeKGPRResult> {
    if (!this.apiClient) {
      return {
        success: false,
        entitiesMerged: 0,
        relationshipsMerged: 0,
        conflictsResolved: 0,
        skipped: 0,
        error: 'Not connected to YATA Global',
      };
    }

    try {
      const response = await this.apiClient.post<MergeKGPRResult>(
        `/kgpr/${kgprId}/merge`,
        options
      );

      if (response.success && response.data) {
        this.emit('kgpr:merged', { kgprId });
        return response.data;
      }

      return {
        success: false,
        entitiesMerged: 0,
        relationshipsMerged: 0,
        conflictsResolved: 0,
        skipped: 0,
        error: response.error ?? 'Merge failed',
      };
    } catch (error) {
      return {
        success: false,
        entitiesMerged: 0,
        relationshipsMerged: 0,
        conflictsResolved: 0,
        skipped: 0,
        error: error instanceof Error ? error.message : 'Unknown error',
      };
    }
  }

  /**
   * Close a KGPR without merging
   */
  async close(kgprId: string, reason?: string): Promise<boolean> {
    // Check if it's a local draft
    const draft = this.drafts.get(kgprId);
    if (draft) {
      draft.status = 'closed';
      draft.closedAt = new Date();
      draft.closedBy = this.userId;
      draft.updatedAt = new Date();
      this.emit('kgpr:closed', { kgprId });
      return true;
    }

    if (!this.apiClient) {
      return false;
    }

    try {
      const response = await this.apiClient.post(`/kgpr/${kgprId}/close`, { reason });
      if (response.success) {
        this.emit('kgpr:closed', { kgprId });
        return true;
      }
      return false;
    } catch {
      return false;
    }
  }
}

/**
 * Create KGPR manager instance
 */
export function createKGPRManager(options?: {
  apiClient?: ApiClient;
  userId?: string;
  userName?: string;
}): KGPRManager {
  return new KGPRManager(options);
}
