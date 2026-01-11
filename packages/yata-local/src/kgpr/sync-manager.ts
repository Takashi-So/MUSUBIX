/**
 * YATA Local → YATA Global Sync Manager
 *
 * Push KGPR from local to global server
 *
 * @packageDocumentation
 * @module @nahisaho/yata-local/kgpr
 *
 * @see REQ-YL-EXT-KGPR-002
 */

import type { LocalKGPRInfo } from './types.js';

/**
 * Global server configuration
 */
export interface GlobalServerConfig {
  /** Server endpoint URL */
  endpoint: string;
  /** API key for authentication */
  apiKey?: string;
  /** Request timeout in ms */
  timeout?: number;
}

/**
 * Push result
 */
export interface PushResult {
  success: boolean;
  globalId?: string;
  error?: string;
  message?: string;
}

/**
 * Entity change for global diff
 */
interface GlobalEntityChange {
  localId: string;
  name: string;
  entityType: string;
  namespace: string;
  filePath?: string;
  metadata?: Record<string, unknown>;
}

/**
 * Relationship change for global diff
 */
interface GlobalRelationshipChange {
  sourceName: string;
  sourceNamespace: string;
  targetName: string;
  targetNamespace: string;
  relationshipType: string;
  metadata?: Record<string, unknown>;
}

/**
 * Global KGPR format (matches YATA Global server API)
 */
interface GlobalKGPRPayload {
  title: string;
  description: string;
  sourceNamespace: string;
  labels?: string[];
  diff: {
    entities: {
      added: GlobalEntityChange[];
      updated: GlobalEntityChange[];
      deleted: GlobalEntityChange[];
    };
    relationships: {
      added: GlobalRelationshipChange[];
      updated: GlobalRelationshipChange[];
      deleted: GlobalRelationshipChange[];
    };
    stats: {
      entitiesAdded: number;
      entitiesUpdated: number;
      entitiesDeleted: number;
      relationshipsAdded: number;
      relationshipsUpdated: number;
      relationshipsDeleted: number;
      totalChanges: number;
    };
  };
}

/**
 * KGPR Sync Manager - Push local KGPRs to YATA Global
 *
 * @example
 * ```typescript
 * const syncManager = createKGPRSyncManager({
 *   endpoint: 'http://localhost:3000',
 * });
 *
 * // Push a KGPR to global
 * const result = await syncManager.push(localKgpr);
 * if (result.success) {
 *   console.log('Pushed as:', result.globalId);
 * }
 * ```
 */
export class KGPRSyncManager {
  private config: Required<GlobalServerConfig>;

  constructor(config: GlobalServerConfig) {
    this.config = {
      endpoint: config.endpoint.replace(/\/$/, ''),
      apiKey: config.apiKey || '',
      timeout: config.timeout || 30000,
    };
  }

  /**
   * Push a local KGPR to YATA Global
   *
   * @param kgpr - Local KGPR to push
   * @param options - Push options
   * @returns Push result with global ID
   */
  async push(
    kgpr: LocalKGPRInfo,
    options?: { projectId?: string }
  ): Promise<PushResult> {
    try {
      // Convert local KGPR diff to global format
      const payload = this.convertToGlobalFormat(kgpr, options?.projectId);

      const response = await this.makeRequest('/api/v1/kgprs', 'POST', payload);

      if (!response.ok) {
        const error = await response.json().catch(() => ({ error: 'Unknown error' }));
        return {
          success: false,
          error: (error as { error?: string }).error || `HTTP ${response.status}`,
        };
      }

      const result = await response.json() as { success: boolean; data?: { id: string }; id?: string; message?: string };
      const globalId = result.data?.id || result.id;
      return {
        success: true,
        globalId,
        message: result.message || 'KGPR pushed successfully',
      };
    } catch (err) {
      return {
        success: false,
        error: err instanceof Error ? err.message : 'Network error',
      };
    }
  }

  /**
   * Submit a pushed KGPR for review
   *
   * @param globalId - Global KGPR ID
   * @returns Submit result
   */
  async submit(globalId: string): Promise<PushResult> {
    try {
      const response = await this.makeRequest(
        `/api/v1/kgprs/${globalId}/submit`,
        'POST'
      );

      if (!response.ok) {
        const error = await response.json().catch(() => ({ error: 'Unknown error' }));
        return {
          success: false,
          error: (error as { error?: string }).error || `HTTP ${response.status}`,
        };
      }

      return {
        success: true,
        globalId,
        message: 'KGPR submitted for review',
      };
    } catch (err) {
      return {
        success: false,
        error: err instanceof Error ? err.message : 'Network error',
      };
    }
  }

  /**
   * Push and immediately submit for review
   *
   * @param kgpr - Local KGPR to push
   * @param options - Push options
   * @returns Push result
   */
  async pushAndSubmit(
    kgpr: LocalKGPRInfo,
    options?: { projectId?: string }
  ): Promise<PushResult> {
    const pushResult = await this.push(kgpr, options);
    if (!pushResult.success || !pushResult.globalId) {
      return pushResult;
    }

    const submitResult = await this.submit(pushResult.globalId);
    if (!submitResult.success) {
      return {
        success: false,
        globalId: pushResult.globalId,
        error: `Pushed but submit failed: ${submitResult.error}`,
      };
    }

    return {
      success: true,
      globalId: pushResult.globalId,
      message: 'KGPR pushed and submitted for review',
    };
  }

  /**
   * Get status of a KGPR on global server
   *
   * @param globalId - Global KGPR ID
   * @returns KGPR status or null
   */
  async getStatus(globalId: string): Promise<{ status: string; updatedAt: string } | null> {
    try {
      const response = await this.makeRequest(`/api/v1/kgprs/${globalId}`, 'GET');

      if (!response.ok) {
        return null;
      }

      const result = await response.json() as { success: boolean; data?: { status: string; updatedAt: string }; status?: string; updatedAt?: string };
      const kgpr = result.data || result;
      return { status: kgpr.status || 'unknown', updatedAt: kgpr.updatedAt || '' };
    } catch {
      return null;
    }
  }

  /**
   * List KGPRs on global server
   *
   * @param options - Filter options
   * @returns List of KGPRs
   */
  async list(options?: { status?: string; projectId?: string }): Promise<Array<{ id: string; title: string; status: string }>> {
    try {
      let path = '/api/v1/kgprs';
      const params: string[] = [];
      if (options?.status) params.push(`status=${options.status}`);
      if (options?.projectId) params.push(`projectId=${options.projectId}`);
      if (params.length > 0) path += '?' + params.join('&');

      const response = await this.makeRequest(path, 'GET');

      if (!response.ok) {
        return [];
      }

      const result = await response.json() as { success: boolean; data?: { items: Array<{ id: string; title: string; status: string }> }; kgprs?: Array<{ id: string; title: string; status: string }> };
      return result.data?.items || result.kgprs || [];
    } catch {
      return [];
    }
  }

  /**
   * Check connection to global server
   */
  async checkConnection(): Promise<{ connected: boolean; version?: string }> {
    try {
      const response = await this.makeRequest('/health', 'GET');
      if (!response.ok) {
        return { connected: false };
      }
      const data = await response.json() as { version?: string };
      return { connected: true, version: data.version };
    } catch {
      return { connected: false };
    }
  }

  /**
   * Convert local KGPR diff to global format
   */
  private convertToGlobalFormat(kgpr: LocalKGPRInfo, _projectId?: string): GlobalKGPRPayload {
    const localDiff = kgpr.diff;

    // Convert entities to global format
    const entitiesAdded = localDiff.entities.added.map((e) => ({
      localId: e.localId,
      name: e.name,
      entityType: e.entityType,
      namespace: e.namespace,
      filePath: e.filePath,
      metadata: e.metadata,
    }));

    const entitiesUpdated = localDiff.entities.updated.map((e) => ({
      localId: e.localId,
      name: e.name,
      entityType: e.entityType,
      namespace: e.namespace,
      filePath: e.filePath,
      metadata: e.metadata,
    }));

    const entitiesDeleted = localDiff.entities.deleted.map((e) => ({
      localId: e.localId,
      name: e.name,
      entityType: e.entityType,
      namespace: e.namespace,
      filePath: e.filePath,
      metadata: e.metadata,
    }));

    // Convert relationships to global format
    const relationshipsAdded = localDiff.relationships.added.map((r) => ({
      sourceName: r.sourceName,
      sourceNamespace: r.sourceNamespace,
      targetName: r.targetName,
      targetNamespace: r.targetNamespace,
      relationshipType: r.relationshipType,
      metadata: r.metadata,
    }));

    const relationshipsUpdated = localDiff.relationships.updated.map((r) => ({
      sourceName: r.sourceName,
      sourceNamespace: r.sourceNamespace,
      targetName: r.targetName,
      targetNamespace: r.targetNamespace,
      relationshipType: r.relationshipType,
      metadata: r.metadata,
    }));

    const relationshipsDeleted = localDiff.relationships.deleted.map((r) => ({
      sourceName: r.sourceName,
      sourceNamespace: r.sourceNamespace,
      targetName: r.targetName,
      targetNamespace: r.targetNamespace,
      relationshipType: r.relationshipType,
      metadata: r.metadata,
    }));

    // Calculate stats
    const stats = {
      entitiesAdded: entitiesAdded.length,
      entitiesUpdated: entitiesUpdated.length,
      entitiesDeleted: entitiesDeleted.length,
      relationshipsAdded: relationshipsAdded.length,
      relationshipsUpdated: relationshipsUpdated.length,
      relationshipsDeleted: relationshipsDeleted.length,
      totalChanges:
        entitiesAdded.length +
        entitiesUpdated.length +
        entitiesDeleted.length +
        relationshipsAdded.length +
        relationshipsUpdated.length +
        relationshipsDeleted.length,
    };

    return {
      title: kgpr.title,
      description: kgpr.description,
      sourceNamespace: kgpr.namespace !== '*' ? kgpr.namespace : 'default',
      diff: {
        entities: {
          added: entitiesAdded,
          updated: entitiesUpdated,
          deleted: entitiesDeleted,
        },
        relationships: {
          added: relationshipsAdded,
          updated: relationshipsUpdated,
          deleted: relationshipsDeleted,
        },
        stats,
      },
    };
  }

  /**
   * Make HTTP request to global server
   */
  private async makeRequest(
    path: string,
    method: 'GET' | 'POST' | 'PUT' | 'DELETE',
    body?: unknown
  ): Promise<Response> {
    const url = `${this.config.endpoint}${path}`;
    const headers: Record<string, string> = {
      'Content-Type': 'application/json',
      'Accept': 'application/json',
    };

    if (this.config.apiKey) {
      headers['X-API-Key'] = this.config.apiKey;
    }

    const controller = new AbortController();
    const timeoutId = setTimeout(() => controller.abort(), this.config.timeout);

    try {
      return await fetch(url, {
        method,
        headers,
        body: body ? JSON.stringify(body) : undefined,
        signal: controller.signal,
      });
    } finally {
      clearTimeout(timeoutId);
    }
  }
}

/**
 * Create a new KGPR sync manager
 *
 * @param config - Global server configuration
 * @returns New sync manager
 */
export function createKGPRSyncManager(config: GlobalServerConfig): KGPRSyncManager {
  return new KGPRSyncManager(config);
}
