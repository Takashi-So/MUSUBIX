/**
 * YATA Global Sync Manager
 *
 * Manages synchronization between YATA Local and YATA Global.
 *
 * @packageDocumentation
 * @module @nahisaho/yata-local/sync
 *
 * @see REQ-YI-GLB-001 - Global Synchronization
 * @see REQ-YI-GLB-002 - Sync State Management
 * @see REQ-YI-GLB-003 - Conflict Resolution
 * @see DES-YATA-IMPROVEMENTS-001 - Design Document
 */

import type { Entity, Relationship } from './types.js';
import type { YataDatabase } from './database.js';

// ============================================================
// Types
// ============================================================

/**
 * Synchronization configuration
 */
export interface SyncConfig {
  /** YATA Global endpoint URL */
  globalEndpoint: string;
  /** Authentication token (optional) */
  authToken?: string;
  /** Namespace to sync */
  namespace: string;
  /** Sync direction */
  syncDirection: 'push' | 'pull' | 'bidirectional';
  /** Conflict resolution strategy */
  conflictStrategy: 'local-wins' | 'remote-wins' | 'manual';
  /** Request timeout in milliseconds */
  timeoutMs?: number;
  /** Batch size for sync operations */
  batchSize?: number;
}

/**
 * Sync state
 */
export type SyncState = 'idle' | 'preparing' | 'uploading' | 'downloading' | 'conflict' | 'finalizing' | 'error';

/**
 * Sync status
 */
export interface SyncStatus {
  /** Current sync state */
  state: SyncState;
  /** Progress percentage (0-100) */
  progress: number;
  /** Last successful sync timestamp */
  lastSyncAt?: Date;
  /** Number of pending local changes */
  pendingChanges: number;
  /** Active conflicts */
  conflicts: SyncConflict[];
  /** Error message if in error state */
  errorMessage?: string;
}

/**
 * Sync conflict
 */
export interface SyncConflict {
  /** Entity ID */
  entityId: string;
  /** Local version */
  localVersion: Entity;
  /** Remote version */
  remoteVersion: Entity;
  /** Conflict type */
  conflictType: 'update-update' | 'delete-update' | 'create-create';
  /** Resolution status */
  resolved: boolean;
  /** Chosen resolution */
  resolution?: 'local' | 'remote' | 'merged';
}

/**
 * Sync result
 */
export interface SyncResult {
  /** Whether sync completed successfully */
  success: boolean;
  /** Number of entities uploaded */
  uploaded: number;
  /** Number of entities downloaded */
  downloaded: number;
  /** Conflicts encountered */
  conflicts: SyncConflict[];
  /** Conflicts auto-resolved */
  conflictsResolved: number;
  /** Sync duration in milliseconds */
  syncTimeMs: number;
  /** Error message if failed */
  errorMessage?: string;
}

/**
 * Change set for sync
 */
export interface ChangeSet {
  /** New or modified entities */
  entities: Entity[];
  /** New or modified relationships */
  relationships: Relationship[];
  /** Deleted entity IDs */
  deletedEntityIds: string[];
  /** Deleted relationship IDs */
  deletedRelationshipIds: string[];
  /** Last sync ID for continuation */
  lastSyncId?: string;
}

/**
 * Sync response from Global
 */
export interface SyncResponse {
  /** Changes from remote */
  changes: ChangeSet;
  /** Detected conflicts */
  conflicts: SyncConflict[];
  /** New sync ID */
  syncId: string;
  /** Server timestamp */
  serverTimestamp: string;
}

/**
 * Default sync configuration
 */
export const DEFAULT_SYNC_CONFIG: Partial<SyncConfig> = {
  syncDirection: 'bidirectional',
  conflictStrategy: 'local-wins',
  timeoutMs: 60000,
  batchSize: 100,
};

// ============================================================
// GlobalSyncManager Class
// ============================================================

/**
 * Manages synchronization with YATA Global
 *
 * @example
 * ```typescript
 * const syncManager = new GlobalSyncManager(db, {
 *   globalEndpoint: 'https://yata.global/api',
 *   namespace: 'my-project',
 *   syncDirection: 'bidirectional',
 *   conflictStrategy: 'local-wins',
 * });
 *
 * const result = await syncManager.sync();
 * console.log(`Uploaded: ${result.uploaded}, Downloaded: ${result.downloaded}`);
 * ```
 *
 * @see REQ-YI-GLB-001
 * @see REQ-YI-GLB-002
 * @see REQ-YI-GLB-003
 */
export class GlobalSyncManager {
  private db: YataDatabase;
  private config: SyncConfig;
  private status: SyncStatus;
  private lastSyncId?: string;

  constructor(db: YataDatabase, config: SyncConfig) {
    this.db = db;
    this.config = { ...DEFAULT_SYNC_CONFIG, ...config } as SyncConfig;
    this.status = {
      state: 'idle',
      progress: 0,
      pendingChanges: 0,
      conflicts: [],
    };
  }

  // ============================================================
  // Public API
  // ============================================================

  /**
   * Get current sync status
   * @see REQ-YI-GLB-002
   */
  getStatus(): SyncStatus {
    return { ...this.status };
  }

  /**
   * Perform full synchronization
   * Performance target: 60 seconds for up to 1,000 changed entities
   *
   * @returns Sync result
   * @see REQ-YI-GLB-001
   */
  async sync(): Promise<SyncResult> {
    const startTime = Date.now();
    const result: SyncResult = {
      success: false,
      uploaded: 0,
      downloaded: 0,
      conflicts: [],
      conflictsResolved: 0,
      syncTimeMs: 0,
    };

    try {
      // Phase 1: Preparing
      this.updateStatus('preparing', 0);
      const localChanges = await this.getLocalChanges();
      this.status.pendingChanges = localChanges.entities.length + localChanges.deletedEntityIds.length;

      // Phase 2: Upload local changes
      if (this.config.syncDirection !== 'pull') {
        this.updateStatus('uploading', 20);
        const uploadResult = await this.uploadChanges(localChanges);
        result.uploaded = uploadResult.uploaded;
        result.conflicts.push(...uploadResult.conflicts);
      }

      // Phase 3: Download remote changes
      if (this.config.syncDirection !== 'push') {
        this.updateStatus('downloading', 50);
        const downloadResult = await this.downloadChanges();
        result.downloaded = downloadResult.downloaded;
        result.conflicts.push(...downloadResult.conflicts);
      }

      // Phase 4: Resolve conflicts
      if (result.conflicts.length > 0) {
        this.updateStatus('conflict', 70);
        const resolved = await this.resolveConflicts(result.conflicts);
        result.conflictsResolved = resolved;
      }

      // Phase 5: Finalize
      this.updateStatus('finalizing', 90);
      await this.finalize();

      result.success = true;
      this.status.lastSyncAt = new Date();
      this.updateStatus('idle', 100);

    } catch (error) {
      result.success = false;
      result.errorMessage = error instanceof Error ? error.message : String(error);
      this.status.errorMessage = result.errorMessage;
      this.updateStatus('error', 0);
    }

    result.syncTimeMs = Date.now() - startTime;
    return result;
  }

  /**
   * Push local changes to Global
   * @see REQ-YI-GLB-001
   */
  async push(): Promise<SyncResult> {
    const originalDirection = this.config.syncDirection;
    this.config.syncDirection = 'push';
    try {
      return await this.sync();
    } finally {
      this.config.syncDirection = originalDirection;
    }
  }

  /**
   * Pull remote changes from Global
   * @see REQ-YI-GLB-001
   */
  async pull(): Promise<SyncResult> {
    const originalDirection = this.config.syncDirection;
    this.config.syncDirection = 'pull';
    try {
      return await this.sync();
    } finally {
      this.config.syncDirection = originalDirection;
    }
  }

  /**
   * Manually resolve a conflict
   * @see REQ-YI-GLB-003
   */
  async resolveConflict(
    entityId: string,
    resolution: 'local' | 'remote' | 'merged',
    mergedEntity?: Entity
  ): Promise<boolean> {
    const conflict = this.status.conflicts.find(c => c.entityId === entityId);
    if (!conflict) {
      return false;
    }

    switch (resolution) {
      case 'local':
        // Keep local version - no action needed
        conflict.resolution = 'local';
        break;
      case 'remote':
        // Apply remote version
        this.db.updateEntity(entityId, conflict.remoteVersion);
        conflict.resolution = 'remote';
        break;
      case 'merged':
        if (!mergedEntity) {
          throw new Error('Merged entity required for merge resolution');
        }
        this.db.updateEntity(entityId, mergedEntity);
        conflict.resolution = 'merged';
        break;
    }

    conflict.resolved = true;
    return true;
  }

  /**
   * Reset sync state
   */
  reset(): void {
    this.status = {
      state: 'idle',
      progress: 0,
      pendingChanges: 0,
      conflicts: [],
    };
    this.lastSyncId = undefined;
  }

  // ============================================================
  // Internal Methods
  // ============================================================

  /**
   * Update sync status
   */
  private updateStatus(state: SyncState, progress: number): void {
    this.status.state = state;
    this.status.progress = progress;
  }

  /**
   * Get local changes since last sync
   */
  private async getLocalChanges(): Promise<ChangeSet> {
    const since = this.status.lastSyncAt ?? new Date(0);
    const changes = this.db.getChangesSince(since);

    return {
      entities: [...changes.entities.added, ...changes.entities.updated],
      relationships: [...changes.relationships.added],
      deletedEntityIds: changes.entities.deleted,
      deletedRelationshipIds: changes.relationships.deleted,
      lastSyncId: this.lastSyncId,
    };
  }

  /**
   * Upload changes to Global
   */
  private async uploadChanges(
    changes: ChangeSet
  ): Promise<{ uploaded: number; conflicts: SyncConflict[] }> {
    // In a real implementation, this would make HTTP requests to YATA Global
    // For now, we simulate the behavior
    
    const result = {
      uploaded: 0,
      conflicts: [] as SyncConflict[],
    };

    // Simulate batched upload
    const batchSize = this.config.batchSize ?? 100;
    for (let i = 0; i < changes.entities.length; i += batchSize) {
      const batch = changes.entities.slice(i, i + batchSize);
      
      try {
        // Simulated API call
        const response = await this.simulateGlobalApiCall('push', {
          entities: batch,
          namespace: this.config.namespace,
        });

        result.uploaded += batch.length;
        
        if (response.conflicts) {
          result.conflicts.push(...response.conflicts);
        }
      } catch (error) {
        throw new Error(`Failed to upload batch: ${error instanceof Error ? error.message : String(error)}`);
      }

      // Update progress
      const progress = 20 + (30 * (i + batch.length) / changes.entities.length);
      this.updateStatus('uploading', progress);
    }

    return result;
  }

  /**
   * Download changes from Global
   */
  private async downloadChanges(): Promise<{ downloaded: number; conflicts: SyncConflict[] }> {
    const result = {
      downloaded: 0,
      conflicts: [] as SyncConflict[],
    };

    try {
      // Simulated API call to get remote changes
      const response = await this.simulateGlobalApiCall('pull', {
        namespace: this.config.namespace,
        since: this.lastSyncId,
      });

      // Apply remote changes
      for (const entity of response.changes?.entities ?? []) {
        const local = this.db.getEntity(entity.id);
        
        if (local) {
          // Potential conflict
          if (this.hasConflict(local, entity)) {
            result.conflicts.push({
              entityId: entity.id,
              localVersion: local,
              remoteVersion: entity,
              conflictType: 'update-update',
              resolved: false,
            });
          } else {
            this.db.updateEntity(entity.id, entity);
            result.downloaded++;
          }
        } else {
          this.db.insertEntity(entity);
          result.downloaded++;
        }
      }

      // Handle deleted entities
      for (const entityId of response.changes?.deletedEntityIds ?? []) {
        const local = this.db.getEntity(entityId);
        if (local) {
          // Check if local was modified after remote deletion
          const localChanges = this.db.getChangesSince(this.status.lastSyncAt ?? new Date(0));
          const wasModified = localChanges.entities.updated.some(e => e.id === entityId);
          
          if (wasModified) {
            result.conflicts.push({
              entityId,
              localVersion: local,
              remoteVersion: { ...local, id: entityId } as Entity, // Marker for deleted
              conflictType: 'delete-update',
              resolved: false,
            });
          } else {
            this.db.deleteEntity(entityId);
            result.downloaded++;
          }
        }
      }

      // Update sync ID
      if (response.syncId) {
        this.lastSyncId = response.syncId;
      }

    } catch (error) {
      throw new Error(`Failed to download changes: ${error instanceof Error ? error.message : String(error)}`);
    }

    return result;
  }

  /**
   * Check if there's a conflict between local and remote versions
   */
  private hasConflict(local: Entity, remote: Entity): boolean {
    // Simple conflict detection: both modified after last sync
    const lastSync = this.status.lastSyncAt ?? new Date(0);
    return local.updatedAt > lastSync && remote.updatedAt > lastSync;
  }

  /**
   * Auto-resolve conflicts based on strategy
   * @see REQ-YI-GLB-003
   */
  private async resolveConflicts(conflicts: SyncConflict[]): Promise<number> {
    let resolved = 0;

    for (const conflict of conflicts) {
      if (this.config.conflictStrategy === 'manual') {
        // Skip - wait for manual resolution
        continue;
      }

      const resolution = this.config.conflictStrategy === 'local-wins' ? 'local' : 'remote';
      
      if (resolution === 'remote') {
        this.db.updateEntity(conflict.entityId, conflict.remoteVersion);
      }
      // local-wins: keep local, no action needed

      conflict.resolved = true;
      conflict.resolution = resolution;
      resolved++;
    }

    // Update status conflicts (only unresolved)
    this.status.conflicts = conflicts.filter(c => !c.resolved);

    return resolved;
  }

  /**
   * Finalize sync
   */
  private async finalize(): Promise<void> {
    // Commit any pending changes
    // In a real implementation, this might involve committing a transaction
    // or updating sync metadata

    // Clear pending changes count
    this.status.pendingChanges = 0;
  }

  /**
   * Simulate YATA Global API call
   * This is a placeholder for actual HTTP requests
   */
  private async simulateGlobalApiCall(
    _operation: 'push' | 'pull',
    _payload: object
  ): Promise<SyncResponse> {
    // Simulate network delay
    await new Promise(resolve => setTimeout(resolve, 10));

    // In production, this would be:
    // const response = await fetch(`${this.config.globalEndpoint}/sync/${operation}`, {
    //   method: 'POST',
    //   headers: {
    //     'Content-Type': 'application/json',
    //     'Authorization': `Bearer ${this.config.authToken}`,
    //   },
    //   body: JSON.stringify(payload),
    // });

    return {
      changes: {
        entities: [],
        relationships: [],
        deletedEntityIds: [],
        deletedRelationshipIds: [],
      },
      conflicts: [],
      syncId: `sync-${Date.now()}`,
      serverTimestamp: new Date().toISOString(),
    };
  }
}

/**
 * Factory function to create GlobalSyncManager
 */
export function createGlobalSyncManager(
  db: YataDatabase,
  config: SyncConfig
): GlobalSyncManager {
  return new GlobalSyncManager(db, config);
}
