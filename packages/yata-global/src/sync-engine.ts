/**
 * YATA Global - Sync Engine
 *
 * Handles synchronization between local cache and YATA Global server
 *
 * @packageDocumentation
 * @module @nahisaho/yata-global
 *
 * @see REQ-YG-SYNC-001
 */

import { EventEmitter } from 'events';
import type {
  FrameworkKnowledge,
  SharedPattern,
  SyncConfig,
  SyncResult,
  SyncStatus,
} from './types.js';
import { ApiClient } from './api-client.js';
import { CacheManager } from './cache-manager.js';

/**
 * Sync delta from server
 */
interface SyncDelta {
  frameworks: {
    added: FrameworkKnowledge[];
    updated: FrameworkKnowledge[];
    deleted: string[];
  };
  patterns: {
    added: SharedPattern[];
    updated: SharedPattern[];
    deleted: string[];
  };
  serverTime: number;
}

/**
 * Pending local changes
 */
interface PendingChanges {
  patterns: {
    create: Omit<SharedPattern, 'id' | 'authorId' | 'rating' | 'downloads' | 'createdAt' | 'updatedAt'>[];
    update: { id: string; updates: Partial<SharedPattern> }[];
    delete: string[];
  };
  ratings: { patternId: string; rating: 1 | 2 | 3 | 4 | 5 }[];
}

/**
 * Sync engine events
 */
export interface SyncEngineEvents {
  'sync:start': void;
  'sync:progress': { phase: string; progress: number };
  'sync:complete': SyncResult;
  'sync:error': Error;
  'conflict': { type: 'framework' | 'pattern'; id: string };
}

/**
 * Sync engine for YATA Global
 */
export class SyncEngine extends EventEmitter {
  private apiClient: ApiClient;
  private cacheManager: CacheManager;
  private config: SyncConfig;
  private syncInProgress: boolean = false;
  private lastError: string | null = null;
  private pendingChanges: PendingChanges = {
    patterns: { create: [], update: [], delete: [] },
    ratings: [],
  };
  private syncTimer: NodeJS.Timeout | null = null;

  constructor(apiClient: ApiClient, cacheManager: CacheManager, config: SyncConfig) {
    super();
    this.apiClient = apiClient;
    this.cacheManager = cacheManager;
    this.config = config;
  }

  /**
   * Get current sync status
   */
  getStatus(): SyncStatus {
    return {
      lastSync: this.cacheManager.getLastSyncTime(),
      inProgress: this.syncInProgress,
      pendingChanges: this.countPendingChanges(),
      lastError: this.lastError ?? undefined,
      connected: !this.config.offlineMode,
    };
  }

  /**
   * Count pending changes
   */
  private countPendingChanges(): number {
    return (
      this.pendingChanges.patterns.create.length +
      this.pendingChanges.patterns.update.length +
      this.pendingChanges.patterns.delete.length +
      this.pendingChanges.ratings.length
    );
  }

  /**
   * Start automatic sync
   */
  startAutoSync(): void {
    if (this.syncTimer) return;

    this.syncTimer = setInterval(() => {
      if (!this.syncInProgress && !this.config.offlineMode) {
        this.sync().catch(err => {
          this.emit('sync:error', err);
        });
      }
    }, this.config.syncInterval * 1000);
  }

  /**
   * Stop automatic sync
   */
  stopAutoSync(): void {
    if (this.syncTimer) {
      clearInterval(this.syncTimer);
      this.syncTimer = null;
    }
  }

  /**
   * Queue pattern for creation
   */
  queuePatternCreate(pattern: Omit<SharedPattern, 'id' | 'authorId' | 'rating' | 'downloads' | 'createdAt' | 'updatedAt'>): void {
    this.pendingChanges.patterns.create.push(pattern);
  }

  /**
   * Queue pattern update
   */
  queuePatternUpdate(id: string, updates: Partial<SharedPattern>): void {
    this.pendingChanges.patterns.update.push({ id, updates });
  }

  /**
   * Queue pattern deletion
   */
  queuePatternDelete(id: string): void {
    this.pendingChanges.patterns.delete.push(id);
  }

  /**
   * Queue pattern rating
   */
  queueRating(patternId: string, rating: 1 | 2 | 3 | 4 | 5): void {
    // Remove any existing rating for this pattern
    this.pendingChanges.ratings = this.pendingChanges.ratings.filter(
      r => r.patternId !== patternId
    );
    this.pendingChanges.ratings.push({ patternId, rating });
  }

  /**
   * Perform full sync
   */
  async sync(): Promise<SyncResult> {
    if (this.syncInProgress) {
      return {
        success: false,
        frameworksPulled: 0,
        patternsPulled: 0,
        changesPushed: 0,
        conflictsResolved: 0,
        duration: 0,
        error: 'Sync already in progress',
      };
    }

    if (this.config.offlineMode) {
      return {
        success: false,
        frameworksPulled: 0,
        patternsPulled: 0,
        changesPushed: 0,
        conflictsResolved: 0,
        duration: 0,
        error: 'Offline mode enabled',
      };
    }

    this.syncInProgress = true;
    this.lastError = null;
    const startTime = Date.now();

    this.emit('sync:start');

    try {
      // Phase 1: Push local changes
      this.emit('sync:progress', { phase: 'push', progress: 0 });
      const changesPushed = await this.pushChanges();

      // Phase 2: Pull remote changes
      this.emit('sync:progress', { phase: 'pull', progress: 50 });
      const { frameworksPulled, patternsPulled, conflictsResolved } = await this.pullChanges();

      // Phase 3: Update cache metadata
      this.emit('sync:progress', { phase: 'finalize', progress: 90 });
      this.cacheManager.setLastSyncTime(new Date());
      this.cacheManager.enforceMaxSize();

      const result: SyncResult = {
        success: true,
        frameworksPulled,
        patternsPulled,
        changesPushed,
        conflictsResolved,
        duration: Date.now() - startTime,
      };

      this.emit('sync:complete', result);
      this.emit('sync:progress', { phase: 'complete', progress: 100 });

      return result;
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : 'Unknown error';
      this.lastError = errorMessage;

      const result: SyncResult = {
        success: false,
        frameworksPulled: 0,
        patternsPulled: 0,
        changesPushed: 0,
        conflictsResolved: 0,
        duration: Date.now() - startTime,
        error: errorMessage,
      };

      this.emit('sync:error', error instanceof Error ? error : new Error(errorMessage));

      return result;
    } finally {
      this.syncInProgress = false;
    }
  }

  /**
   * Push local changes to server
   */
  private async pushChanges(): Promise<number> {
    let pushed = 0;

    // Push pattern creations
    for (const pattern of this.pendingChanges.patterns.create) {
      const response = await this.apiClient.post<{ id: string }>('/patterns', pattern);
      if (response.success) {
        pushed++;
      }
    }

    // Push pattern updates
    for (const { id, updates } of this.pendingChanges.patterns.update) {
      const response = await this.apiClient.put(`/patterns/${id}`, updates);
      if (response.success) {
        pushed++;
      }
    }

    // Push pattern deletions
    for (const id of this.pendingChanges.patterns.delete) {
      const response = await this.apiClient.delete(`/patterns/${id}`);
      if (response.success) {
        pushed++;
      }
    }

    // Push ratings
    for (const { patternId, rating } of this.pendingChanges.ratings) {
      const response = await this.apiClient.post(`/patterns/${patternId}/rate`, { rating });
      if (response.success) {
        pushed++;
      }
    }

    // Clear pending changes
    this.pendingChanges = {
      patterns: { create: [], update: [], delete: [] },
      ratings: [],
    };

    return pushed;
  }

  /**
   * Pull remote changes from server
   */
  private async pullChanges(): Promise<{
    frameworksPulled: number;
    patternsPulled: number;
    conflictsResolved: number;
  }> {
    const lastSync = this.cacheManager.getLastSyncTime();
    const since = lastSync ? lastSync.getTime() : 0;

    // Get delta from server
    const response = await this.apiClient.get<SyncDelta>('/sync/delta', { since });

    if (!response.success || !response.data) {
      throw new Error(response.error || 'Failed to get sync delta');
    }

    const delta = response.data;
    let conflictsResolved = 0;

    // Apply framework changes
    if (delta.frameworks.added.length > 0 || delta.frameworks.updated.length > 0) {
      const frameworks = [...delta.frameworks.added, ...delta.frameworks.updated];
      this.cacheManager.cacheFrameworks(frameworks);
    }

    // Note: We don't delete frameworks locally, they just expire

    // Apply pattern changes
    if (delta.patterns.added.length > 0 || delta.patterns.updated.length > 0) {
      const patterns = [...delta.patterns.added, ...delta.patterns.updated];
      this.cacheManager.cachePatterns(patterns);
    }

    return {
      frameworksPulled: delta.frameworks.added.length + delta.frameworks.updated.length,
      patternsPulled: delta.patterns.added.length + delta.patterns.updated.length,
      conflictsResolved,
    };
  }

  /**
   * Force refresh all data
   */
  async forceRefresh(): Promise<SyncResult> {
    // Clear all cache
    this.cacheManager.clearAll();
    this.cacheManager.setSyncMeta('last_sync', '0');

    // Perform full sync
    return this.sync();
  }

  /**
   * Enable offline mode
   */
  enableOfflineMode(): void {
    this.config.offlineMode = true;
    this.stopAutoSync();
  }

  /**
   * Disable offline mode
   */
  disableOfflineMode(): void {
    this.config.offlineMode = false;
    this.startAutoSync();
  }

  /**
   * Check if offline mode is enabled
   */
  isOfflineMode(): boolean {
    return this.config.offlineMode;
  }
}
