/**
 * YATA Global - Main Client
 *
 * @packageDocumentation
 * @module @nahisaho/yata-global
 *
 * @see REQ-YATA-GLOBAL-001
 */

import { EventEmitter } from 'events';
import * as path from 'path';
import * as os from 'os';
import type {
  FrameworkKnowledge,
  FrameworkCategory,
  SharedPattern,
  SearchOptions,
  SearchResult,
  SyncConfig,
  SyncResult,
  SyncStatus,
  AuthToken,
  User,
  AnalyticsData,
  YataGlobalClient,
} from './types.js';
import { DEFAULT_SYNC_CONFIG } from './types.js';
import { ApiClient } from './api-client.js';
import { CacheManager } from './cache-manager.js';
import { SyncEngine } from './sync-engine.js';

/**
 * YATA Global main client
 */
export class YataGlobal extends EventEmitter implements YataGlobalClient {
  private config: SyncConfig;
  private apiClient: ApiClient;
  private cacheManager: CacheManager;
  private syncEngine: SyncEngine;
  private currentUser: User | null = null;

  constructor(config: Partial<SyncConfig> = {}) {
    super();

    this.config = { ...DEFAULT_SYNC_CONFIG, ...config };
    this.apiClient = new ApiClient(this.config);

    // Default cache location
    const cacheDir = process.env.YATA_CACHE_DIR || path.join(os.homedir(), '.yata');
    const cachePath = path.join(cacheDir, 'global-cache.sqlite');

    this.cacheManager = new CacheManager(cachePath, this.config);
    this.syncEngine = new SyncEngine(this.apiClient, this.cacheManager, this.config);

    // Forward sync engine events
    this.syncEngine.on('sync:start', () => this.emit('sync:start'));
    this.syncEngine.on('sync:complete', (result: SyncResult) => this.emit('sync:complete', result));
    this.syncEngine.on('sync:error', (error: Error) => this.emit('sync:error', error));
  }

  /**
   * Close connections and cleanup
   */
  close(): void {
    this.syncEngine.stopAutoSync();
    this.cacheManager.close();
  }

  // ========================================
  // Configuration
  // ========================================

  /**
   * Update configuration
   */
  configure(config: Partial<SyncConfig>): void {
    this.config = { ...this.config, ...config };
    this.apiClient.configure(config);
  }

  /**
   * Get current configuration
   */
  getConfig(): SyncConfig {
    return { ...this.config };
  }

  // ========================================
  // Authentication
  // ========================================

  /**
   * Login with username/password
   */
  async login(credentials: { username: string; password: string }): Promise<AuthToken> {
    const response = await this.apiClient.post<AuthToken>('/auth/login', credentials);

    if (!response.success || !response.data) {
      throw new Error(response.error || 'Login failed');
    }

    const token = {
      ...response.data,
      expiresAt: new Date(response.data.expiresAt),
    };

    this.apiClient.setAuthToken(token);
    await this.fetchCurrentUser();

    if (this.currentUser) {
      this.emit('auth:login', this.currentUser);
    }

    return token;
  }

  /**
   * Login with existing token
   */
  async loginWithToken(token: string): Promise<AuthToken> {
    const authToken: AuthToken = {
      accessToken: token,
      tokenType: 'Bearer',
      expiresAt: new Date(Date.now() + 3600 * 1000), // Assume 1 hour validity
      scopes: [],
    };

    this.apiClient.setAuthToken(authToken);

    // Validate token by fetching user
    await this.fetchCurrentUser();

    if (!this.currentUser) {
      this.apiClient.setAuthToken(null);
      throw new Error('Invalid token');
    }

    this.emit('auth:login', this.currentUser);

    return authToken;
  }

  /**
   * Logout
   */
  async logout(): Promise<void> {
    const token = this.apiClient.getAuthToken();
    if (token) {
      await this.apiClient.post('/auth/logout');
    }

    this.apiClient.setAuthToken(null);
    this.currentUser = null;

    this.emit('auth:logout');
  }

  /**
   * Check if authenticated
   */
  isAuthenticated(): boolean {
    const token = this.apiClient.getAuthToken();
    if (!token) return false;
    return token.expiresAt > new Date();
  }

  /**
   * Fetch current user info
   */
  private async fetchCurrentUser(): Promise<void> {
    const response = await this.apiClient.get<User>('/users/me');
    if (response.success && response.data) {
      this.currentUser = {
        ...response.data,
        joinedAt: new Date(response.data.joinedAt),
      };
    } else {
      this.currentUser = null;
    }
  }

  // ========================================
  // Framework Knowledge
  // ========================================

  /**
   * Get framework by ID
   */
  async getFramework(id: string): Promise<FrameworkKnowledge | null> {
    // Check cache first
    const cached = this.cacheManager.getFramework(id);
    if (cached) return cached;

    // Fetch from API
    if (!this.config.offlineMode) {
      const response = await this.apiClient.get<FrameworkKnowledge>(`/frameworks/${id}`);
      if (response.success && response.data) {
        const framework = {
          ...response.data,
          updatedAt: new Date(response.data.updatedAt),
          createdAt: new Date(response.data.createdAt),
        };
        this.cacheManager.cacheFramework(framework);
        return framework;
      }
    }

    return null;
  }

  /**
   * Search frameworks
   */
  async searchFrameworks(options: SearchOptions): Promise<SearchResult<FrameworkKnowledge>> {
    const startTime = Date.now();

    // In offline mode, search local cache
    if (this.config.offlineMode) {
      const all = this.cacheManager.getAllFrameworks();
      const filtered = this.filterFrameworks(all, options);
      const sorted = this.sortResults(filtered, options.sortBy || 'relevance');
      const offset = options.offset || 0;
      const limit = options.limit || 20;
      const items = sorted.slice(offset, offset + limit);

      return {
        items,
        total: filtered.length,
        executionTime: Date.now() - startTime,
        hasMore: offset + limit < filtered.length,
      };
    }

    // Search via API
    const params: Record<string, string | number | boolean> = {
      q: options.query,
    };
    if (options.category) params.category = options.category;
    if (options.language) params.language = options.language;
    if (options.tags) params.tags = options.tags.join(',');
    if (options.minQuality !== undefined) params.minQuality = options.minQuality;
    if (options.sortBy) params.sortBy = options.sortBy;
    if (options.limit !== undefined) params.limit = options.limit;
    if (options.offset !== undefined) params.offset = options.offset;

    const response = await this.apiClient.get<SearchResult<FrameworkKnowledge>>('/frameworks/search', params);

    if (response.success && response.data) {
      // Cache results
      this.cacheManager.cacheFrameworks(response.data.items);
      return {
        ...response.data,
        executionTime: Date.now() - startTime,
      };
    }

    // Fallback to cache
    const all = this.cacheManager.getAllFrameworks();
    const filtered = this.filterFrameworks(all, options);

    return {
      items: filtered.slice(0, options.limit || 20),
      total: filtered.length,
      executionTime: Date.now() - startTime,
      hasMore: filtered.length > (options.limit || 20),
    };
  }

  /**
   * Get frameworks by category
   */
  async getFrameworksByCategory(category: FrameworkCategory): Promise<FrameworkKnowledge[]> {
    const result = await this.searchFrameworks({
      query: '',
      category,
      sortBy: 'popularity',
      limit: 100,
    });
    return result.items;
  }

  /**
   * Filter frameworks by search options
   */
  private filterFrameworks(frameworks: FrameworkKnowledge[], options: SearchOptions): FrameworkKnowledge[] {
    return frameworks.filter(fw => {
      // Query match
      if (options.query) {
        const q = options.query.toLowerCase();
        const matches =
          fw.name.toLowerCase().includes(q) ||
          fw.description.toLowerCase().includes(q) ||
          fw.tags.some(t => t.toLowerCase().includes(q));
        if (!matches) return false;
      }

      // Category filter
      if (options.category && fw.category !== options.category) return false;

      // Language filter
      if (options.language && fw.language !== options.language) return false;

      // Tags filter
      if (options.tags && options.tags.length > 0) {
        const hasTags = options.tags.some(t => fw.tags.includes(t));
        if (!hasTags) return false;
      }

      // Quality filter
      if (options.minQuality && fw.quality < options.minQuality) return false;

      return true;
    });
  }

  // ========================================
  // Patterns
  // ========================================

  /**
   * Get pattern by ID
   */
  async getPattern(id: string): Promise<SharedPattern | null> {
    // Check cache first
    const cached = this.cacheManager.getPattern(id);
    if (cached) return cached;

    // Fetch from API
    if (!this.config.offlineMode) {
      const response = await this.apiClient.get<SharedPattern>(`/patterns/${id}`);
      if (response.success && response.data) {
        const pattern = {
          ...response.data,
          updatedAt: new Date(response.data.updatedAt),
          createdAt: new Date(response.data.createdAt),
        };
        this.cacheManager.cachePattern(pattern);
        return pattern;
      }
    }

    return null;
  }

  /**
   * Search patterns
   */
  async searchPatterns(options: SearchOptions): Promise<SearchResult<SharedPattern>> {
    const startTime = Date.now();

    // In offline mode, search local cache
    if (this.config.offlineMode) {
      const all = this.cacheManager.getAllPatterns();
      const filtered = this.filterPatterns(all, options);
      const sorted = this.sortResults(filtered, options.sortBy || 'relevance');
      const offset = options.offset || 0;
      const limit = options.limit || 20;
      const items = sorted.slice(offset, offset + limit);

      return {
        items,
        total: filtered.length,
        executionTime: Date.now() - startTime,
        hasMore: offset + limit < filtered.length,
      };
    }

    // Search via API
    const patternParams: Record<string, string | number | boolean> = {
      q: options.query,
    };
    if (options.category) patternParams.category = options.category;
    if (options.language) patternParams.language = options.language;
    if (options.tags) patternParams.tags = options.tags.join(',');
    if (options.minQuality !== undefined) patternParams.minQuality = options.minQuality;
    if (options.sortBy) patternParams.sortBy = options.sortBy;
    if (options.limit !== undefined) patternParams.limit = options.limit;
    if (options.offset !== undefined) patternParams.offset = options.offset;

    const response = await this.apiClient.get<SearchResult<SharedPattern>>('/patterns/search', patternParams);

    if (response.success && response.data) {
      // Cache results
      this.cacheManager.cachePatterns(response.data.items);
      return {
        ...response.data,
        executionTime: Date.now() - startTime,
      };
    }

    // Fallback to cache
    const all = this.cacheManager.getAllPatterns();
    const filtered = this.filterPatterns(all, options);

    return {
      items: filtered.slice(0, options.limit || 20),
      total: filtered.length,
      executionTime: Date.now() - startTime,
      hasMore: filtered.length > (options.limit || 20),
    };
  }

  /**
   * Share a new pattern
   */
  async sharePattern(
    pattern: Omit<SharedPattern, 'id' | 'authorId' | 'rating' | 'downloads' | 'createdAt' | 'updatedAt'>
  ): Promise<string> {
    if (!this.isAuthenticated()) {
      throw new Error('Authentication required to share patterns');
    }

    if (this.config.offlineMode) {
      // Queue for later sync
      this.syncEngine.queuePatternCreate(pattern);
      return 'pending-' + Date.now();
    }

    const response = await this.apiClient.post<{ id: string }>('/patterns', pattern);

    if (!response.success || !response.data) {
      throw new Error(response.error || 'Failed to share pattern');
    }

    return response.data.id;
  }

  /**
   * Rate a pattern
   */
  async ratePattern(patternId: string, rating: 1 | 2 | 3 | 4 | 5): Promise<void> {
    if (!this.isAuthenticated()) {
      throw new Error('Authentication required to rate patterns');
    }

    if (this.config.offlineMode) {
      this.syncEngine.queueRating(patternId, rating);
      return;
    }

    const response = await this.apiClient.post(`/patterns/${patternId}/rate`, { rating });

    if (!response.success) {
      throw new Error(response.error || 'Failed to rate pattern');
    }
  }

  /**
   * Delete a pattern
   */
  async deletePattern(patternId: string): Promise<void> {
    if (!this.isAuthenticated()) {
      throw new Error('Authentication required to delete patterns');
    }

    if (this.config.offlineMode) {
      this.syncEngine.queuePatternDelete(patternId);
      return;
    }

    const response = await this.apiClient.delete(`/patterns/${patternId}`);

    if (!response.success) {
      throw new Error(response.error || 'Failed to delete pattern');
    }
  }

  /**
   * Filter patterns by search options
   */
  private filterPatterns(patterns: SharedPattern[], options: SearchOptions): SharedPattern[] {
    return patterns.filter(p => {
      // Only show public patterns in search
      if (p.visibility !== 'public') return false;

      // Query match
      if (options.query) {
        const q = options.query.toLowerCase();
        const matches =
          p.name.toLowerCase().includes(q) ||
          p.description.toLowerCase().includes(q) ||
          p.tags.some(t => t.toLowerCase().includes(q));
        if (!matches) return false;
      }

      // Category filter
      if (options.category && p.category !== options.category) return false;

      // Language filter
      if (options.language && p.language !== options.language) return false;

      // Tags filter
      if (options.tags && options.tags.length > 0) {
        const hasTags = options.tags.some(t => p.tags.includes(t));
        if (!hasTags) return false;
      }

      return true;
    });
  }

  /**
   * Sort results by criteria
   */
  private sortResults<T extends { popularity?: number; quality?: number; rating?: { average: number }; downloads?: number; updatedAt: Date }>(
    items: T[],
    sortBy: string
  ): T[] {
    return [...items].sort((a, b) => {
      switch (sortBy) {
        case 'popularity':
          return (b.popularity || b.downloads || 0) - (a.popularity || a.downloads || 0);
        case 'quality':
          return (b.quality || b.rating?.average || 0) - (a.quality || a.rating?.average || 0);
        case 'updated':
          return b.updatedAt.getTime() - a.updatedAt.getTime();
        default: // relevance - already sorted by search
          return 0;
      }
    });
  }

  // ========================================
  // Sync
  // ========================================

  /**
   * Perform sync with server
   */
  async sync(): Promise<SyncResult> {
    return this.syncEngine.sync();
  }

  /**
   * Get current sync status
   */
  getSyncStatus(): SyncStatus {
    return this.syncEngine.getStatus();
  }

  /**
   * Enable offline mode
   */
  enableOfflineMode(): void {
    this.config.offlineMode = true;
    this.syncEngine.enableOfflineMode();
    this.emit('connection:offline');
  }

  /**
   * Disable offline mode
   */
  disableOfflineMode(): void {
    this.config.offlineMode = false;
    this.syncEngine.disableOfflineMode();
    this.emit('connection:online');
  }

  // ========================================
  // Analytics
  // ========================================

  /**
   * Get analytics data
   */
  async getAnalytics(): Promise<AnalyticsData> {
    if (this.config.offlineMode) {
      // Return cached/local stats
      const stats = this.cacheManager.getStats();
      return {
        totalFrameworks: stats.frameworkCount,
        totalPatterns: stats.patternCount,
        totalUsers: 0,
        frameworksByCategory: {} as Record<FrameworkCategory, number>,
        patternsByCategory: {} as Record<import('./types.js').PatternCategory, number>,
        topFrameworks: [],
        topPatterns: [],
        recentActivity: [],
      };
    }

    const response = await this.apiClient.get<AnalyticsData>('/analytics');

    if (!response.success || !response.data) {
      throw new Error(response.error || 'Failed to get analytics');
    }

    return response.data;
  }

  // ========================================
  // User
  // ========================================

  /**
   * Get current user
   */
  async getCurrentUser(): Promise<User | null> {
    if (!this.isAuthenticated()) return null;

    if (this.currentUser) return this.currentUser;

    await this.fetchCurrentUser();
    return this.currentUser;
  }

  /**
   * Update user profile
   */
  async updateProfile(updates: Partial<User>): Promise<void> {
    if (!this.isAuthenticated()) {
      throw new Error('Authentication required');
    }

    const response = await this.apiClient.put('/users/me', updates);

    if (!response.success) {
      throw new Error(response.error || 'Failed to update profile');
    }

    await this.fetchCurrentUser();
  }
}

/**
 * Create YATA Global client
 */
export function createYataGlobal(config: Partial<SyncConfig> = {}): YataGlobal {
  return new YataGlobal(config);
}

// Re-export types and classes
export * from './types.js';
export { ApiClient } from './api-client.js';
export { CacheManager } from './cache-manager.js';
export { SyncEngine } from './sync-engine.js';

// KGPR exports
export * from './kgpr/index.js';
