/**
 * YATA Global - Type Definitions
 *
 * @packageDocumentation
 * @module @nahisaho/yata-global
 *
 * @see REQ-YATA-GLOBAL-001
 */

/**
 * Framework knowledge entry
 * @see REQ-YG-REPO-001
 */
export interface FrameworkKnowledge {
  /** Framework identifier */
  id: string;
  /** Framework name */
  name: string;
  /** Version */
  version: string;
  /** Category (e.g., web, database, testing) */
  category: FrameworkCategory;
  /** Language */
  language: ProgrammingLanguage;
  /** Description */
  description: string;
  /** Official documentation URL */
  documentationUrl?: string;
  /** GitHub repository URL */
  repositoryUrl?: string;
  /** License */
  license?: string;
  /** Popularity score (0-100) */
  popularity: number;
  /** Quality score (0-100) */
  quality: number;
  /** Tags */
  tags: string[];
  /** Last updated */
  updatedAt: Date;
  /** Created timestamp */
  createdAt: Date;
}

/**
 * Framework categories
 */
export type FrameworkCategory =
  | 'web-frontend'
  | 'web-backend'
  | 'mobile'
  | 'desktop'
  | 'database'
  | 'orm'
  | 'testing'
  | 'build-tool'
  | 'cli'
  | 'ai-ml'
  | 'devops'
  | 'cloud'
  | 'security'
  | 'networking'
  | 'data-processing'
  | 'logging'
  | 'monitoring'
  | 'documentation'
  | 'other';

/**
 * Programming languages
 */
export type ProgrammingLanguage =
  | 'typescript'
  | 'javascript'
  | 'python'
  | 'java'
  | 'kotlin'
  | 'swift'
  | 'go'
  | 'rust'
  | 'c'
  | 'cpp'
  | 'csharp'
  | 'ruby'
  | 'php'
  | 'scala'
  | 'haskell'
  | 'elixir'
  | 'clojure'
  | 'dart'
  | 'r'
  | 'julia'
  | 'multi';

/**
 * Code pattern shared in the community
 * @see REQ-YG-COMM-001
 */
export interface SharedPattern {
  /** Pattern identifier */
  id: string;
  /** Pattern name */
  name: string;
  /** Description */
  description: string;
  /** Pattern category */
  category: PatternCategory;
  /** Associated frameworks */
  frameworks: string[];
  /** Language */
  language: ProgrammingLanguage;
  /** Code template */
  template: string;
  /** Example usage */
  example?: string;
  /** Tags */
  tags: string[];
  /** Author ID */
  authorId: string;
  /** Community ratings */
  rating: CommunityRating;
  /** Download count */
  downloads: number;
  /** Is official pattern */
  official: boolean;
  /** Visibility */
  visibility: 'public' | 'private' | 'unlisted';
  /** Created timestamp */
  createdAt: Date;
  /** Last updated */
  updatedAt: Date;
}

/**
 * Pattern categories
 */
export type PatternCategory =
  | 'architecture'
  | 'design-pattern'
  | 'testing'
  | 'error-handling'
  | 'authentication'
  | 'authorization'
  | 'api-design'
  | 'data-access'
  | 'validation'
  | 'logging'
  | 'caching'
  | 'async'
  | 'configuration'
  | 'dependency-injection'
  | 'other';

/**
 * Community rating for patterns
 * @see REQ-YG-COMM-002
 */
export interface CommunityRating {
  /** Average rating (1-5) */
  average: number;
  /** Total votes */
  count: number;
  /** Rating distribution */
  distribution: {
    1: number;
    2: number;
    3: number;
    4: number;
    5: number;
  };
}

/**
 * User in the YATA Global community
 */
export interface User {
  /** User identifier */
  id: string;
  /** Username */
  username: string;
  /** Display name */
  displayName?: string;
  /** Email */
  email: string;
  /** Avatar URL */
  avatarUrl?: string;
  /** Bio */
  bio?: string;
  /** Reputation score */
  reputation: number;
  /** Number of contributions */
  contributions: number;
  /** Subscription tier */
  tier: SubscriptionTier;
  /** Joined timestamp */
  joinedAt: Date;
}

/**
 * Subscription tiers
 * @see REQ-YG-COMM-004
 */
export type SubscriptionTier = 'free' | 'pro' | 'enterprise';

/**
 * Sync configuration
 * @see REQ-YG-SYNC-001
 */
export interface SyncConfig {
  /** Server endpoint */
  endpoint: string;
  /** API key or token */
  apiKey?: string;
  /** Sync interval in seconds */
  syncInterval: number;
  /** Frameworks to sync */
  frameworks?: string[];
  /** Whether to sync patterns */
  syncPatterns: boolean;
  /** Whether to sync offline */
  offlineMode: boolean;
  /** Maximum cache size in bytes */
  maxCacheSize: number;
}

/**
 * Default sync configuration
 */
export const DEFAULT_SYNC_CONFIG: SyncConfig = {
  endpoint: 'https://api.yata.global/v1',
  syncInterval: 3600, // 1 hour
  syncPatterns: true,
  offlineMode: true,
  maxCacheSize: 100 * 1024 * 1024, // 100MB
};

/**
 * Sync status
 */
export interface SyncStatus {
  /** Last sync timestamp */
  lastSync: Date | null;
  /** Sync in progress */
  inProgress: boolean;
  /** Pending changes count */
  pendingChanges: number;
  /** Last error */
  lastError?: string;
  /** Connection status */
  connected: boolean;
}

/**
 * Sync result
 */
export interface SyncResult {
  /** Success status */
  success: boolean;
  /** Frameworks pulled */
  frameworksPulled: number;
  /** Patterns pulled */
  patternsPulled: number;
  /** Local changes pushed */
  changesPushed: number;
  /** Conflicts resolved */
  conflictsResolved: number;
  /** Duration in ms */
  duration: number;
  /** Error if any */
  error?: string;
}

/**
 * Search options
 * @see REQ-YG-SEARCH-001
 */
export interface SearchOptions {
  /** Search query */
  query: string;
  /** Filter by category */
  category?: FrameworkCategory | PatternCategory;
  /** Filter by language */
  language?: ProgrammingLanguage;
  /** Filter by tags */
  tags?: string[];
  /** Minimum quality score */
  minQuality?: number;
  /** Sort by */
  sortBy?: 'relevance' | 'popularity' | 'quality' | 'updated';
  /** Max results */
  limit?: number;
  /** Offset for pagination */
  offset?: number;
}

/**
 * Search result
 */
export interface SearchResult<T> {
  /** Matched items */
  items: T[];
  /** Total count */
  total: number;
  /** Query execution time */
  executionTime: number;
  /** Has more results */
  hasMore: boolean;
}

/**
 * API rate limit info
 * @see REQ-YG-API-004
 */
export interface RateLimitInfo {
  /** Requests remaining */
  remaining: number;
  /** Rate limit */
  limit: number;
  /** Reset timestamp */
  resetAt: Date;
}

/**
 * API response wrapper
 */
export interface ApiResponse<T> {
  /** Success status */
  success: boolean;
  /** Response data */
  data?: T;
  /** Error message */
  error?: string;
  /** Rate limit info */
  rateLimit?: RateLimitInfo;
}

/**
 * Authentication token
 * @see REQ-YG-API-005
 */
export interface AuthToken {
  /** Access token */
  accessToken: string;
  /** Refresh token */
  refreshToken?: string;
  /** Token type */
  tokenType: 'Bearer';
  /** Expiration timestamp */
  expiresAt: Date;
  /** Scopes */
  scopes: string[];
}

/**
 * Analytics data
 * @see REQ-YG-ANALYTICS-001
 */
export interface AnalyticsData {
  /** Total frameworks */
  totalFrameworks: number;
  /** Total patterns */
  totalPatterns: number;
  /** Total users */
  totalUsers: number;
  /** Frameworks by category */
  frameworksByCategory: Record<FrameworkCategory, number>;
  /** Patterns by category */
  patternsByCategory: Record<PatternCategory, number>;
  /** Top frameworks by popularity */
  topFrameworks: FrameworkKnowledge[];
  /** Top patterns by downloads */
  topPatterns: SharedPattern[];
  /** Recent activity */
  recentActivity: ActivityItem[];
}

/**
 * Activity item
 */
export interface ActivityItem {
  /** Activity type */
  type: 'framework_added' | 'pattern_shared' | 'pattern_rated' | 'user_joined';
  /** Actor ID */
  actorId: string;
  /** Target ID */
  targetId: string;
  /** Timestamp */
  timestamp: Date;
  /** Details */
  details: Record<string, unknown>;
}

/**
 * YATA Global client interface
 */
export interface YataGlobalClient {
  // Configuration
  configure(config: Partial<SyncConfig>): void;
  getConfig(): SyncConfig;

  // Authentication
  login(credentials: { username: string; password: string }): Promise<AuthToken>;
  loginWithToken(token: string): Promise<AuthToken>;
  logout(): Promise<void>;
  isAuthenticated(): boolean;

  // Framework knowledge
  getFramework(id: string): Promise<FrameworkKnowledge | null>;
  searchFrameworks(options: SearchOptions): Promise<SearchResult<FrameworkKnowledge>>;
  getFrameworksByCategory(category: FrameworkCategory): Promise<FrameworkKnowledge[]>;

  // Patterns
  getPattern(id: string): Promise<SharedPattern | null>;
  searchPatterns(options: SearchOptions): Promise<SearchResult<SharedPattern>>;
  sharePattern(pattern: Omit<SharedPattern, 'id' | 'authorId' | 'rating' | 'downloads' | 'createdAt' | 'updatedAt'>): Promise<string>;
  ratePattern(patternId: string, rating: 1 | 2 | 3 | 4 | 5): Promise<void>;
  deletePattern(patternId: string): Promise<void>;

  // Sync
  sync(): Promise<SyncResult>;
  getSyncStatus(): SyncStatus;
  enableOfflineMode(): void;
  disableOfflineMode(): void;

  // Analytics
  getAnalytics(): Promise<AnalyticsData>;

  // User
  getCurrentUser(): Promise<User | null>;
  updateProfile(updates: Partial<User>): Promise<void>;
}

/**
 * Event types emitted by YATA Global
 */
export interface YataGlobalEvents {
  'sync:start': void;
  'sync:complete': SyncResult;
  'sync:error': Error;
  'auth:login': User;
  'auth:logout': void;
  'connection:online': void;
  'connection:offline': void;
}
