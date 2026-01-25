/**
 * Session Manager Types
 *
 * Type definitions for session management skill
 *
 * @see REQ-SM-001 - SessionStart Hook
 * @see REQ-SM-002 - SessionEnd Hook
 * @see REQ-SM-003 - Pre-Compact State Saving
 * @see REQ-SM-004 - TodoWrite Integration
 * @see DES-v3.7.0 Section 4 - Session Manager Design
 */

/**
 * Todo item status
 */
export type TodoStatus = 'not-started' | 'in-progress' | 'completed' | 'blocked';

/**
 * Todo item for task tracking
 *
 * @see REQ-SM-004 - TodoWrite統合
 */
export interface TodoItem {
  readonly id: string;
  readonly title: string;
  readonly description?: string;
  readonly status: TodoStatus;
  readonly order: number;
  readonly createdAt: Date;
  readonly updatedAt: Date;
  readonly blockedReason?: string;
}

/**
 * Pre-compact snapshot for context preservation
 *
 * @see REQ-SM-003 - Pre-Compact State Saving
 */
export interface PreCompactSnapshot {
  readonly timestamp: Date;
  readonly toolCallCount: number;
  readonly activeContext: string[];
  readonly keyDecisions: Array<{
    readonly decision: string;
    readonly reason: string;
  }>;
  readonly pendingIssues: string[];
}

/**
 * Session data structure
 *
 * @see REQ-SM-002 - SessionEnd Hook
 */
export interface SessionData {
  readonly id: string;
  readonly date: string;
  readonly startedAt: Date;
  readonly lastUpdatedAt: Date;
  readonly projectName?: string;
  readonly completedTasks: TodoItem[];
  readonly inProgressTasks: TodoItem[];
  readonly blockedTasks: TodoItem[];
  readonly notesForNextSession: string[];
  readonly contextToLoad: string[];
  readonly preCompactSnapshots: PreCompactSnapshot[];
  readonly summary: SessionSummary;
}

/**
 * Session summary statistics
 */
export interface SessionSummary {
  readonly tasksCompleted: number;
  readonly patternsLearned: number;
  readonly checkpointsCreated: number;
  readonly toolCallsTotal: number;
}

/**
 * Session search options
 *
 * @see REQ-SM-001 - SessionStart Hook
 */
export interface SessionSearchOptions {
  readonly daysBack?: number;
  readonly projectName?: string;
  readonly limit?: number;
}

/**
 * Session notification for context restoration
 *
 * @see REQ-SM-001 - SessionStart Hook
 */
export interface SessionNotification {
  readonly previousSession: SessionData | null;
  readonly unfinishedTasks: TodoItem[];
  readonly notesFromLastSession: string[];
  readonly recommendedFiles: string[];
  readonly message: string;
}

/**
 * Session save result
 */
export interface SessionSaveResult {
  readonly success: boolean;
  readonly filePath?: string;
  readonly error?: string;
}

/**
 * Session store configuration
 */
export interface SessionStoreConfig {
  readonly sessionsDir: string;
  readonly retentionDays: number;
  readonly maxFileSizeBytes: number;
  readonly maxFileCount: number;
}

/**
 * Default session store configuration
 */
export const DEFAULT_SESSION_STORE_CONFIG: SessionStoreConfig = {
  sessionsDir: '~/.musubix/sessions',
  retentionDays: 30,
  maxFileSizeBytes: 1024 * 1024, // 1MB
  maxFileCount: 100,
};

/**
 * Session store interface
 */
export interface SessionStore {
  /**
   * Search for recent sessions
   *
   * @param options - Search options
   * @returns Array of session data
   */
  searchSessions(options?: SessionSearchOptions): Promise<SessionData[]>;

  /**
   * Get session by ID
   *
   * @param sessionId - Session ID
   * @returns Session data or null
   */
  getSession(sessionId: string): Promise<SessionData | null>;

  /**
   * Save session
   *
   * @param session - Session data to save
   * @returns Save result
   */
  saveSession(session: SessionData): Promise<SessionSaveResult>;

  /**
   * Get notification for session start
   *
   * @param options - Search options
   * @returns Session notification
   */
  getStartNotification(options?: SessionSearchOptions): Promise<SessionNotification>;

  /**
   * Cleanup old sessions
   *
   * @returns Number of sessions deleted
   */
  cleanup(): Promise<number>;
}
