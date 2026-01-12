/**
 * Spaces Types - Type definitions for Copilot Spaces integration
 *
 * Implements: REQ-SPACES-001〜006, DES-SPACES-001
 */

/**
 * Space definition
 */
export interface Space {
  /** Unique space identifier */
  id: string;

  /** Space display name */
  name: string;

  /** Space description */
  description?: string;

  /** Space type */
  type: SpaceType;

  /** Creation timestamp */
  createdAt: Date;

  /** Last updated timestamp */
  updatedAt: Date;

  /** Space context */
  context: SpaceContext;

  /** Space settings */
  settings: SpaceSettings;

  /** Space metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Space type
 */
export type SpaceType =
  | 'feature'       // Feature development
  | 'bugfix'        // Bug fixing
  | 'refactor'      // Refactoring
  | 'documentation' // Documentation
  | 'exploration'   // Research/exploration
  | 'custom';       // Custom space

/**
 * Space context - files, entities, and context for a space
 */
export interface SpaceContext {
  /** Included files (glob patterns or specific paths) */
  includedFiles: string[];

  /** Excluded files (glob patterns) */
  excludedFiles: string[];

  /** Related requirements */
  requirements: string[];

  /** Related designs */
  designs: string[];

  /** Related tasks */
  tasks: string[];

  /** Custom instructions for this space */
  instructions?: string;

  /** Active branch for this space */
  branch?: string;

  /** Related entities (any entity ID) */
  relatedEntities?: string[];

  /** Pinned files (always in context) */
  pinnedFiles?: string[];

  /** Recent files (automatically tracked) */
  recentFiles?: RecentFile[];
}

/**
 * Recent file entry
 */
export interface RecentFile {
  /** File path */
  path: string;

  /** Last accessed timestamp */
  lastAccessed: Date;

  /** Access count */
  accessCount: number;
}

/**
 * Space settings
 */
export interface SpaceSettings {
  /** Auto-include related files */
  autoInclude: boolean;

  /** Max files in context */
  maxContextFiles: number;

  /** Auto-track recent files */
  trackRecentFiles: boolean;

  /** Recent files limit */
  recentFilesLimit: number;

  /** Auto-create branch on space activation */
  autoCreateBranch: boolean;

  /** Branch naming pattern (supports ${spaceId}, ${spaceName}) */
  branchPattern: string;

  /** Watch mode settings for this space */
  watchSettings?: SpaceWatchSettings;

  /** CodeQL settings for this space */
  codeqlSettings?: SpaceCodeQLSettings;
}

/**
 * Watch settings for a space
 */
export interface SpaceWatchSettings {
  /** Enable watch mode */
  enabled: boolean;

  /** Run lint on file change */
  runLint: boolean;

  /** Run tests on file change */
  runTest: boolean;

  /** Run security scan on file change */
  runSecurity: boolean;

  /** Run EARS validation on requirement changes */
  runEars: boolean;
}

/**
 * CodeQL settings for a space
 */
export interface SpaceCodeQLSettings {
  /** Enable CodeQL integration */
  enabled: boolean;

  /** Auto-scan on commit */
  autoScan: boolean;

  /** Query suites to run */
  querySuites: string[];

  /** Severity threshold for blocking */
  severityThreshold: 'error' | 'warning' | 'note';
}

/**
 * Space activation result
 */
export interface SpaceActivationResult {
  /** Whether activation was successful */
  success: boolean;

  /** Space that was activated */
  space?: Space;

  /** Error message if failed */
  error?: string;

  /** Files loaded into context */
  loadedFiles?: string[];

  /** Branch created or switched to */
  branch?: string;

  /** Watch mode started */
  watchStarted?: boolean;
}

/**
 * Space creation input
 */
export interface CreateSpaceInput {
  /** Space name */
  name: string;

  /** Space description */
  description?: string;

  /** Space type */
  type: SpaceType;

  /** Initial context */
  context?: Partial<SpaceContext>;

  /** Custom settings */
  settings?: Partial<SpaceSettings>;

  /** Metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Space update input
 */
export interface UpdateSpaceInput {
  /** Updated name */
  name?: string;

  /** Updated description */
  description?: string;

  /** Updated type */
  type?: SpaceType;

  /** Context updates (merged with existing) */
  context?: Partial<SpaceContext>;

  /** Settings updates (merged with existing) */
  settings?: Partial<SpaceSettings>;

  /** Metadata updates */
  metadata?: Record<string, unknown>;
}

/**
 * Context query for finding relevant files
 */
export interface ContextQuery {
  /** Search query */
  query: string;

  /** File types to include */
  fileTypes?: string[];

  /** Max results */
  maxResults?: number;

  /** Include test files */
  includeTests?: boolean;

  /** Include node_modules */
  includeNodeModules?: boolean;
}

/**
 * Context suggestion - suggested files or entities for context
 */
export interface ContextSuggestion {
  /** Suggestion type */
  type: 'file' | 'requirement' | 'design' | 'task' | 'entity';

  /** Path or ID */
  value: string;

  /** Relevance score (0-1) */
  relevance: number;

  /** Reason for suggestion */
  reason: string;
}

/**
 * Space statistics
 */
export interface SpaceStats {
  /** Total spaces */
  totalSpaces: number;

  /** Spaces by type */
  byType: Record<SpaceType, number>;

  /** Active space ID */
  activeSpaceId?: string;

  /** Recently used spaces */
  recentSpaces: Array<{
    id: string;
    name: string;
    lastUsed: Date;
  }>;

  /** Total files in all spaces */
  totalFiles: number;

  /** Total requirements tracked */
  totalRequirements: number;
}

/**
 * Default space settings
 */
export const DEFAULT_SPACE_SETTINGS: SpaceSettings = {
  autoInclude: true,
  maxContextFiles: 50,
  trackRecentFiles: true,
  recentFilesLimit: 20,
  autoCreateBranch: false,
  branchPattern: 'space/${spaceId}',
  watchSettings: {
    enabled: false,
    runLint: true,
    runTest: true,
    runSecurity: false,
    runEars: true,
  },
  codeqlSettings: {
    enabled: false,
    autoScan: false,
    querySuites: ['javascript-security-and-quality'],
    severityThreshold: 'warning',
  },
};

/**
 * Default space context
 */
export const DEFAULT_SPACE_CONTEXT: SpaceContext = {
  includedFiles: [],
  excludedFiles: ['node_modules/**', 'dist/**', '.git/**'],
  requirements: [],
  designs: [],
  tasks: [],
  pinnedFiles: [],
  recentFiles: [],
};
