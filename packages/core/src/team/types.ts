/**
 * Team Types - Type definitions for team sharing
 *
 * Implements: TSK-TEAM-001, REQ-TEAM-001
 */

/**
 * Team member information
 */
export interface TeamMember {
  id: string;
  name: string;
  email: string;
  role: 'owner' | 'admin' | 'member' | 'viewer';
  joinedAt: Date;
}

/**
 * Team configuration
 */
export interface TeamConfig {
  /** Team name */
  name: string;

  /** Team description */
  description?: string;

  /** Remote repository URL */
  remoteUrl?: string;

  /** Branch for team sharing (default: musubix-team) */
  branch?: string;

  /** Auto-sync on change */
  autoSync?: boolean;

  /** Sync interval in minutes */
  syncIntervalMinutes?: number;

  /** Patterns to share */
  sharePatterns?: boolean;

  /** Knowledge to share */
  shareKnowledge?: boolean;

  /** ADRs to share */
  shareDecisions?: boolean;
}

/**
 * Shared pattern
 */
export interface SharedPattern {
  /** Pattern ID */
  id: string;

  /** Pattern name */
  name: string;

  /** Pattern type */
  type: 'code' | 'design' | 'test' | 'documentation';

  /** Pattern description */
  description: string;

  /** Pattern content */
  content: string;

  /** Applicable languages/frameworks */
  applicableTo?: string[];

  /** Example usage */
  examples?: string[];

  /** Shared by */
  sharedBy: {
    name: string;
    email: string;
    date: Date;
  };

  /** Adoption count */
  adoptionCount?: number;

  /** Rating (1-5) */
  rating?: number;

  /** Tags */
  tags?: string[];

  /** Metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Team knowledge entry
 */
export interface TeamKnowledgeEntry {
  /** Entry ID */
  id: string;

  /** Entry type */
  type: 'concept' | 'convention' | 'guideline' | 'pitfall' | 'faq' | 'decision' | 'lesson-learned' | 'best-practice' | 'warning';

  /** Title */
  title: string;

  /** Content */
  content: string;

  /** Category */
  category: string;

  /** Related patterns */
  relatedPatterns?: string[];

  /** Related ADRs */
  relatedADRs?: string[];

  /** Related entities */
  relatedEntities?: string[];

  /** Contributor */
  contributor: TeamMember | {
    id: string;
    name: string;
    email: string;
  };

  /** Created by (legacy alias) */
  createdBy?: {
    name: string;
    email: string;
    date: Date;
  };

  /** Timestamp */
  timestamp: Date;

  /** Last updated */
  updatedAt?: Date;

  /** Tags */
  tags?: string[];
}

/**
 * Sync status
 */
export interface SyncStatus {
  /** Last sync timestamp */
  lastSync?: Date;

  /** Sync status */
  status: 'synced' | 'pending' | 'error' | 'conflict';

  /** Pending changes count */
  pendingChanges: number;

  /** Error message if any */
  error?: string;

  /** Conflicts if any */
  conflicts?: SyncConflict[];
}

/**
 * Sync conflict
 */
export interface SyncConflict {
  /** File path */
  path: string;

  /** Conflict type */
  type: 'modified' | 'deleted' | 'added';

  /** Local version */
  local?: string;

  /** Remote version */
  remote?: string;

  /** Resolution strategy */
  resolution?: 'ours' | 'theirs' | 'manual';
}

/**
 * Git operation result
 */
export interface GitResult {
  /** Success flag */
  success: boolean;

  /** Message */
  message: string;

  /** Output */
  output?: string;

  /** Error details */
  error?: string;

  /** Affected files */
  affectedFiles?: string[];
}

/**
 * Commit info
 */
export interface CommitInfo {
  /** Commit hash */
  hash: string;

  /** Short hash */
  shortHash: string;

  /** Author name */
  authorName: string;

  /** Author email */
  authorEmail: string;

  /** Commit date */
  date: Date;

  /** Commit message */
  message: string;

  /** Parent hashes */
  parents?: string[];
}

/**
 * Branch info
 */
export interface BranchInfo {
  /** Branch name */
  name: string;

  /** Is current branch */
  current: boolean;

  /** Latest commit hash */
  latestCommit?: string;

  /** Remote tracking branch */
  upstream?: string;

  /** Ahead/behind counts */
  aheadBehind?: {
    ahead: number;
    behind: number;
  };
}

/**
 * Remote info
 */
export interface RemoteInfo {
  /** Remote name */
  name: string;

  /** Fetch URL */
  fetchUrl: string;

  /** Push URL */
  pushUrl: string;
}

/**
 * File status
 */
export interface FileStatus {
  /** File path */
  path: string;

  /** Status in index */
  index: 'M' | 'A' | 'D' | 'R' | 'C' | '?' | '!' | ' ';

  /** Status in working tree */
  workingTree: 'M' | 'A' | 'D' | 'R' | 'C' | '?' | '!' | ' ';

  /** Original path (for renames) */
  originalPath?: string;
}

/**
 * Pull result
 */
export interface PullResult {
  /** Success flag */
  success: boolean;

  /** Number of commits pulled */
  commitCount: number;

  /** Changed files */
  changedFiles: string[];

  /** Inserted lines */
  insertions: number;

  /** Deleted lines */
  deletions: number;

  /** Conflicts */
  conflicts?: string[];
}

/**
 * Push result
 */
export interface PushResult {
  /** Success flag */
  success: boolean;

  /** Remote name */
  remote: string;

  /** Branch name */
  branch: string;

  /** Commits pushed */
  commitCount: number;
}
