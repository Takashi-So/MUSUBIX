/**
 * Checkpoint Types
 *
 * Type definitions for checkpoint skill
 *
 * @see REQ-CP-001 - Checkpoint Creation
 * @see REQ-CP-002 - Checkpoint Verification
 * @see REQ-CP-003 - Checkpoint Listing
 * @see REQ-CP-004 - Checkpoint Restore
 * @see REQ-CP-005 - Checkpoint Retention & Location
 */

/**
 * Checkpoint status
 */
export type CheckpointStatus = 'current' | 'behind' | 'ahead';

/**
 * Checkpoint entry
 *
 * @see REQ-CP-001 - Checkpoint Creation
 */
export interface CheckpointEntry {
  readonly name: string;
  readonly timestamp: Date;
  readonly gitSha: string;
  readonly gitShortSha: string;
  readonly verificationStatus: 'passed' | 'failed' | 'skipped';
  readonly status: CheckpointStatus;
  readonly message?: string;
}

/**
 * Checkpoint comparison result
 *
 * @see REQ-CP-002 - Checkpoint Verification
 */
export interface CheckpointComparison {
  readonly checkpointName: string;
  readonly checkpointSha: string;
  readonly currentSha: string;
  readonly filesChanged: number;
  readonly additions: number;
  readonly deletions: number;
  readonly testsPassed?: number;
  readonly testsTotal?: number;
  readonly coverageChange?: number;
  readonly buildStatus: 'passing' | 'failing' | 'unknown';
}

/**
 * Checkpoint list entry
 *
 * @see REQ-CP-003 - Checkpoint Listing
 */
export interface CheckpointListEntry {
  readonly name: string;
  readonly timestamp: Date;
  readonly gitShortSha: string;
  readonly status: CheckpointStatus;
  readonly isCurrent: boolean;
}

/**
 * Checkpoint restore result
 *
 * @see REQ-CP-004 - Checkpoint Restore
 */
export interface CheckpointRestoreResult {
  readonly success: boolean;
  readonly checkpointName: string;
  readonly previousSha: string;
  readonly restoredSha: string;
  readonly stashCreated?: string;
  readonly message: string;
}

/**
 * Checkpoint configuration
 *
 * @see REQ-CP-005 - Checkpoint Retention & Location
 */
export interface CheckpointConfig {
  readonly checkpointsDir: string;
  readonly logFile: string;
  readonly maxCheckpoints: number;
  readonly autoVerify: boolean;
}

/**
 * Default checkpoint configuration
 */
export const DEFAULT_CHECKPOINT_CONFIG: CheckpointConfig = {
  checkpointsDir: '~/.musubix/checkpoints',
  logFile: '~/.musubix/checkpoints/checkpoints.log',
  maxCheckpoints: 10,
  autoVerify: true,
};

/**
 * Checkpoint manager interface
 */
export interface CheckpointManager {
  /**
   * Create a checkpoint
   *
   * @param name - Checkpoint name
   * @param runVerification - Whether to run verification before creating
   * @returns Created checkpoint entry
   */
  createCheckpoint(
    name: string,
    runVerification?: boolean
  ): Promise<CheckpointEntry>;

  /**
   * Verify checkpoint against current state
   *
   * @param name - Checkpoint name
   * @returns Comparison result
   */
  verifyCheckpoint(name: string): Promise<CheckpointComparison>;

  /**
   * List all checkpoints
   *
   * @returns Array of checkpoint list entries
   */
  listCheckpoints(): Promise<CheckpointListEntry[]>;

  /**
   * Restore to a checkpoint
   *
   * @param name - Checkpoint name
   * @param stashUncommitted - Whether to stash uncommitted changes
   * @returns Restore result
   */
  restoreCheckpoint(
    name: string,
    stashUncommitted?: boolean
  ): Promise<CheckpointRestoreResult>;

  /**
   * Delete a checkpoint
   *
   * @param name - Checkpoint name
   * @returns Success status
   */
  deleteCheckpoint(name: string): Promise<boolean>;

  /**
   * Get checkpoint by name
   *
   * @param name - Checkpoint name
   * @returns Checkpoint entry or null
   */
  getCheckpoint(name: string): Promise<CheckpointEntry | null>;

  /**
   * Clean old checkpoints beyond retention limit
   *
   * @returns Number of checkpoints deleted
   */
  cleanOldCheckpoints(): Promise<number>;

  /**
   * Get configuration
   */
  getConfig(): CheckpointConfig;
}
