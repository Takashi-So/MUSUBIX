/**
 * TaskStatus Value Object
 * 
 * Represents the status of a task in workflow
 * 
 * @see REQ-ORCH-002 - State Tracking
 * @see DES-ORCH-002 - StateTracker
 */

/**
 * Task status type
 */
export type TaskStatus = 'not-started' | 'in-progress' | 'completed' | 'failed';

/**
 * Status metadata
 */
export interface StatusMetadata {
  readonly status: TaskStatus;
  readonly label: string;
  readonly emoji: string;
  readonly isTerminal: boolean;
}

/**
 * Status definitions
 */
export const STATUSES: ReadonlyMap<TaskStatus, StatusMetadata> = new Map([
  ['not-started', {
    status: 'not-started',
    label: '未開始',
    emoji: '⬜',
    isTerminal: false,
  }],
  ['in-progress', {
    status: 'in-progress',
    label: '進行中',
    emoji: '🔄',
    isTerminal: false,
  }],
  ['completed', {
    status: 'completed',
    label: '完了',
    emoji: '✅',
    isTerminal: true,
  }],
  ['failed', {
    status: 'failed',
    label: '失敗',
    emoji: '❌',
    isTerminal: true,
  }],
]);

/**
 * Valid status transitions
 */
export const VALID_STATUS_TRANSITIONS: ReadonlyMap<TaskStatus, readonly TaskStatus[]> = new Map([
  ['not-started', ['in-progress']],
  ['in-progress', ['completed', 'failed']],
  ['completed', []],  // Terminal
  ['failed', ['in-progress']],  // Can retry
]);

/**
 * Get status metadata
 * 
 * @param status - Task status
 * @returns Status metadata
 */
export function getStatusMetadata(status: TaskStatus): StatusMetadata {
  const metadata = STATUSES.get(status);
  if (!metadata) {
    throw new Error(`Invalid task status: ${status}`);
  }
  return metadata;
}

/**
 * Check if status transition is valid
 * 
 * @param from - Current status
 * @param to - Target status
 * @returns true if valid
 */
export function isValidStatusTransition(from: TaskStatus, to: TaskStatus): boolean {
  const validTargets = VALID_STATUS_TRANSITIONS.get(from);
  return validTargets?.includes(to) ?? false;
}

/**
 * Check if status is terminal
 * 
 * @param status - Task status
 * @returns true if terminal
 */
export function isTerminalStatus(status: TaskStatus): boolean {
  return getStatusMetadata(status).isTerminal;
}

/**
 * Get status display string
 * 
 * @param status - Task status
 * @returns Display string with emoji
 */
export function getStatusDisplay(status: TaskStatus): string {
  const metadata = getStatusMetadata(status);
  return `${metadata.emoji} ${metadata.label}`;
}
