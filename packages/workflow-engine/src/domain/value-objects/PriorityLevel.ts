/**
 * PriorityLevel Value Objects
 *
 * Defines priority levels for task triage in the SDD workflow.
 *
 * @see TSK-FR-023 - TriageEngine型定義
 * @see REQ-FR-040〜041 - TriageEngine
 * @trace DES-MUSUBIX-FR-001 DES-WORKFLOW-001
 */

/**
 * Priority level classification
 * - P0: Critical - Must be resolved immediately, blocks all other work
 * - P1: High - Should be resolved soon, may block new features
 * - P2: Medium - Normal priority, standard workflow
 * - P3: Low - Can be deferred, nice-to-have
 */
export type PriorityLevel = 'P0' | 'P1' | 'P2' | 'P3';

/**
 * Priority level metadata
 */
export interface PriorityLevelMetadata {
  readonly level: PriorityLevel;
  readonly label: string;
  readonly description: string;
  readonly blocksNewWork: boolean;
  readonly maxResponseTimeHours: number;
  readonly color: string;
}

/**
 * Priority level configuration
 */
export const PRIORITY_LEVELS: ReadonlyMap<PriorityLevel, PriorityLevelMetadata> = new Map([
  ['P0', {
    level: 'P0',
    label: '🔴 Critical',
    description: 'Must be resolved immediately, blocks all other work',
    blocksNewWork: true,
    maxResponseTimeHours: 4,
    color: 'red',
  }],
  ['P1', {
    level: 'P1',
    label: '🟠 High',
    description: 'Should be resolved soon, may block new features',
    blocksNewWork: true,
    maxResponseTimeHours: 24,
    color: 'orange',
  }],
  ['P2', {
    level: 'P2',
    label: '🟡 Medium',
    description: 'Normal priority, standard workflow',
    blocksNewWork: false,
    maxResponseTimeHours: 72,
    color: 'yellow',
  }],
  ['P3', {
    level: 'P3',
    label: '🟢 Low',
    description: 'Can be deferred, nice-to-have',
    blocksNewWork: false,
    maxResponseTimeHours: 168, // 1 week
    color: 'green',
  }],
]);

/**
 * Triage result for a single task
 */
export interface TriageResult {
  readonly taskId: string;
  readonly priority: PriorityLevel;
  readonly reason: string;
  readonly suggestedAction: string;
  readonly estimatedEffort?: string;
  readonly blockedBy?: readonly string[];
  readonly blocking?: readonly string[];
}

/**
 * Triage check result (for QualityGate)
 */
export interface TriageCheckResult {
  readonly passed: boolean;
  readonly message: string;
  readonly severity: 'info' | 'warning' | 'error';
  readonly blockingTasks: readonly TriageResult[];
  readonly details?: string;
}

/**
 * Task status for triage
 */
export type TaskStatus =
  | 'open'
  | 'in-progress'
  | 'blocked'
  | 'resolved'
  | 'closed';

/**
 * Task for triage
 */
export interface TriageTask {
  readonly id: string;
  readonly title: string;
  readonly description?: string;
  readonly priority?: PriorityLevel;
  readonly status: TaskStatus;
  readonly type: 'bug' | 'feature' | 'improvement' | 'task';
  readonly createdAt: Date;
  readonly updatedAt?: Date;
  readonly assignee?: string;
  readonly labels?: readonly string[];
}

/**
 * Triage configuration
 */
export interface TriageConfig {
  /** Priority levels that block new work */
  readonly blockingPriorities: readonly PriorityLevel[];
  /** Task statuses considered "active" */
  readonly activeStatuses: readonly TaskStatus[];
  /** Whether to include in-progress tasks in blocking check */
  readonly includeInProgress: boolean;
  /** Maximum age (days) for blocking tasks */
  readonly maxBlockingAgeDays: number;
}

/**
 * Default triage configuration
 */
export const DEFAULT_TRIAGE_CONFIG: TriageConfig = Object.freeze({
  blockingPriorities: ['P0', 'P1'] as readonly PriorityLevel[],
  activeStatuses: ['open', 'in-progress', 'blocked'] as readonly TaskStatus[],
  includeInProgress: true,
  maxBlockingAgeDays: 30,
});

/**
 * Check if a priority level blocks new work
 */
export function blocksNewWork(priority: PriorityLevel): boolean {
  const metadata = PRIORITY_LEVELS.get(priority);
  return metadata?.blocksNewWork ?? false;
}

/**
 * Get priority level metadata
 */
export function getPriorityMetadata(priority: PriorityLevel): PriorityLevelMetadata | undefined {
  return PRIORITY_LEVELS.get(priority);
}

/**
 * Compare priority levels (lower number = higher priority)
 * Returns negative if a > b, positive if a < b, 0 if equal
 */
export function comparePriority(a: PriorityLevel, b: PriorityLevel): number {
  const order: Record<PriorityLevel, number> = { P0: 0, P1: 1, P2: 2, P3: 3 };
  return order[a] - order[b];
}

/**
 * Create a triage result
 */
export function createTriageResult(params: {
  taskId: string;
  priority: PriorityLevel;
  reason: string;
  suggestedAction: string;
  estimatedEffort?: string;
  blockedBy?: readonly string[];
  blocking?: readonly string[];
}): TriageResult {
  return Object.freeze({
    taskId: params.taskId,
    priority: params.priority,
    reason: params.reason,
    suggestedAction: params.suggestedAction,
    estimatedEffort: params.estimatedEffort,
    blockedBy: params.blockedBy,
    blocking: params.blocking,
  });
}

/**
 * Create a triage check result
 */
export function createTriageCheckResult(params: {
  passed: boolean;
  message: string;
  severity: 'info' | 'warning' | 'error';
  blockingTasks?: readonly TriageResult[];
  details?: string;
}): TriageCheckResult {
  return Object.freeze({
    passed: params.passed,
    message: params.message,
    severity: params.severity,
    blockingTasks: Object.freeze(params.blockingTasks ?? []),
    details: params.details,
  });
}
