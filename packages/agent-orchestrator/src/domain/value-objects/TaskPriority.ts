/**
 * TaskPriority Value Object
 * 
 * Represents the priority of a task
 * 
 * @see REQ-SDD-001 - Task Complexity Evaluation
 */

/**
 * Priority levels
 */
export type TaskPriorityLevel = 'P0' | 'P1' | 'P2';

/**
 * Immutable task priority value object
 */
export interface TaskPriority {
  /** Priority level */
  readonly level: TaskPriorityLevel;
  /** Numeric value for sorting (0 = highest) */
  readonly value: number;
  /** Human-readable label */
  readonly label: string;
}

/**
 * Priority definitions
 */
export const PRIORITIES: ReadonlyMap<TaskPriorityLevel, TaskPriority> = new Map([
  ['P0', { level: 'P0', value: 0, label: '必須（Must Have）' }],
  ['P1', { level: 'P1', value: 1, label: '重要（Should Have）' }],
  ['P2', { level: 'P2', value: 2, label: '任意（Nice to Have）' }],
]);

/**
 * Create a TaskPriority value object
 * 
 * @param level - Priority level
 * @returns TaskPriority
 */
export function createTaskPriority(level: TaskPriorityLevel): TaskPriority {
  const priority = PRIORITIES.get(level);
  if (!priority) {
    throw new Error(`Invalid priority level: ${level}`);
  }
  return priority;
}

/**
 * Compare two priorities
 * 
 * @param a - First priority
 * @param b - Second priority
 * @returns Negative if a < b, positive if a > b, 0 if equal
 */
export function comparePriorities(a: TaskPriority, b: TaskPriority): number {
  return a.value - b.value;
}
