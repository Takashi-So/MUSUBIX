/**
 * Task Status Value Object
 * 
 * @see REQ-PM-TSK-002 - カンバンステータス遷移
 * @see DES-PM-001 Section 3.2.2
 * @see TSK-PM-001 - Value Objects実装
 */

export type TaskStatus = 'backlog' | 'todo' | 'inProgress' | 'review' | 'done';

/**
 * Valid task status transitions (Kanban workflow)
 * @see BP-DESIGN-001 - Status Transition Map
 */
export const validTaskStatusTransitions: Record<TaskStatus, TaskStatus[]> = {
  backlog: ['todo'],
  todo: ['inProgress', 'backlog'],
  inProgress: ['review', 'todo'],
  review: ['done', 'inProgress'],
  done: [], // Terminal state
};

/**
 * Check if a task status transition is valid
 */
export function isValidTaskStatusTransition(
  from: TaskStatus,
  to: TaskStatus
): boolean {
  return validTaskStatusTransitions[from].includes(to);
}

/**
 * Get available next statuses from current status
 */
export function getAvailableTaskStatuses(current: TaskStatus): TaskStatus[] {
  return validTaskStatusTransitions[current];
}
