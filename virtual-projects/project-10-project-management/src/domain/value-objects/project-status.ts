/**
 * Project Status Value Object
 * 
 * @see REQ-PM-PRJ-003 - ステータス遷移
 * @see DES-PM-001 Section 3.2.2
 * @see TSK-PM-001 - Value Objects実装
 */

export type ProjectStatus = 'planning' | 'active' | 'onHold' | 'completed' | 'archived';

/**
 * Valid project status transitions
 * @see BP-DESIGN-001 - Status Transition Map
 */
export const validProjectStatusTransitions: Record<ProjectStatus, ProjectStatus[]> = {
  planning: ['active', 'archived'],
  active: ['onHold', 'completed', 'archived'],
  onHold: ['active', 'archived'],
  completed: ['archived'],
  archived: [], // Terminal state - no transitions allowed
};

/**
 * Check if a status transition is valid
 */
export function isValidProjectStatusTransition(
  from: ProjectStatus,
  to: ProjectStatus
): boolean {
  return validProjectStatusTransitions[from].includes(to);
}

/**
 * Get available next statuses from current status
 */
export function getAvailableProjectStatuses(current: ProjectStatus): ProjectStatus[] {
  return validProjectStatusTransitions[current];
}
