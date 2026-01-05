/**
 * Priority Value Object
 * 
 * @see REQ-PM-TSK-001 - タスク作成
 * @see DES-PM-001 Section 3.2.2
 * @see TSK-PM-001 - Value Objects実装
 */

export type Priority = 'low' | 'medium' | 'high';

/**
 * Priority weights for sorting
 */
export const priorityWeight: Record<Priority, number> = {
  high: 3,
  medium: 2,
  low: 1,
};

/**
 * Compare priorities for sorting
 * Returns positive if a > b, negative if a < b, 0 if equal
 */
export function comparePriority(a: Priority, b: Priority): number {
  return priorityWeight[a] - priorityWeight[b];
}

/**
 * Get priority label for display
 */
export function getPriorityLabel(priority: Priority): string {
  const labels: Record<Priority, string> = {
    high: '🔴 High',
    medium: '🟡 Medium',
    low: '🟢 Low',
  };
  return labels[priority];
}
