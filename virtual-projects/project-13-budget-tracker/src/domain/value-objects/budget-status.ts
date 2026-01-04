/**
 * BudgetStatus Value Object
 * Represents the budget consumption status of a category
 * 
 * Traces to: REQ-BT-022, REQ-BT-023
 * - normal: spending < 80%
 * - warning: 80% <= spending < 100%
 * - exceeded: spending >= 100%
 */
import { Money } from './money.js';

export type BudgetStatus = 'normal' | 'warning' | 'exceeded';

/**
 * Calculates the budget status based on spending vs limit
 * @param spending - Current spending amount
 * @param limit - Monthly budget limit
 * @returns BudgetStatus based on percentage thresholds
 */
export function calculateBudgetStatus(spending: Money, limit: Money): BudgetStatus {
  const percentage = spending.percentage(limit);
  
  if (percentage >= 100) {
    return 'exceeded';
  }
  if (percentage >= 80) {
    return 'warning';
  }
  return 'normal';
}

/**
 * Gets a human-readable description for a budget status
 */
export function getBudgetStatusDescription(status: BudgetStatus): string {
  switch (status) {
    case 'normal':
      return '予算内';
    case 'warning':
      return '予算警告（80%超過）';
    case 'exceeded':
      return '予算超過';
  }
}
