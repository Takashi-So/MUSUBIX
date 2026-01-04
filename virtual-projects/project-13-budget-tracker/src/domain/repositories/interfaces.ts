/**
 * Repository Interfaces
 * Ports for data access (Hexagonal Architecture)
 */
import { Money } from '../value-objects/money.js';
import { BudgetPeriod } from '../value-objects/budget-period.js';
import { Category, CategoryId, UserId } from '../entities/category.js';
import { Expense, ExpenseId, ExpenseFilter } from '../entities/expense.js';

// ============================================================================
// Category Repository
// ============================================================================

export interface CategoryRepository {
  save(category: Category): Promise<void>;
  findById(id: CategoryId): Promise<Category | null>;
  findByUserId(userId: UserId): Promise<Category[]>;
  findActiveByUserId(userId: UserId): Promise<Category[]>;
  existsByNameAndUserId(name: string, userId: UserId): Promise<boolean>;
}

// ============================================================================
// Expense Repository
// ============================================================================

export interface ExpenseRepository {
  save(expense: Expense): Promise<void>;
  findById(id: ExpenseId): Promise<Expense | null>;
  findByFilter(userId: UserId, filter: ExpenseFilter): Promise<Expense[]>;
  sumByCategory(categoryId: CategoryId, period: BudgetPeriod): Promise<Money>;
  findByCategoryAndPeriod(categoryId: CategoryId, period: BudgetPeriod): Promise<Expense[]>;
}

// ============================================================================
// Alert Types
// ============================================================================

export type AlertId = string & { readonly __brand: unique symbol };
export type AlertType = 'warning' | 'exceeded';
export type AlertStatus = 'unread' | 'read';

export interface Alert {
  id: AlertId;
  userId: UserId;
  categoryId: CategoryId;
  type: AlertType;
  budgetPeriod: BudgetPeriod;
  status: AlertStatus;
  createdAt: Date;
  readAt?: Date;
}

// ============================================================================
// Alert Repository
// ============================================================================

export interface AlertRepository {
  save(alert: Alert): Promise<void>;
  findUnreadByUser(userId: UserId): Promise<Alert[]>;
  findById(id: AlertId): Promise<Alert | null>;
  existsForCategoryAndType(
    categoryId: CategoryId,
    type: AlertType,
    period: BudgetPeriod
  ): Promise<boolean>;
}
