/**
 * Expense Entity
 * Represents an individual expense record
 * 
 * Traces to: REQ-BT-010, REQ-BT-011, REQ-BT-012, REQ-BT-013
 */
import { Result, ok, err, ValidationError } from '../../shared/result.js';
import { Money } from '../value-objects/money.js';
import { CategoryId, UserId } from './category.js';

// ============================================================================
// Types
// ============================================================================

export type ExpenseId = string & { readonly __brand: unique symbol };

export type ExpenseStatus = 'active' | 'archived';

export interface Expense {
  id: ExpenseId;
  userId: UserId;
  categoryId: CategoryId;
  amount: Money;
  date: Date;
  description: string;
  status: ExpenseStatus;
  createdAt: Date;
  updatedAt: Date;
}

// ============================================================================
// Input DTOs (BP-CODE-001)
// ============================================================================

export interface RecordExpenseInput {
  userId: string;
  categoryId: string;
  amount: number;
  date: string; // ISO 8601 format (YYYY-MM-DD)
  description: string;
}

export interface UpdateExpenseInput {
  categoryId?: string;
  amount?: number;
  date?: string;
  description?: string;
}

export interface ExpenseFilter {
  categoryId?: string;
  startDate?: string;
  endDate?: string;
  status?: ExpenseStatus;
}

// ============================================================================
// Status Transition Map (BP-DESIGN-001)
// ============================================================================

const expenseStatusTransitions: Record<ExpenseStatus, ExpenseStatus[]> = {
  active: ['archived'],
  archived: [],
};

export function isValidExpenseTransition(
  from: ExpenseStatus,
  to: ExpenseStatus
): boolean {
  return expenseStatusTransitions[from].includes(to);
}

// ============================================================================
// ID Generation (BP-CODE-002, BP-TEST-001)
// ============================================================================

let expenseCounter = 0;

export function generateExpenseId(): ExpenseId {
  const date = new Date().toISOString().slice(0, 10).replace(/-/g, '');
  expenseCounter++;
  return `EXP-${date}-${String(expenseCounter).padStart(3, '0')}` as ExpenseId;
}

export function resetExpenseCounter(): void {
  expenseCounter = 0;
}

// ============================================================================
// Factory
// ============================================================================

export function createExpense(
  input: RecordExpenseInput
): Result<Expense, ValidationError> {
  // Validate amount
  const moneyResult = Money.create(input.amount);
  if (moneyResult.isErr()) {
    return err(moneyResult.unwrapErr());
  }

  // Parse and validate date
  const expenseDate = new Date(input.date);
  if (isNaN(expenseDate.getTime())) {
    return err(new ValidationError('Invalid date format'));
  }

  // Check date is not in the future
  const today = new Date();
  today.setHours(23, 59, 59, 999);
  if (expenseDate > today) {
    return err(new ValidationError('Expense date cannot be in the future'));
  }

  // Check date is within 365 days
  const oneYearAgo = new Date();
  oneYearAgo.setDate(oneYearAgo.getDate() - 365);
  oneYearAgo.setHours(0, 0, 0, 0);
  if (expenseDate < oneYearAgo) {
    return err(new ValidationError('Expense date must be within the past 365 days'));
  }

  const now = new Date();

  const expense: Expense = {
    id: generateExpenseId(),
    userId: input.userId as UserId,
    categoryId: input.categoryId as CategoryId,
    amount: moneyResult.unwrap(),
    date: expenseDate,
    description: input.description,
    status: 'active',
    createdAt: now,
    updatedAt: now,
  };

  return ok(expense);
}

// ============================================================================
// Update
// ============================================================================

export function updateExpense(
  expense: Expense,
  input: UpdateExpenseInput
): Result<Expense, ValidationError> {
  let updated = { ...expense };

  if (input.categoryId !== undefined) {
    updated.categoryId = input.categoryId as CategoryId;
  }

  if (input.amount !== undefined) {
    const moneyResult = Money.create(input.amount);
    if (moneyResult.isErr()) {
      return err(moneyResult.unwrapErr());
    }
    updated.amount = moneyResult.unwrap();
  }

  if (input.date !== undefined) {
    const newDate = new Date(input.date);
    if (isNaN(newDate.getTime())) {
      return err(new ValidationError('Invalid date format'));
    }
    updated.date = newDate;
  }

  if (input.description !== undefined) {
    updated.description = input.description;
  }

  updated.updatedAt = new Date();

  return ok(updated);
}

// ============================================================================
// Archive
// ============================================================================

export function archiveExpense(
  expense: Expense
): Result<Expense, ValidationError> {
  if (!isValidExpenseTransition(expense.status, 'archived')) {
    return err(new ValidationError(`Cannot archive expense with status: ${expense.status}`));
  }

  return ok({
    ...expense,
    status: 'archived',
    updatedAt: new Date(),
  });
}
