/**
 * Category Entity
 * Represents a budget category for organizing expenses
 * 
 * Traces to: REQ-BT-001, REQ-BT-002, REQ-BT-003, REQ-BT-004
 */
import { Result, ok, err, ValidationError } from '../../shared/result.js';
import { Money } from '../value-objects/money.js';

// ============================================================================
// Types
// ============================================================================

export type CategoryId = string & { readonly __brand: unique symbol };
export type UserId = string & { readonly __brand: unique symbol };

export type CategoryStatus = 'active' | 'archived';

export interface Category {
  id: CategoryId;
  userId: UserId;
  name: string;
  description: string;
  monthlyLimit: Money;
  status: CategoryStatus;
  createdAt: Date;
  updatedAt: Date;
}

// ============================================================================
// Input DTOs (BP-CODE-001)
// ============================================================================

export interface CreateCategoryInput {
  userId: string;
  name: string;
  description: string;
  monthlyLimit: number;
}

export interface UpdateCategoryInput {
  name?: string;
  description?: string;
  monthlyLimit?: number;
}

// ============================================================================
// Status Transition Map (BP-DESIGN-001)
// ============================================================================

const categoryStatusTransitions: Record<CategoryStatus, CategoryStatus[]> = {
  active: ['archived'],
  archived: [], // No transitions from archived (v1.0)
};

export function isValidCategoryTransition(
  from: CategoryStatus,
  to: CategoryStatus
): boolean {
  return categoryStatusTransitions[from].includes(to);
}

// ============================================================================
// ID Generation (BP-CODE-002, BP-TEST-001)
// ============================================================================

let categoryCounter = 0;

export function generateCategoryId(): CategoryId {
  const date = new Date().toISOString().slice(0, 10).replace(/-/g, '');
  categoryCounter++;
  return `CAT-${date}-${String(categoryCounter).padStart(3, '0')}` as CategoryId;
}

export function resetCategoryCounter(): void {
  categoryCounter = 0;
}

// ============================================================================
// Factory
// ============================================================================

export function createCategory(
  input: CreateCategoryInput
): Result<Category, ValidationError> {
  // Validate name
  if (input.name.length < 1 || input.name.length > 50) {
    return err(new ValidationError('Category name must be 1-50 characters'));
  }

  // Validate and create Money
  const moneyResult = Money.create(input.monthlyLimit);
  if (moneyResult.isErr()) {
    return err(moneyResult.unwrapErr());
  }

  const now = new Date();

  const category: Category = {
    id: generateCategoryId(),
    userId: input.userId as UserId,
    name: input.name,
    description: input.description,
    monthlyLimit: moneyResult.unwrap(),
    status: 'active',
    createdAt: now,
    updatedAt: now,
  };

  return ok(category);
}

// ============================================================================
// Update
// ============================================================================

export function updateCategory(
  category: Category,
  input: UpdateCategoryInput
): Result<Category, ValidationError> {
  let updatedCategory = { ...category };

  if (input.name !== undefined) {
    if (input.name.length < 1 || input.name.length > 50) {
      return err(new ValidationError('Category name must be 1-50 characters'));
    }
    updatedCategory.name = input.name;
  }

  if (input.description !== undefined) {
    updatedCategory.description = input.description;
  }

  if (input.monthlyLimit !== undefined) {
    const moneyResult = Money.create(input.monthlyLimit);
    if (moneyResult.isErr()) {
      return err(moneyResult.unwrapErr());
    }
    updatedCategory.monthlyLimit = moneyResult.unwrap();
  }

  updatedCategory.updatedAt = new Date();

  return ok(updatedCategory);
}

// ============================================================================
// Archive
// ============================================================================

export function archiveCategory(
  category: Category
): Result<Category, ValidationError> {
  if (!isValidCategoryTransition(category.status, 'archived')) {
    return err(new ValidationError(`Cannot archive category with status: ${category.status}`));
  }

  return ok({
    ...category,
    status: 'archived',
    updatedAt: new Date(),
  });
}
