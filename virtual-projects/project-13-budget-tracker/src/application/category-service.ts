/**
 * CategoryService
 * Application service for budget category management
 * 
 * Traces to: REQ-BT-001, REQ-BT-002, REQ-BT-003, REQ-BT-004
 */
import { Result, ok, err, DomainError } from '../shared/result.js';
import { Money } from '../domain/value-objects/money.js';
import { BudgetPeriod } from '../domain/value-objects/budget-period.js';
import { BudgetStatus, calculateBudgetStatus } from '../domain/value-objects/budget-status.js';
import {
  Category,
  CategoryId,
  UserId,
  CreateCategoryInput as EntityInput,
  UpdateCategoryInput,
  createCategory,
  updateCategory,
  archiveCategory,
} from '../domain/entities/category.js';
import { CategoryRepository, ExpenseRepository } from '../domain/repositories/interfaces.js';

// ============================================================================
// DTOs
// ============================================================================

export interface CreateCategoryInput {
  name: string;
  description: string;
  monthlyLimit: number;
}

export interface CategoryWithSpending extends Category {
  currentMonthSpending: Money;
  budgetStatus: BudgetStatus;
}

// ============================================================================
// Service (BP-DESIGN-003)
// ============================================================================

export class CategoryService {
  constructor(
    private readonly categoryRepository: CategoryRepository,
    private readonly expenseRepository: ExpenseRepository
  ) {}

  /**
   * Creates a new budget category
   * Traces to: REQ-BT-001
   */
  async create(
    userId: string,
    input: CreateCategoryInput
  ): Promise<Result<Category, DomainError>> {
    // Check for duplicate name
    const exists = await this.categoryRepository.existsByNameAndUserId(
      input.name,
      userId as UserId
    );
    if (exists) {
      return err(new DomainError(`Category "${input.name}" already exists`));
    }

    // Create category entity
    const entityInput: EntityInput = {
      userId,
      name: input.name,
      description: input.description,
      monthlyLimit: input.monthlyLimit,
    };

    const result = createCategory(entityInput);
    if (result.isErr()) {
      return err(new DomainError(result.unwrapErr().message));
    }

    const category = result.unwrap();
    await this.categoryRepository.save(category);

    return ok(category);
  }

  /**
   * Lists all active categories with current spending
   * Traces to: REQ-BT-002
   */
  async list(userId: string): Promise<CategoryWithSpending[]> {
    const categories = await this.categoryRepository.findActiveByUserId(userId as UserId);
    const currentPeriod = BudgetPeriod.current();

    const result: CategoryWithSpending[] = [];

    for (const category of categories) {
      const spending = await this.expenseRepository.sumByCategory(
        category.id,
        currentPeriod
      );

      result.push({
        ...category,
        currentMonthSpending: spending,
        budgetStatus: calculateBudgetStatus(spending, category.monthlyLimit),
      });
    }

    return result;
  }

  /**
   * Updates a category
   * Traces to: REQ-BT-003
   */
  async update(
    userId: string,
    categoryId: CategoryId,
    input: UpdateCategoryInput
  ): Promise<Result<Category, DomainError>> {
    const category = await this.categoryRepository.findById(categoryId);

    if (!category) {
      return err(new DomainError('Category not found'));
    }

    if (category.userId !== userId) {
      return err(new DomainError('Access denied'));
    }

    // Check for duplicate name if name is being changed
    if (input.name && input.name !== category.name) {
      const exists = await this.categoryRepository.existsByNameAndUserId(
        input.name,
        userId as UserId
      );
      if (exists) {
        return err(new DomainError(`Category "${input.name}" already exists`));
      }
    }

    const result = updateCategory(category, input);
    if (result.isErr()) {
      return err(new DomainError(result.unwrapErr().message));
    }

    const updated = result.unwrap();
    await this.categoryRepository.save(updated);

    return ok(updated);
  }

  /**
   * Archives a category (logical delete)
   * Traces to: REQ-BT-004
   */
  async archive(
    userId: string,
    categoryId: CategoryId
  ): Promise<Result<void, DomainError>> {
    const category = await this.categoryRepository.findById(categoryId);

    if (!category) {
      return err(new DomainError('Category not found'));
    }

    if (category.userId !== userId) {
      return err(new DomainError('Access denied'));
    }

    const result = archiveCategory(category);
    if (result.isErr()) {
      return err(new DomainError(result.unwrapErr().message));
    }

    await this.categoryRepository.save(result.unwrap());

    return ok(undefined);
  }

  /**
   * Gets a single category by ID
   */
  async getById(
    userId: string,
    categoryId: CategoryId
  ): Promise<Result<CategoryWithSpending, DomainError>> {
    const category = await this.categoryRepository.findById(categoryId);

    if (!category) {
      return err(new DomainError('Category not found'));
    }

    if (category.userId !== userId) {
      return err(new DomainError('Access denied'));
    }

    const currentPeriod = BudgetPeriod.current();
    const spending = await this.expenseRepository.sumByCategory(
      category.id,
      currentPeriod
    );

    return ok({
      ...category,
      currentMonthSpending: spending,
      budgetStatus: calculateBudgetStatus(spending, category.monthlyLimit),
    });
  }
}
