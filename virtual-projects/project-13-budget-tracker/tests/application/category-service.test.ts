/**
 * CategoryService Tests
 * Traces to: REQ-BT-001, REQ-BT-002, REQ-BT-003, REQ-BT-004
 */
import { describe, it, expect, beforeEach, vi } from 'vitest';
import { CategoryService } from '../../src/application/category-service.js';
import { CategoryRepository, ExpenseRepository } from '../../src/domain/repositories/interfaces.js';
import { resetCategoryCounter } from '../../src/domain/entities/category.js';
import { Money } from '../../src/domain/value-objects/money.js';
import { BudgetPeriod } from '../../src/domain/value-objects/budget-period.js';

// Mock repositories
function createMockCategoryRepository(): CategoryRepository {
  const categories = new Map();
  return {
    save: vi.fn(async (category) => {
      categories.set(category.id, category);
    }),
    findById: vi.fn(async (id) => categories.get(id) || null),
    findByUserId: vi.fn(async (userId) => 
      Array.from(categories.values()).filter((c: any) => c.userId === userId)
    ),
    findActiveByUserId: vi.fn(async (userId) =>
      Array.from(categories.values()).filter((c: any) => c.userId === userId && c.status === 'active')
    ),
    existsByNameAndUserId: vi.fn(async (name, userId) =>
      Array.from(categories.values()).some((c: any) => c.name === name && c.userId === userId && c.status === 'active')
    ),
  };
}

function createMockExpenseRepository(): ExpenseRepository {
  return {
    save: vi.fn(),
    findById: vi.fn(),
    findByFilter: vi.fn(),
    sumByCategory: vi.fn(async () => Money.zero()),
    findByCategoryAndPeriod: vi.fn(async () => []),
  };
}

describe('CategoryService', () => {
  let service: CategoryService;
  let categoryRepo: CategoryRepository;
  let expenseRepo: ExpenseRepository;

  beforeEach(() => {
    resetCategoryCounter();
    categoryRepo = createMockCategoryRepository();
    expenseRepo = createMockExpenseRepository();
    service = new CategoryService(categoryRepo, expenseRepo);
  });

  describe('create', () => {
    it('should create a category with valid input', async () => {
      const result = await service.create('USR-A1B2C3D4', {
        name: '食費',
        description: '日常の食料品',
        monthlyLimit: 50000,
      });

      expect(result.isOk()).toBe(true);
      const category = result.unwrap();
      expect(category.name).toBe('食費');
      expect(category.monthlyLimit.toNumber()).toBe(50000);
      expect(categoryRepo.save).toHaveBeenCalled();
    });

    it('should reject duplicate category name for same user', async () => {
      // First create succeeds
      await service.create('USR-A1B2C3D4', {
        name: '食費',
        description: 'test',
        monthlyLimit: 50000,
      });

      // Second create with same name fails
      const result = await service.create('USR-A1B2C3D4', {
        name: '食費',
        description: 'test',
        monthlyLimit: 30000,
      });

      expect(result.isErr()).toBe(true);
      expect(result.unwrapErr().message).toContain('already exists');
    });

    it('should allow same category name for different users', async () => {
      await service.create('USR-A1B2C3D4', {
        name: '食費',
        description: 'test',
        monthlyLimit: 50000,
      });

      const result = await service.create('USR-X9Y8Z7W6', {
        name: '食費',
        description: 'test',
        monthlyLimit: 30000,
      });

      expect(result.isOk()).toBe(true);
    });
  });

  describe('list', () => {
    it('should return categories with spending amounts', async () => {
      // Create a category first
      await service.create('USR-A1B2C3D4', {
        name: '食費',
        description: 'test',
        monthlyLimit: 50000,
      });

      const categories = await service.list('USR-A1B2C3D4');

      expect(categories.length).toBe(1);
      expect(categories[0].name).toBe('食費');
      expect(categories[0].currentMonthSpending).toBeDefined();
      expect(categories[0].budgetStatus).toBeDefined();
    });

    it('should only return active categories', async () => {
      await service.create('USR-A1B2C3D4', {
        name: '食費',
        description: 'test',
        monthlyLimit: 50000,
      });

      const categories = await service.list('USR-A1B2C3D4');
      expect(categories.every(c => c.status === 'active')).toBe(true);
    });
  });

  describe('update', () => {
    it('should update category name', async () => {
      const createResult = await service.create('USR-A1B2C3D4', {
        name: '食費',
        description: 'test',
        monthlyLimit: 50000,
      });
      const categoryId = createResult.unwrap().id;

      const updateResult = await service.update('USR-A1B2C3D4', categoryId, {
        name: '食料品',
      });

      expect(updateResult.isOk()).toBe(true);
      expect(updateResult.unwrap().name).toBe('食料品');
    });

    it('should update monthly limit', async () => {
      const createResult = await service.create('USR-A1B2C3D4', {
        name: '食費',
        description: 'test',
        monthlyLimit: 50000,
      });
      const categoryId = createResult.unwrap().id;

      const updateResult = await service.update('USR-A1B2C3D4', categoryId, {
        monthlyLimit: 60000,
      });

      expect(updateResult.isOk()).toBe(true);
      expect(updateResult.unwrap().monthlyLimit.toNumber()).toBe(60000);
    });

    it('should reject update for non-existent category', async () => {
      const result = await service.update('USR-A1B2C3D4', 'CAT-00000000-999' as any, {
        name: 'test',
      });

      expect(result.isErr()).toBe(true);
      expect(result.unwrapErr().message).toContain('not found');
    });
  });

  describe('archive', () => {
    it('should archive an active category', async () => {
      const createResult = await service.create('USR-A1B2C3D4', {
        name: '食費',
        description: 'test',
        monthlyLimit: 50000,
      });
      const categoryId = createResult.unwrap().id;

      const archiveResult = await service.archive('USR-A1B2C3D4', categoryId);

      expect(archiveResult.isOk()).toBe(true);
    });

    it('should reject archive for non-existent category', async () => {
      const result = await service.archive('USR-A1B2C3D4', 'CAT-00000000-999' as any);

      expect(result.isErr()).toBe(true);
    });
  });
});
