/**
 * Expense Entity Tests
 * Traces to: REQ-BT-010, REQ-BT-011, REQ-BT-012, REQ-BT-013
 */
import { describe, it, expect, beforeEach } from 'vitest';
import {
  createExpense,
  generateExpenseId,
  resetExpenseCounter,
  isValidExpenseTransition,
} from '../../../src/domain/entities/expense';

describe('Expense Entity', () => {
  beforeEach(() => {
    resetExpenseCounter();
  });

  describe('createExpense', () => {
    it('should create an expense with valid input', () => {
      const result = createExpense({
        userId: 'USR-A1B2C3D4',
        categoryId: 'CAT-20260104-001',
        amount: 1200,
        date: '2026-01-04',
        description: 'ランチ',
      });

      expect(result.isOk()).toBe(true);
      const expense = result.unwrap();
      expect(expense.amount.toNumber()).toBe(1200);
      expect(expense.description).toBe('ランチ');
      expect(expense.status).toBe('active');
    });

    it('should reject invalid amount', () => {
      const result = createExpense({
        userId: 'USR-A1B2C3D4',
        categoryId: 'CAT-20260104-001',
        amount: 0,
        date: '2026-01-04',
        description: 'test',
      });

      expect(result.isErr()).toBe(true);
    });

    it('should reject future date', () => {
      const futureDate = new Date();
      futureDate.setDate(futureDate.getDate() + 10);
      
      const result = createExpense({
        userId: 'USR-A1B2C3D4',
        categoryId: 'CAT-20260104-001',
        amount: 1000,
        date: futureDate.toISOString().slice(0, 10),
        description: 'test',
      });

      expect(result.isErr()).toBe(true);
      expect(result.unwrapErr().message).toContain('future');
    });

    it('should reject date older than 365 days', () => {
      const oldDate = new Date();
      oldDate.setDate(oldDate.getDate() - 400);
      
      const result = createExpense({
        userId: 'USR-A1B2C3D4',
        categoryId: 'CAT-20260104-001',
        amount: 1000,
        date: oldDate.toISOString().slice(0, 10),
        description: 'test',
      });

      expect(result.isErr()).toBe(true);
      expect(result.unwrapErr().message).toContain('365');
    });

    it('should accept today date', () => {
      const today = new Date().toISOString().slice(0, 10);
      
      const result = createExpense({
        userId: 'USR-A1B2C3D4',
        categoryId: 'CAT-20260104-001',
        amount: 1000,
        date: today,
        description: 'test',
      });

      expect(result.isOk()).toBe(true);
    });
  });

  describe('generateExpenseId', () => {
    it('should generate ID in EXP-YYYYMMDD-NNN format', () => {
      const id = generateExpenseId();
      expect(id).toMatch(/^EXP-\d{8}-\d{3}$/);
    });

    it('should increment counter for each call', () => {
      const id1 = generateExpenseId();
      const id2 = generateExpenseId();
      expect(id1).toMatch(/-001$/);
      expect(id2).toMatch(/-002$/);
    });
  });

  describe('ExpenseStatus transitions', () => {
    it('should allow transition from active to archived', () => {
      expect(isValidExpenseTransition('active', 'archived')).toBe(true);
    });

    it('should not allow transition from archived to active', () => {
      expect(isValidExpenseTransition('archived', 'active')).toBe(false);
    });
  });
});
