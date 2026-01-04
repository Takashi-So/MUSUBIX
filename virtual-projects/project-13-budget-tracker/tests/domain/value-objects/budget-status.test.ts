/**
 * BudgetStatus Value Object Tests
 * Traces to: REQ-BT-022, REQ-BT-023
 */
import { describe, it, expect } from 'vitest';
import { calculateBudgetStatus, BudgetStatus } from '../../../src/domain/value-objects/budget-status';
import { Money } from '../../../src/domain/value-objects/money';

describe('BudgetStatus', () => {
  describe('calculateBudgetStatus', () => {
    it('should return "normal" when spending is below 80%', () => {
      const spending = Money.create(7900).unwrap();
      const limit = Money.create(10000).unwrap();
      expect(calculateBudgetStatus(spending, limit)).toBe('normal');
    });

    it('should return "warning" when spending is exactly 80%', () => {
      const spending = Money.create(8000).unwrap();
      const limit = Money.create(10000).unwrap();
      expect(calculateBudgetStatus(spending, limit)).toBe('warning');
    });

    it('should return "warning" when spending is between 80% and 99%', () => {
      const spending = Money.create(9500).unwrap();
      const limit = Money.create(10000).unwrap();
      expect(calculateBudgetStatus(spending, limit)).toBe('warning');
    });

    it('should return "exceeded" when spending is exactly 100%', () => {
      const spending = Money.create(10000).unwrap();
      const limit = Money.create(10000).unwrap();
      expect(calculateBudgetStatus(spending, limit)).toBe('exceeded');
    });

    it('should return "exceeded" when spending exceeds 100%', () => {
      const spending = Money.create(12000).unwrap();
      const limit = Money.create(10000).unwrap();
      expect(calculateBudgetStatus(spending, limit)).toBe('exceeded');
    });

    it('should return "normal" when spending is zero', () => {
      const spending = Money.zero();
      const limit = Money.create(10000).unwrap();
      expect(calculateBudgetStatus(spending, limit)).toBe('normal');
    });

    it('should handle edge case at 79%', () => {
      const spending = Money.create(79).unwrap();
      const limit = Money.create(100).unwrap();
      expect(calculateBudgetStatus(spending, limit)).toBe('normal');
    });

    it('should handle edge case at 99%', () => {
      const spending = Money.create(99).unwrap();
      const limit = Money.create(100).unwrap();
      expect(calculateBudgetStatus(spending, limit)).toBe('warning');
    });
  });
});
