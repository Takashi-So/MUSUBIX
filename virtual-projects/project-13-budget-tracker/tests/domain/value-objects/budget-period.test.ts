/**
 * BudgetPeriod Value Object Tests
 * Traces to: REQ-001 Section 2.2
 */
import { describe, it, expect } from 'vitest';
import { BudgetPeriod } from '../../../src/domain/value-objects/budget-period';

describe('BudgetPeriod Value Object', () => {
  describe('fromYearMonth', () => {
    it('should create BudgetPeriod with valid year and month', () => {
      const result = BudgetPeriod.fromYearMonth(2026, 1);
      expect(result.isOk()).toBe(true);
      expect(result.unwrap().toString()).toBe('2026-01');
    });

    it('should reject month less than 1', () => {
      const result = BudgetPeriod.fromYearMonth(2026, 0);
      expect(result.isErr()).toBe(true);
    });

    it('should reject month greater than 12', () => {
      const result = BudgetPeriod.fromYearMonth(2026, 13);
      expect(result.isErr()).toBe(true);
    });

    it('should accept month 1 (January)', () => {
      const result = BudgetPeriod.fromYearMonth(2026, 1);
      expect(result.isOk()).toBe(true);
    });

    it('should accept month 12 (December)', () => {
      const result = BudgetPeriod.fromYearMonth(2026, 12);
      expect(result.isOk()).toBe(true);
    });
  });

  describe('current', () => {
    it('should create BudgetPeriod for current month', () => {
      const period = BudgetPeriod.current();
      const now = new Date();
      expect(period.toString()).toBe(
        `${now.getFullYear()}-${String(now.getMonth() + 1).padStart(2, '0')}`
      );
    });
  });

  describe('fromDate', () => {
    it('should create BudgetPeriod from Date', () => {
      const date = new Date(2026, 0, 15); // January 15, 2026
      const period = BudgetPeriod.fromDate(date);
      expect(period.toString()).toBe('2026-01');
    });

    it('should handle end of month correctly', () => {
      const date = new Date(2026, 1, 28); // February 28, 2026
      const period = BudgetPeriod.fromDate(date);
      expect(period.toString()).toBe('2026-02');
    });
  });

  describe('getStartDate', () => {
    it('should return first day of month at 00:00:00', () => {
      const period = BudgetPeriod.fromYearMonth(2026, 1).unwrap();
      const start = period.getStartDate();
      expect(start.getFullYear()).toBe(2026);
      expect(start.getMonth()).toBe(0); // January = 0
      expect(start.getDate()).toBe(1);
      expect(start.getHours()).toBe(0);
      expect(start.getMinutes()).toBe(0);
      expect(start.getSeconds()).toBe(0);
    });
  });

  describe('getEndDate', () => {
    it('should return last day of January', () => {
      const period = BudgetPeriod.fromYearMonth(2026, 1).unwrap();
      const end = period.getEndDate();
      expect(end.getDate()).toBe(31);
    });

    it('should return last day of February (non-leap year)', () => {
      const period = BudgetPeriod.fromYearMonth(2025, 2).unwrap();
      const end = period.getEndDate();
      expect(end.getDate()).toBe(28);
    });

    it('should return last day of February (leap year)', () => {
      const period = BudgetPeriod.fromYearMonth(2024, 2).unwrap();
      const end = period.getEndDate();
      expect(end.getDate()).toBe(29);
    });

    it('should set time to 23:59:59.999', () => {
      const period = BudgetPeriod.fromYearMonth(2026, 1).unwrap();
      const end = period.getEndDate();
      expect(end.getHours()).toBe(23);
      expect(end.getMinutes()).toBe(59);
      expect(end.getSeconds()).toBe(59);
      expect(end.getMilliseconds()).toBe(999);
    });
  });

  describe('equals', () => {
    it('should return true for same year and month', () => {
      const p1 = BudgetPeriod.fromYearMonth(2026, 1).unwrap();
      const p2 = BudgetPeriod.fromYearMonth(2026, 1).unwrap();
      expect(p1.equals(p2)).toBe(true);
    });

    it('should return false for different month', () => {
      const p1 = BudgetPeriod.fromYearMonth(2026, 1).unwrap();
      const p2 = BudgetPeriod.fromYearMonth(2026, 2).unwrap();
      expect(p1.equals(p2)).toBe(false);
    });

    it('should return false for different year', () => {
      const p1 = BudgetPeriod.fromYearMonth(2026, 1).unwrap();
      const p2 = BudgetPeriod.fromYearMonth(2025, 1).unwrap();
      expect(p1.equals(p2)).toBe(false);
    });
  });

  describe('toString', () => {
    it('should format as YYYY-MM', () => {
      const period = BudgetPeriod.fromYearMonth(2026, 3).unwrap();
      expect(period.toString()).toBe('2026-03');
    });

    it('should pad single digit months', () => {
      const period = BudgetPeriod.fromYearMonth(2026, 1).unwrap();
      expect(period.toString()).toBe('2026-01');
    });
  });
});
