/**
 * BudgetPeriod Value Object
 * Represents a budget period (calendar month)
 * 
 * Traces to: REQ-001 Section 2.2
 * - Period type: Calendar month (1st to last day)
 * - Timezone: Asia/Tokyo (JST)
 */
import { Result, ok, err, ValidationError } from '../../shared/result.js';

export class BudgetPeriod {
  private constructor(
    private readonly year: number,
    private readonly month: number // 1-12
  ) {}

  /**
   * Creates BudgetPeriod for the current month
   */
  static current(): BudgetPeriod {
    const now = new Date();
    return new BudgetPeriod(now.getFullYear(), now.getMonth() + 1);
  }

  /**
   * Creates BudgetPeriod from a Date
   */
  static fromDate(date: Date): BudgetPeriod {
    return new BudgetPeriod(date.getFullYear(), date.getMonth() + 1);
  }

  /**
   * Creates BudgetPeriod from year and month with validation
   * @param year - The year
   * @param month - The month (1-12)
   */
  static fromYearMonth(year: number, month: number): Result<BudgetPeriod, ValidationError> {
    if (month < 1 || month > 12) {
      return err(new ValidationError('Month must be between 1 and 12'));
    }
    return ok(new BudgetPeriod(year, month));
  }

  /**
   * Gets the start date of the period (first day at 00:00:00)
   */
  getStartDate(): Date {
    return new Date(this.year, this.month - 1, 1, 0, 0, 0, 0);
  }

  /**
   * Gets the end date of the period (last day at 23:59:59.999)
   */
  getEndDate(): Date {
    // Day 0 of next month = last day of current month
    return new Date(this.year, this.month, 0, 23, 59, 59, 999);
  }

  /**
   * Checks equality with another BudgetPeriod
   */
  equals(other: BudgetPeriod): boolean {
    return this.year === other.year && this.month === other.month;
  }

  /**
   * Returns the year
   */
  getYear(): number {
    return this.year;
  }

  /**
   * Returns the month (1-12)
   */
  getMonth(): number {
    return this.month;
  }

  /**
   * Formats as YYYY-MM string
   */
  toString(): string {
    return `${this.year}-${String(this.month).padStart(2, '0')}`;
  }
}
