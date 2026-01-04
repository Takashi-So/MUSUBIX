/**
 * Money Value Object
 * Represents monetary amounts in JPY (Japanese Yen)
 * 
 * Traces to: REQ-001 Section 2.1
 * - Currency: JPY (fixed for v1.0)
 * - Minimum unit: 1 yen (no decimals)
 * - Maximum value: 999,999,999 yen
 */
import { Result, ok, err, ValidationError } from '../../shared/result.js';

export class Money {
  private constructor(private readonly amount: number) {}

  /**
   * Creates a Money instance with validation
   * @param amount - Amount in yen (must be integer, 1-999,999,999)
   */
  static create(amount: number): Result<Money, ValidationError> {
    if (!Number.isInteger(amount)) {
      return err(new ValidationError('Amount must be an integer'));
    }
    if (amount < 1 || amount > 999_999_999) {
      return err(new ValidationError('Amount must be between 1 and 999,999,999'));
    }
    return ok(new Money(amount));
  }

  /**
   * Creates a zero Money instance (for calculations)
   */
  static zero(): Money {
    return new Money(0);
  }

  /**
   * Adds two Money values
   */
  add(other: Money): Money {
    return new Money(this.amount + other.amount);
  }

  /**
   * Subtracts another Money value (returns 0 if result would be negative)
   */
  subtract(other: Money): Money {
    return new Money(Math.max(0, this.amount - other.amount));
  }

  /**
   * Calculates the percentage this amount represents of a total
   * @param total - The total to compare against
   * @returns Percentage as integer (e.g., 80 for 80%)
   */
  percentage(total: Money): number {
    if (total.amount === 0) return 0;
    return Math.round((this.amount / total.amount) * 100);
  }

  /**
   * Returns the numeric value
   */
  toNumber(): number {
    return this.amount;
  }

  /**
   * Checks equality with another Money instance
   */
  equals(other: Money): boolean {
    return this.amount === other.amount;
  }

  /**
   * Formats as currency string (e.g., "¥1,000")
   */
  toString(): string {
    return `¥${this.amount.toLocaleString('ja-JP')}`;
  }
}
