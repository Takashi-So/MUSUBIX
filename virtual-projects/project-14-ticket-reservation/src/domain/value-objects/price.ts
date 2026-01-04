/**
 * Price Value Object
 * Traces to: REQ-TR-001, REQ-TR-014
 * 
 * Immutable representation of ticket price in JPY.
 * Valid range: 100 - 1,000,000 JPY
 */
import { Result, ok, err, ValidationError } from '../../shared/result.js';

const MIN_PRICE = 100;
const MAX_PRICE = 1_000_000;

export interface Price {
  readonly amount: number;
  readonly currency: 'JPY';
}

/**
 * Create a Price with validation
 */
export function createPrice(amount: number): Result<Price, ValidationError> {
  if (!Number.isInteger(amount)) {
    return err(new ValidationError('Price must be an integer'));
  }
  if (amount < MIN_PRICE) {
    return err(new ValidationError(
      `Price must be at least ${MIN_PRICE.toLocaleString()} JPY`
    ));
  }
  if (amount > MAX_PRICE) {
    return err(new ValidationError(
      `Price must not exceed ${MAX_PRICE.toLocaleString()} JPY`
    ));
  }
  return ok({ amount, currency: 'JPY' });
}

/**
 * Add two prices
 */
export function addPrices(p1: Price, p2: Price): Result<Price, ValidationError> {
  const sum = p1.amount + p2.amount;
  if (sum > MAX_PRICE) {
    return err(new ValidationError(
      `Sum exceeds maximum price of ${MAX_PRICE.toLocaleString()} JPY`
    ));
  }
  return ok({ amount: sum, currency: 'JPY' });
}

/**
 * Multiply price by quantity
 */
export function multiplyPrice(price: Price, quantity: number): Result<Price, ValidationError> {
  if (quantity < 1) {
    return err(new ValidationError('Quantity must be at least 1'));
  }
  const total = price.amount * quantity;
  if (total > MAX_PRICE) {
    return err(new ValidationError(
      `Total exceeds maximum price of ${MAX_PRICE.toLocaleString()} JPY`
    ));
  }
  return ok({ amount: total, currency: 'JPY' });
}

/**
 * Format price as Japanese Yen string
 */
export function formatPrice(price: Price): string {
  return `¥${price.amount.toLocaleString('ja-JP')}`;
}

/**
 * Check equality
 */
export function priceEquals(p1: Price, p2: Price): boolean {
  return p1.amount === p2.amount;
}
