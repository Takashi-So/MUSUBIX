/**
 * Money Value Object
 * REQ-EMPLOYEE-001-F030 対応
 */

import { Money, Currency } from './types.js';

/**
 * Money作成
 * @param amount 金額
 * @param currency 通貨（デフォルト: JPY）
 * @throws Error 金額が負の場合
 */
export function createMoney(amount: number, currency: Currency = 'JPY'): Money {
  if (amount < 0) {
    throw new Error('Amount cannot be negative');
  }
  return { amount, currency };
}

/**
 * Money加算
 * @param a Money
 * @param b Money
 * @throws Error 通貨が異なる場合
 */
export function addMoney(a: Money, b: Money): Money {
  if (a.currency !== b.currency) {
    throw new Error(`Currency mismatch: ${a.currency} vs ${b.currency}`);
  }
  return createMoney(a.amount + b.amount, a.currency);
}

/**
 * Money減算
 * @param a Money
 * @param b Money
 * @throws Error 通貨が異なる場合
 * @throws Error 結果が負になる場合
 */
export function subtractMoney(a: Money, b: Money): Money {
  if (a.currency !== b.currency) {
    throw new Error(`Currency mismatch: ${a.currency} vs ${b.currency}`);
  }
  if (a.amount < b.amount) {
    throw new Error('Result cannot be negative');
  }
  return createMoney(a.amount - b.amount, a.currency);
}

/**
 * Money乗算
 * @param money Money
 * @param multiplier 乗数
 * @throws Error 乗数が負の場合
 */
export function multiplyMoney(money: Money, multiplier: number): Money {
  if (multiplier < 0) {
    throw new Error('Multiplier cannot be negative');
  }
  return createMoney(Math.round(money.amount * multiplier), money.currency);
}

/**
 * Money比較（大なり）
 */
export function isGreaterThan(a: Money, b: Money): boolean {
  if (a.currency !== b.currency) {
    throw new Error(`Currency mismatch: ${a.currency} vs ${b.currency}`);
  }
  return a.amount > b.amount;
}

/**
 * Money等価比較
 */
export function isEqual(a: Money, b: Money): boolean {
  return a.currency === b.currency && a.amount === b.amount;
}

/**
 * ゼロMoney作成
 */
export function zeroMoney(currency: Currency = 'JPY'): Money {
  return createMoney(0, currency);
}
