/**
 * Money Value Object Tests
 * Traces to: REQ-001 Section 2.1
 */
import { describe, it, expect } from 'vitest';
import { Money } from '../../../src/domain/value-objects/money';

describe('Money Value Object', () => {
  describe('create', () => {
    it('should create Money with valid amount', () => {
      const result = Money.create(1000);
      expect(result.isOk()).toBe(true);
      expect(result.unwrap().toNumber()).toBe(1000);
    });

    it('should reject amount less than 1', () => {
      const result = Money.create(0);
      expect(result.isErr()).toBe(true);
      expect(result.unwrapErr().message).toContain('between 1 and 999,999,999');
    });

    it('should reject amount greater than 999,999,999', () => {
      const result = Money.create(1_000_000_000);
      expect(result.isErr()).toBe(true);
    });

    it('should reject non-integer amounts', () => {
      const result = Money.create(100.5);
      expect(result.isErr()).toBe(true);
      expect(result.unwrapErr().message).toContain('integer');
    });

    it('should accept minimum value (1)', () => {
      const result = Money.create(1);
      expect(result.isOk()).toBe(true);
    });

    it('should accept maximum value (999,999,999)', () => {
      const result = Money.create(999_999_999);
      expect(result.isOk()).toBe(true);
    });
  });

  describe('zero', () => {
    it('should create zero Money', () => {
      const money = Money.zero();
      expect(money.toNumber()).toBe(0);
    });
  });

  describe('add', () => {
    it('should add two Money values', () => {
      const m1 = Money.create(1000).unwrap();
      const m2 = Money.create(500).unwrap();
      const result = m1.add(m2);
      expect(result.toNumber()).toBe(1500);
    });

    it('should add zero correctly', () => {
      const m1 = Money.create(1000).unwrap();
      const result = m1.add(Money.zero());
      expect(result.toNumber()).toBe(1000);
    });
  });

  describe('subtract', () => {
    it('should subtract two Money values', () => {
      const m1 = Money.create(1000).unwrap();
      const m2 = Money.create(300).unwrap();
      const result = m1.subtract(m2);
      expect(result.toNumber()).toBe(700);
    });

    it('should return zero when subtracting larger amount', () => {
      const m1 = Money.create(100).unwrap();
      const m2 = Money.create(500).unwrap();
      const result = m1.subtract(m2);
      expect(result.toNumber()).toBe(0);
    });
  });

  describe('percentage', () => {
    it('should calculate percentage correctly', () => {
      const spending = Money.create(800).unwrap();
      const total = Money.create(1000).unwrap();
      expect(spending.percentage(total)).toBe(80);
    });

    it('should return 0 when total is zero', () => {
      const spending = Money.create(100).unwrap();
      const total = Money.zero();
      expect(spending.percentage(total)).toBe(0);
    });

    it('should handle over 100%', () => {
      const spending = Money.create(1200).unwrap();
      const total = Money.create(1000).unwrap();
      expect(spending.percentage(total)).toBe(120);
    });

    it('should round to nearest integer', () => {
      const spending = Money.create(333).unwrap();
      const total = Money.create(1000).unwrap();
      expect(spending.percentage(total)).toBe(33);
    });
  });

  describe('equals', () => {
    it('should return true for equal amounts', () => {
      const m1 = Money.create(1000).unwrap();
      const m2 = Money.create(1000).unwrap();
      expect(m1.equals(m2)).toBe(true);
    });

    it('should return false for different amounts', () => {
      const m1 = Money.create(1000).unwrap();
      const m2 = Money.create(999).unwrap();
      expect(m1.equals(m2)).toBe(false);
    });
  });
});
