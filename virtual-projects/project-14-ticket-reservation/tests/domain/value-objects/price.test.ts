/**
 * Price Value Object Tests
 * Traces to: REQ-TR-010
 */
import { describe, it, expect } from 'vitest';
import { createPrice, addPrices, multiplyPrice } from '../../../src/domain/value-objects/price.js';

describe('Price Value Object', () => {
  describe('createPrice', () => {
    it('should create valid price within range', () => {
      const result = createPrice(5000);
      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.amount).toBe(5000);
        expect(result.value.currency).toBe('JPY');
      }
    });

    it('should reject price below minimum (100 JPY)', () => {
      const result = createPrice(99);
      expect(result.isErr()).toBe(true);
      if (result.isErr()) {
        expect(result.error.message).toContain('100');
      }
    });

    it('should reject price above maximum (1,000,000 JPY)', () => {
      const result = createPrice(1000001);
      expect(result.isErr()).toBe(true);
      if (result.isErr()) {
        expect(result.error.message).toContain('1,000,000');
      }
    });

    it('should accept minimum price (100 JPY)', () => {
      const result = createPrice(100);
      expect(result.isOk()).toBe(true);
    });

    it('should accept maximum price (1,000,000 JPY)', () => {
      const result = createPrice(1000000);
      expect(result.isOk()).toBe(true);
    });

    it('should reject non-integer amounts', () => {
      const result = createPrice(100.5);
      expect(result.isErr()).toBe(true);
    });

    it('should reject negative amounts', () => {
      const result = createPrice(-100);
      expect(result.isErr()).toBe(true);
    });
  });

  describe('addPrices', () => {
    it('should add two prices correctly', () => {
      const p1 = createPrice(1000);
      const p2 = createPrice(2000);
      
      if (p1.isOk() && p2.isOk()) {
        const result = addPrices(p1.value, p2.value);
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.amount).toBe(3000);
        }
      }
    });

    it('should reject sum exceeding maximum', () => {
      const p1 = createPrice(900000);
      const p2 = createPrice(200000);
      
      if (p1.isOk() && p2.isOk()) {
        const result = addPrices(p1.value, p2.value);
        expect(result.isErr()).toBe(true);
      }
    });
  });

  describe('multiplyPrice', () => {
    it('should multiply price by quantity', () => {
      const price = createPrice(5000);
      
      if (price.isOk()) {
        const result = multiplyPrice(price.value, 3);
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.amount).toBe(15000);
        }
      }
    });

    it('should reject zero quantity', () => {
      const price = createPrice(5000);
      
      if (price.isOk()) {
        const result = multiplyPrice(price.value, 0);
        expect(result.isErr()).toBe(true);
      }
    });

    it('should reject result exceeding maximum', () => {
      const price = createPrice(500000);
      
      if (price.isOk()) {
        const result = multiplyPrice(price.value, 3);
        expect(result.isErr()).toBe(true);
      }
    });
  });
});
