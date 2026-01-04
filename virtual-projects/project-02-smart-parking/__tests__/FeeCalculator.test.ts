/**
 * Fee Calculator Tests
 * @requirement REQ-FEE-001, REQ-FEE-002, REQ-FEE-003
 * @design DES-PARKING-001 Section 4
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { FeeCalculator } from '../src/services/FeeCalculator.js';
import { DiscountCode } from '../src/types/Fee.js';

describe('FeeCalculator', () => {
  let calculator: FeeCalculator;

  beforeEach(() => {
    calculator = new FeeCalculator();
  });

  describe('calculate', () => {
    it('should be free within 30 minutes', () => {
      // @requirement REQ-FEE-001: 最初の30分無料
      const entryTime = new Date('2024-01-01T10:00:00');
      const exitTime = new Date('2024-01-01T10:25:00'); // 25分後

      const result = calculator.calculate(entryTime, exitTime);

      expect(result.durationMinutes).toBe(25);
      expect(result.baseFee).toBe(0);
      expect(result.finalFee).toBe(0);
    });

    it('should charge 200 yen for 31-60 minutes', () => {
      // @requirement REQ-FEE-002: 30分ごとに200円
      const entryTime = new Date('2024-01-01T10:00:00');
      const exitTime = new Date('2024-01-01T10:45:00'); // 45分後

      const result = calculator.calculate(entryTime, exitTime);

      expect(result.durationMinutes).toBe(45);
      expect(result.baseFee).toBe(200);
      expect(result.finalFee).toBe(200);
    });

    it('should charge 400 yen for 61-90 minutes', () => {
      const entryTime = new Date('2024-01-01T10:00:00');
      const exitTime = new Date('2024-01-01T11:15:00'); // 75分後

      const result = calculator.calculate(entryTime, exitTime);

      expect(result.durationMinutes).toBe(75);
      expect(result.baseFee).toBe(400); // 75-30=45分 -> ceil(45/30)=2単位 -> 400円
      expect(result.finalFee).toBe(400);
    });

    it('should apply daily maximum of 2000 yen', () => {
      // @requirement REQ-FEE-003: 24時間上限2000円
      const entryTime = new Date('2024-01-01T10:00:00');
      const exitTime = new Date('2024-01-02T08:00:00'); // 22時間後

      const result = calculator.calculate(entryTime, exitTime);

      expect(result.dailyMaxApplied).toBe(true);
      expect(result.finalFee).toBe(2000);
    });

    it('should apply multi-day maximum', () => {
      const entryTime = new Date('2024-01-01T10:00:00');
      const exitTime = new Date('2024-01-03T14:00:00'); // 52時間後

      const result = calculator.calculate(entryTime, exitTime);

      // 52時間 = ceil(52/24) = 3日 -> 最大6000円
      expect(result.dailyMaxApplied).toBe(true);
      expect(result.finalFee).toBe(6000);
    });

    it('should apply valid discount code', () => {
      const entryTime = new Date('2024-01-01T10:00:00');
      const exitTime = new Date('2024-01-01T12:00:00'); // 2時間後

      const discountCode: DiscountCode = {
        code: 'SHOP50',
        discountPercent: 50,
        validFrom: new Date('2024-01-01'),
        validTo: new Date('2024-12-31'),
        shopName: 'Test Shop',
      };

      const result = calculator.calculate(entryTime, exitTime, discountCode);

      // 2時間 = 120分 -> 120-30=90分 -> ceil(90/30)=3単位 -> 600円
      expect(result.baseFee).toBe(600);
      expect(result.discountAmount).toBe(300); // 50% off
      expect(result.finalFee).toBe(300);
      expect(result.discountCode).toBe('SHOP50');
    });

    it('should not apply expired discount code', () => {
      const entryTime = new Date('2024-01-01T10:00:00');
      const exitTime = new Date('2024-01-01T12:00:00');

      const expiredCode: DiscountCode = {
        code: 'EXPIRED',
        discountPercent: 50,
        validFrom: new Date('2023-01-01'),
        validTo: new Date('2023-12-31'), // 期限切れ
        shopName: 'Test Shop',
      };

      const result = calculator.calculate(entryTime, exitTime, expiredCode);

      expect(result.discountAmount).toBe(0);
      expect(result.finalFee).toBe(600);
    });
  });

  describe('estimate', () => {
    it('should estimate current fee', () => {
      const entryTime = new Date(Date.now() - 60 * 60 * 1000); // 1時間前

      const estimated = calculator.estimate(entryTime);

      // 60分 -> 60-30=30分 -> ceil(30/30)=1単位 -> 200円
      expect(estimated).toBe(200);
    });
  });

  describe('updateFeeTable', () => {
    it('should allow updating fee table', () => {
      calculator.updateFeeTable({ ratePerUnit: 300 });

      const entryTime = new Date('2024-01-01T10:00:00');
      const exitTime = new Date('2024-01-01T10:45:00');

      const result = calculator.calculate(entryTime, exitTime);

      expect(result.baseFee).toBe(300); // 新料金
    });
  });

  describe('getFeeTable', () => {
    it('should return current fee table', () => {
      const table = calculator.getFeeTable();

      expect(table.freeMinutes).toBe(30);
      expect(table.ratePerUnit).toBe(200);
      expect(table.unitMinutes).toBe(30);
      expect(table.dailyMax).toBe(2000);
    });
  });
});
