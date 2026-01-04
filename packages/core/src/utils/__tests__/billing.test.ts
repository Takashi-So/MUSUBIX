import { describe, it, expect } from 'vitest';
import { BillingCalculator } from '../billing.js';

describe('BillingCalculator', () => {
  describe('constructor', () => {
    it('should use default config values', () => {
      const calc = new BillingCalculator();
      const config = calc.getConfig();
      expect(config.slotMinutes).toBe(15);
      expect(config.fullRefundHours).toBe(2);
      expect(config.partialRefundPercentage).toBe(50);
      expect(config.decimalPlaces).toBe(0);
    });

    it('should accept custom config', () => {
      const calc = new BillingCalculator({
        slotMinutes: 30,
        fullRefundHours: 4,
        partialRefundPercentage: 75,
        decimalPlaces: 2,
      });
      const config = calc.getConfig();
      expect(config.slotMinutes).toBe(30);
      expect(config.partialRefundPercentage).toBe(75);
    });
  });

  describe('calculateFee', () => {
    const calc = new BillingCalculator({ slotMinutes: 15 });

    it('should calculate fee for full hour', () => {
      const start = new Date('2026-01-04T10:00:00');
      const end = new Date('2026-01-04T11:00:00');
      const fee = calc.calculateFee(2000, start, end);
      expect(fee).toBe(2000);
    });

    it('should calculate fee for 2 hours', () => {
      const start = new Date('2026-01-04T10:00:00');
      const end = new Date('2026-01-04T12:00:00');
      const fee = calc.calculateFee(2000, start, end);
      expect(fee).toBe(4000);
    });

    it('should calculate fee in slot increments', () => {
      const start = new Date('2026-01-04T10:00:00');
      const end = new Date('2026-01-04T10:45:00'); // 45分 = 3スロット
      const fee = calc.calculateFee(2000, start, end);
      expect(fee).toBe(1500); // 2000/4 * 3 = 1500
    });
  });

  describe('calculateFeeDetailed', () => {
    const calc = new BillingCalculator({ slotMinutes: 15 });

    it('should return detailed fee info', () => {
      const start = new Date('2026-01-04T10:00:00');
      const end = new Date('2026-01-04T10:45:00');
      const result = calc.calculateFeeDetailed(2000, start, end);
      expect(result.amount).toBe(1500);
      expect(result.slots).toBe(3);
      expect(result.pricePerSlot).toBe(500);
      expect(result.totalMinutes).toBe(45);
    });
  });

  describe('calculateFeeByMinutes', () => {
    const calc = new BillingCalculator({ slotMinutes: 15 });

    it('should calculate fee by minutes', () => {
      const fee = calc.calculateFeeByMinutes(2000, 60);
      expect(fee).toBe(2000);
    });

    it('should round up to nearest slot', () => {
      const fee = calc.calculateFeeByMinutes(2000, 20); // 20分 → 2スロット
      expect(fee).toBe(1000);
    });
  });

  describe('calculateRefund', () => {
    const calc = new BillingCalculator({
      fullRefundHours: 2,
      partialRefundPercentage: 50,
    });

    it('should calculate full refund for early cancellation', () => {
      const reservationStart = new Date('2026-01-04T14:00:00');
      const cancelTime = new Date('2026-01-04T11:00:00'); // 3時間前
      const result = calc.calculateRefund(4000, reservationStart, cancelTime);
      expect(result.amount).toBe(4000);
      expect(result.percentage).toBe(100);
      expect(result.type).toBe('full');
    });

    it('should calculate partial refund for late cancellation', () => {
      const reservationStart = new Date('2026-01-04T14:00:00');
      const cancelTime = new Date('2026-01-04T13:00:00'); // 1時間前
      const result = calc.calculateRefund(4000, reservationStart, cancelTime);
      expect(result.amount).toBe(2000);
      expect(result.percentage).toBe(50);
      expect(result.type).toBe('partial');
    });

    it('should return no refund for cancellation after start', () => {
      const reservationStart = new Date('2026-01-04T14:00:00');
      const cancelTime = new Date('2026-01-04T14:30:00'); // 開始後
      const result = calc.calculateRefund(4000, reservationStart, cancelTime);
      expect(result.amount).toBe(0);
      expect(result.percentage).toBe(0);
      expect(result.type).toBe('none');
    });

    it('should return hours until start', () => {
      const reservationStart = new Date('2026-01-04T14:00:00');
      const cancelTime = new Date('2026-01-04T11:00:00');
      const result = calc.calculateRefund(4000, reservationStart, cancelTime);
      expect(result.hoursUntilStart).toBe(3);
    });
  });

  describe('calculateExtensionFee', () => {
    const calc = new BillingCalculator({ slotMinutes: 15 });

    it('should calculate extension fee', () => {
      const fee = calc.calculateExtensionFee(2000, 30);
      expect(fee).toBe(1000);
    });
  });

  describe('calculateProRata', () => {
    const calc = new BillingCalculator();

    it('should calculate pro-rata for partial month', () => {
      const fee = calc.calculateProRata(30000, 10, 30);
      expect(fee).toBe(10000);
    });

    it('should use default 30 days per month', () => {
      const fee = calc.calculateProRata(30000, 15);
      expect(fee).toBe(15000);
    });
  });

  describe('decimal places', () => {
    it('should round to specified decimal places', () => {
      const calc = new BillingCalculator({
        slotMinutes: 15,
        decimalPlaces: 2,
      });
      const start = new Date('2026-01-04T10:00:00');
      const end = new Date('2026-01-04T10:30:00'); // 30分 = 2スロット
      const fee = calc.calculateFee(1999, start, end); // 1999/4 * 2 = 999.5
      expect(fee).toBe(999.5);
    });
  });
});
