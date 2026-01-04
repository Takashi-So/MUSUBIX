/**
 * Value Objects Tests
 * @task TSK-DLV-001
 */

import { describe, it, expect } from 'vitest';
import { Money, GeoLocation, OperatingHours, DayOfWeek } from '../../src/domain/shared';

describe('Money', () => {
  describe('creation', () => {
    it('should create Money with amount and currency', () => {
      const money = new Money(1000, 'JPY');
      expect(money.amount).toBe(1000);
      expect(money.currency).toBe('JPY');
    });

    it('should default to JPY currency', () => {
      const money = new Money(500);
      expect(money.currency).toBe('JPY');
    });

    it('should reject negative amounts', () => {
      expect(() => new Money(-100)).toThrow('Amount cannot be negative');
    });

    it('should allow zero amount', () => {
      const money = new Money(0);
      expect(money.amount).toBe(0);
    });
  });

  describe('operations', () => {
    it('should add two Money values', () => {
      const a = new Money(1000);
      const b = new Money(500);
      const result = a.add(b);
      expect(result.amount).toBe(1500);
    });

    it('should subtract Money values', () => {
      const a = new Money(1000);
      const b = new Money(300);
      const result = a.subtract(b);
      expect(result.amount).toBe(700);
    });

    it('should multiply Money by factor', () => {
      const money = new Money(500);
      const result = money.multiply(3);
      expect(result.amount).toBe(1500);
    });

    it('should check equality', () => {
      const a = new Money(1000, 'JPY');
      const b = new Money(1000, 'JPY');
      const c = new Money(1000, 'USD');
      expect(a.equals(b)).toBe(true);
      expect(a.equals(c)).toBe(false);
    });

    it('should reject operations with different currencies', () => {
      const jpy = new Money(1000, 'JPY');
      const usd = new Money(10, 'USD');
      expect(() => jpy.add(usd)).toThrow('Currency mismatch');
    });
  });
});

describe('GeoLocation', () => {
  describe('creation', () => {
    it('should create valid GeoLocation', () => {
      const location = new GeoLocation(35.6762, 139.6503);
      expect(location.latitude).toBe(35.6762);
      expect(location.longitude).toBe(139.6503);
    });

    it('should reject invalid latitude (< -90)', () => {
      expect(() => new GeoLocation(-91, 0)).toThrow('Invalid latitude');
    });

    it('should reject invalid latitude (> 90)', () => {
      expect(() => new GeoLocation(91, 0)).toThrow('Invalid latitude');
    });

    it('should reject invalid longitude (< -180)', () => {
      expect(() => new GeoLocation(0, -181)).toThrow('Invalid longitude');
    });

    it('should reject invalid longitude (> 180)', () => {
      expect(() => new GeoLocation(0, 181)).toThrow('Invalid longitude');
    });
  });

  describe('distanceTo', () => {
    it('should calculate distance between two points', () => {
      // Tokyo Station
      const tokyo = new GeoLocation(35.6812, 139.7671);
      // Shibuya Station
      const shibuya = new GeoLocation(35.6580, 139.7016);
      
      const distance = tokyo.distanceTo(shibuya);
      // Approximately 6.4 km
      expect(distance).toBeGreaterThan(6);
      expect(distance).toBeLessThan(7);
    });

    it('should return 0 for same location', () => {
      const location = new GeoLocation(35.6762, 139.6503);
      expect(location.distanceTo(location)).toBe(0);
    });
  });
});

describe('OperatingHours', () => {
  describe('creation', () => {
    it('should create valid operating hours', () => {
      const hours = new OperatingHours(DayOfWeek.MONDAY, '09:00', '22:00');
      expect(hours.dayOfWeek).toBe(DayOfWeek.MONDAY);
      expect(hours.openTime).toBe('09:00');
      expect(hours.closeTime).toBe('22:00');
    });

    it('should reject invalid time format', () => {
      expect(() => new OperatingHours(DayOfWeek.MONDAY, '9:00', '22:00')).toThrow('Invalid time format');
    });

    it('should reject close time before open time', () => {
      expect(() => new OperatingHours(DayOfWeek.MONDAY, '22:00', '09:00')).toThrow('Close time must be after open time');
    });
  });

  describe('isOpenAt', () => {
    it('should return true when within operating hours', () => {
      const hours = new OperatingHours(DayOfWeek.MONDAY, '09:00', '22:00');
      expect(hours.isOpenAt('12:00')).toBe(true);
      expect(hours.isOpenAt('09:00')).toBe(true);
      expect(hours.isOpenAt('21:59')).toBe(true);
    });

    it('should return false when outside operating hours', () => {
      const hours = new OperatingHours(DayOfWeek.MONDAY, '09:00', '22:00');
      expect(hours.isOpenAt('08:59')).toBe(false);
      expect(hours.isOpenAt('22:00')).toBe(false);
      expect(hours.isOpenAt('23:00')).toBe(false);
    });
  });
});
