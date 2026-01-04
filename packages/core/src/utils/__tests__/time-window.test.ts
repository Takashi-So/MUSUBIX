import { describe, it, expect } from 'vitest';
import { TimeWindowValidator } from '../time-window.js';

describe('TimeWindowValidator', () => {
  const validator = new TimeWindowValidator();

  describe('isWithinWindow', () => {
    it('should return true when within window', () => {
      const reference = new Date('2026-01-04T10:00:00');
      const checkTime = new Date('2026-01-04T09:50:00'); // 10分前
      const result = validator.isWithinWindow(reference, checkTime, {
        beforeMinutes: 15,
        afterMinutes: 15,
      });
      expect(result).toBe(true);
    });

    it('should return true when within after window', () => {
      const reference = new Date('2026-01-04T10:00:00');
      const checkTime = new Date('2026-01-04T10:10:00'); // 10分後
      const result = validator.isWithinWindow(reference, checkTime, {
        beforeMinutes: 15,
        afterMinutes: 15,
      });
      expect(result).toBe(true);
    });

    it('should return false when outside window', () => {
      const reference = new Date('2026-01-04T10:00:00');
      const checkTime = new Date('2026-01-04T09:30:00'); // 30分前
      const result = validator.isWithinWindow(reference, checkTime, {
        beforeMinutes: 15,
        afterMinutes: 15,
      });
      expect(result).toBe(false);
    });

    it('should return true at exact boundary', () => {
      const reference = new Date('2026-01-04T10:00:00');
      const checkTime = new Date('2026-01-04T09:45:00'); // 15分前（境界）
      const result = validator.isWithinWindow(reference, checkTime, {
        beforeMinutes: 15,
        afterMinutes: 15,
      });
      expect(result).toBe(true);
    });
  });

  describe('validateWindow', () => {
    it('should return detailed window info', () => {
      const reference = new Date('2026-01-04T10:00:00');
      const checkTime = new Date('2026-01-04T09:50:00');
      const result = validator.validateWindow(reference, checkTime, {
        beforeMinutes: 15,
        afterMinutes: 15,
      });
      expect(result.isValid).toBe(true);
      expect(result.windowStart.getHours()).toBe(9);
      expect(result.windowStart.getMinutes()).toBe(45);
      expect(result.windowEnd.getHours()).toBe(10);
      expect(result.windowEnd.getMinutes()).toBe(15);
    });
  });

  describe('isBeforeDeadline', () => {
    it('should return true when before deadline', () => {
      const reference = new Date('2026-01-04T14:00:00');
      const checkTime = new Date('2026-01-04T11:00:00');
      const result = validator.isBeforeDeadline(reference, checkTime, {
        hoursBeforeDeadline: 1,
      });
      expect(result).toBe(true);
    });

    it('should return false when after deadline', () => {
      const reference = new Date('2026-01-04T14:00:00');
      const checkTime = new Date('2026-01-04T13:30:00');
      const result = validator.isBeforeDeadline(reference, checkTime, {
        hoursBeforeDeadline: 1,
      });
      expect(result).toBe(false);
    });

    it('should accept minutes before deadline', () => {
      const reference = new Date('2026-01-04T14:00:00');
      const checkTime = new Date('2026-01-04T13:45:00');
      const result = validator.isBeforeDeadline(reference, checkTime, {
        minutesBeforeDeadline: 30,
      });
      expect(result).toBe(false);
    });
  });

  describe('validateDeadline', () => {
    it('should return detailed deadline info', () => {
      const reference = new Date('2026-01-04T14:00:00');
      const checkTime = new Date('2026-01-04T11:00:00');
      const result = validator.validateDeadline(reference, checkTime, {
        hoursBeforeDeadline: 1,
      });
      expect(result.isValid).toBe(true);
      expect(result.deadline.getHours()).toBe(13);
      expect(result.hoursRemaining).toBe(2);
      expect(result.minutesRemaining).toBe(120);
    });
  });

  describe('hoursUntil', () => {
    it('should calculate hours until reference time', () => {
      const reference = new Date('2026-01-04T14:00:00');
      const checkTime = new Date('2026-01-04T11:00:00');
      expect(validator.hoursUntil(reference, checkTime)).toBe(3);
    });

    it('should return negative for past times', () => {
      const reference = new Date('2026-01-04T10:00:00');
      const checkTime = new Date('2026-01-04T12:00:00');
      expect(validator.hoursUntil(reference, checkTime)).toBe(-2);
    });
  });

  describe('minutesUntil', () => {
    it('should calculate minutes until reference time', () => {
      const reference = new Date('2026-01-04T10:30:00');
      const checkTime = new Date('2026-01-04T10:00:00');
      expect(validator.minutesUntil(reference, checkTime)).toBe(30);
    });
  });

  describe('minutesSince', () => {
    it('should calculate minutes since reference time', () => {
      const reference = new Date('2026-01-04T10:00:00');
      const checkTime = new Date('2026-01-04T10:30:00');
      expect(validator.minutesSince(reference, checkTime)).toBe(30);
    });
  });

  describe('isPast', () => {
    it('should return true for past times', () => {
      const time = new Date('2026-01-04T10:00:00');
      const reference = new Date('2026-01-04T12:00:00');
      expect(validator.isPast(time, reference)).toBe(true);
    });

    it('should return false for future times', () => {
      const time = new Date('2026-01-04T14:00:00');
      const reference = new Date('2026-01-04T12:00:00');
      expect(validator.isPast(time, reference)).toBe(false);
    });
  });

  describe('isFuture', () => {
    it('should return true for future times', () => {
      const time = new Date('2026-01-04T14:00:00');
      const reference = new Date('2026-01-04T12:00:00');
      expect(validator.isFuture(time, reference)).toBe(true);
    });
  });

  describe('isSameDay', () => {
    it('should return true for same day', () => {
      const date1 = new Date('2026-01-04T10:00:00');
      const date2 = new Date('2026-01-04T20:00:00');
      expect(validator.isSameDay(date1, date2)).toBe(true);
    });

    it('should return false for different days', () => {
      const date1 = new Date('2026-01-04T10:00:00');
      const date2 = new Date('2026-01-05T10:00:00');
      expect(validator.isSameDay(date1, date2)).toBe(false);
    });
  });

  describe('isWithinBusinessHours', () => {
    it('should return true within business hours', () => {
      const time = new Date('2026-01-04T14:00:00');
      expect(validator.isWithinBusinessHours(time, 9, 18)).toBe(true);
    });

    it('should return false before business hours', () => {
      const time = new Date('2026-01-04T08:00:00');
      expect(validator.isWithinBusinessHours(time, 9, 18)).toBe(false);
    });

    it('should return false after business hours', () => {
      const time = new Date('2026-01-04T19:00:00');
      expect(validator.isWithinBusinessHours(time, 9, 18)).toBe(false);
    });

    it('should return true at start of business hours', () => {
      const time = new Date('2026-01-04T09:00:00');
      expect(validator.isWithinBusinessHours(time, 9, 18)).toBe(true);
    });

    it('should return false at end of business hours', () => {
      const time = new Date('2026-01-04T18:00:00');
      expect(validator.isWithinBusinessHours(time, 9, 18)).toBe(false);
    });
  });
});
