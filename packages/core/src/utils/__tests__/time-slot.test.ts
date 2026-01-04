import { describe, it, expect } from 'vitest';
import { TimeSlotService } from '../time-slot.js';

describe('TimeSlotService', () => {
  describe('constructor', () => {
    it('should use default config values', () => {
      const service = new TimeSlotService();
      const config = service.getConfig();
      expect(config.slotMinutes).toBe(15);
      expect(config.bufferMinutes).toBe(5);
      expect(config.minDurationMinutes).toBe(30);
      expect(config.maxDurationMinutes).toBe(480);
    });

    it('should accept custom config', () => {
      const service = new TimeSlotService({
        slotMinutes: 30,
        bufferMinutes: 10,
        minDurationMinutes: 60,
        maxDurationMinutes: 240,
      });
      const config = service.getConfig();
      expect(config.slotMinutes).toBe(30);
      expect(config.bufferMinutes).toBe(10);
    });
  });

  describe('validateDuration', () => {
    const service = new TimeSlotService({
      slotMinutes: 15,
      minDurationMinutes: 30,
      maxDurationMinutes: 120,
    });

    it('should accept valid duration', () => {
      const start = new Date('2026-01-04T10:00:00');
      const end = new Date('2026-01-04T11:00:00');
      expect(() => service.validateDuration(start, end)).not.toThrow();
    });

    it('should reject duration below minimum', () => {
      const start = new Date('2026-01-04T10:00:00');
      const end = new Date('2026-01-04T10:15:00'); // 15分
      expect(() => service.validateDuration(start, end)).toThrow('Minimum duration');
    });

    it('should reject duration above maximum', () => {
      const start = new Date('2026-01-04T10:00:00');
      const end = new Date('2026-01-04T13:00:00'); // 3時間
      expect(() => service.validateDuration(start, end)).toThrow('Maximum duration');
    });

    it('should reject duration not in slot increments', () => {
      const start = new Date('2026-01-04T10:00:00');
      const end = new Date('2026-01-04T10:40:00'); // 40分
      expect(() => service.validateDuration(start, end)).toThrow('15 minute increments');
    });

    it('should reject start time after end time', () => {
      const start = new Date('2026-01-04T11:00:00');
      const end = new Date('2026-01-04T10:00:00');
      expect(() => service.validateDuration(start, end)).toThrow('Start time must be before');
    });
  });

  describe('hasConflict', () => {
    const service = new TimeSlotService({
      bufferMinutes: 5,
    });

    it('should detect direct overlap', () => {
      const existing = {
        start: new Date('2026-01-04T10:00:00'),
        end: new Date('2026-01-04T11:00:00'),
      };
      const newSlot = {
        start: new Date('2026-01-04T10:30:00'),
        end: new Date('2026-01-04T11:30:00'),
      };
      expect(service.hasConflict(existing.start, existing.end, newSlot.start, newSlot.end)).toBe(true);
    });

    it('should detect buffer violation', () => {
      const existing = {
        start: new Date('2026-01-04T10:00:00'),
        end: new Date('2026-01-04T11:00:00'),
      };
      const newSlot = {
        start: new Date('2026-01-04T11:03:00'), // 3分後（バッファ5分以内）
        end: new Date('2026-01-04T12:00:00'),
      };
      expect(service.hasConflict(existing.start, existing.end, newSlot.start, newSlot.end)).toBe(true);
    });

    it('should allow reservation after buffer', () => {
      const existing = {
        start: new Date('2026-01-04T10:00:00'),
        end: new Date('2026-01-04T11:00:00'),
      };
      const newSlot = {
        start: new Date('2026-01-04T11:06:00'), // 6分後（バッファ5分超過）
        end: new Date('2026-01-04T12:00:00'),
      };
      expect(service.hasConflict(existing.start, existing.end, newSlot.start, newSlot.end)).toBe(false);
    });
  });

  describe('checkConflict', () => {
    const service = new TimeSlotService({ bufferMinutes: 5 });

    it('should return detailed overlap info', () => {
      const existing = {
        start: new Date('2026-01-04T10:00:00'),
        end: new Date('2026-01-04T11:00:00'),
      };
      const newSlot = {
        start: new Date('2026-01-04T10:30:00'),
        end: new Date('2026-01-04T11:30:00'),
      };
      const result = service.checkConflict(existing.start, existing.end, newSlot.start, newSlot.end);
      expect(result.hasConflict).toBe(true);
      expect(result.conflictType).toBe('overlap');
      expect(result.overlapMinutes).toBe(30);
    });

    it('should return buffer_violation type', () => {
      const existing = {
        start: new Date('2026-01-04T10:00:00'),
        end: new Date('2026-01-04T11:00:00'),
      };
      const newSlot = {
        start: new Date('2026-01-04T11:03:00'),
        end: new Date('2026-01-04T12:00:00'),
      };
      const result = service.checkConflict(existing.start, existing.end, newSlot.start, newSlot.end);
      expect(result.hasConflict).toBe(true);
      expect(result.conflictType).toBe('buffer_violation');
    });
  });

  describe('generateSlots', () => {
    const service = new TimeSlotService({ slotMinutes: 15 });

    it('should generate correct number of slots', () => {
      const date = new Date('2026-01-04');
      const slots = service.generateSlots(date, 9, 12); // 3時間
      expect(slots).toHaveLength(12); // 3時間 × 4スロット
    });

    it('should set correct times', () => {
      const date = new Date('2026-01-04');
      const slots = service.generateSlots(date, 9, 10);
      expect(slots[0].startTime.getHours()).toBe(9);
      expect(slots[0].startTime.getMinutes()).toBe(0);
      expect(slots[0].endTime.getHours()).toBe(9);
      expect(slots[0].endTime.getMinutes()).toBe(15);
    });

    it('should mark all slots as available', () => {
      const date = new Date('2026-01-04');
      const slots = service.generateSlots(date, 9, 10);
      expect(slots.every((s) => s.isAvailable)).toBe(true);
    });
  });

  describe('getAvailableSlots', () => {
    const service = new TimeSlotService({ slotMinutes: 15, bufferMinutes: 0 });

    it('should mark conflicting slots as unavailable', () => {
      const date = new Date('2026-01-04');
      const slots = service.generateSlots(date, 9, 10);
      const reservations = [
        {
          startTime: new Date('2026-01-04T09:15:00'),
          endTime: new Date('2026-01-04T09:45:00'),
        },
      ];
      const available = service.getAvailableSlots(slots, reservations);
      expect(available[0].isAvailable).toBe(true); // 9:00-9:15
      expect(available[1].isAvailable).toBe(false); // 9:15-9:30
      expect(available[2].isAvailable).toBe(false); // 9:30-9:45
      expect(available[3].isAvailable).toBe(true); // 9:45-10:00
    });
  });

  describe('roundToSlot', () => {
    const service = new TimeSlotService({ slotMinutes: 15 });

    it('should round down by default', () => {
      const time = new Date('2026-01-04T10:07:00');
      const rounded = service.roundToSlot(time);
      expect(rounded.getMinutes()).toBe(0);
    });

    it('should round up when specified', () => {
      const time = new Date('2026-01-04T10:07:00');
      const rounded = service.roundToSlot(time, true);
      expect(rounded.getMinutes()).toBe(15);
    });
  });

  describe('getDurationMinutes', () => {
    const service = new TimeSlotService();

    it('should calculate duration in minutes', () => {
      const start = new Date('2026-01-04T10:00:00');
      const end = new Date('2026-01-04T11:30:00');
      expect(service.getDurationMinutes(start, end)).toBe(90);
    });
  });
});
