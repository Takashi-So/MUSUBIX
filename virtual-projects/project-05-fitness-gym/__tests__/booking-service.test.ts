/**
 * BookingService Unit Tests
 * @traces REQ-GYM-005, REQ-GYM-006, REQ-GYM-007, REQ-GYM-008
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  BookingService,
  IBookingRepository,
  IClassRepository,
  Booking,
  GymClass,
  BookingFilterOptions,
  WaitlistEntry,
} from '../src/booking-service';

// Mock Repositories
function createMockBookingRepository(): IBookingRepository {
  const bookings: Map<string, Booking> = new Map();
  const waitlist: WaitlistEntry[] = [];

  return {
    async save(booking: Booking): Promise<Booking> {
      bookings.set(booking.id, booking);
      return booking;
    },
    async findById(id: string): Promise<Booking | null> {
      return bookings.get(id) || null;
    },
    async findByMember(memberId: string, _filter?: BookingFilterOptions): Promise<Booking[]> {
      return Array.from(bookings.values()).filter((b) => b.memberId === memberId);
    },
    async findByResource(
      resourceType: string,
      resourceId: string,
      dateRange: { from: Date; to: Date },
    ): Promise<Booking[]> {
      return Array.from(bookings.values()).filter(
        (b) =>
          b.resourceType === resourceType &&
          b.resourceId === resourceId &&
          b.scheduledStart >= dateRange.from &&
          b.scheduledEnd <= dateRange.to,
      );
    },
    async update(id: string, data: Partial<Booking>): Promise<Booking> {
      const booking = bookings.get(id);
      if (!booking) throw new Error('Not found');
      const updated = { ...booking, ...data };
      bookings.set(id, updated);
      return updated;
    },
    async delete(id: string): Promise<boolean> {
      return bookings.delete(id);
    },
    async getWaitlist(classId: string): Promise<WaitlistEntry[]> {
      return waitlist.filter((w) => w.classId === classId);
    },
    async addToWaitlist(entry: WaitlistEntry): Promise<WaitlistEntry> {
      waitlist.push(entry);
      return entry;
    },
    async removeFromWaitlist(memberId: string, classId: string): Promise<boolean> {
      const index = waitlist.findIndex((w) => w.memberId === memberId && w.classId === classId);
      if (index >= 0) {
        waitlist.splice(index, 1);
        return true;
      }
      return false;
    },
  };
}

function createMockClassRepository(): IClassRepository {
  const classes: Map<string, GymClass> = new Map();

  const defaultClass: GymClass = {
    id: 'class-yoga-001',
    name: 'Morning Yoga',
    description: 'Relaxing morning yoga session',
    instructorId: 'trainer-001',
    capacity: 20,
    currentEnrollment: 0,
    duration: 60,
    difficulty: 'beginner',
    category: 'yoga',
    schedule: [{ dayOfWeek: 1, startTime: '09:00', endTime: '10:00', roomId: 'room-a' }],
  };
  classes.set(defaultClass.id, defaultClass);

  return {
    async findById(id: string): Promise<GymClass | null> {
      return classes.get(id) || null;
    },
    async findBySchedule(_date: Date): Promise<GymClass[]> {
      return Array.from(classes.values());
    },
    async findUpcoming(_days: number): Promise<GymClass[]> {
      return Array.from(classes.values());
    },
    async updateEnrollment(id: string, count: number): Promise<GymClass> {
      const gymClass = classes.get(id);
      if (!gymClass) throw new Error('Not found');
      const updated = { ...gymClass, currentEnrollment: count };
      classes.set(id, updated);
      return updated;
    },
  };
}

describe('BookingService', () => {
  let service: BookingService;
  let bookingRepository: IBookingRepository;
  let classRepository: IClassRepository;

  beforeEach(() => {
    bookingRepository = createMockBookingRepository();
    classRepository = createMockClassRepository();
    service = new BookingService(bookingRepository, classRepository);
  });

  describe('REQ-GYM-005: クラス予約', () => {
    it('THE BookingService SHALL create a class booking', async () => {
      const start = new Date();
      start.setHours(start.getHours() + 24);
      const end = new Date(start);
      end.setHours(end.getHours() + 1);

      const booking = await service.createBooking({
        memberId: 'member-001',
        resourceType: 'class',
        resourceId: 'class-yoga-001',
        scheduledStart: start,
        scheduledEnd: end,
      });

      expect(booking).toBeDefined();
      expect(booking.id).toMatch(/^BK-/);
      expect(booking.status).toBe('confirmed');
      expect(booking.memberId).toBe('member-001');
    });

    it('THE BookingService SHALL increment class enrollment on booking', async () => {
      const start = new Date();
      start.setHours(start.getHours() + 24);
      const end = new Date(start);
      end.setHours(end.getHours() + 1);

      await service.createBooking({
        memberId: 'member-001',
        resourceType: 'class',
        resourceId: 'class-yoga-001',
        scheduledStart: start,
        scheduledEnd: end,
      });

      const gymClass = await classRepository.findById('class-yoga-001');
      expect(gymClass?.currentEnrollment).toBe(1);
    });
  });

  describe('REQ-GYM-006: 予約キャンセル', () => {
    let booking: Booking;

    beforeEach(async () => {
      const start = new Date();
      start.setHours(start.getHours() + 24);
      const end = new Date(start);
      end.setHours(end.getHours() + 1);

      booking = await service.createBooking({
        memberId: 'member-001',
        resourceType: 'class',
        resourceId: 'class-yoga-001',
        scheduledStart: start,
        scheduledEnd: end,
      });
    });

    it('THE BookingService SHALL cancel a booking', async () => {
      const cancelled = await service.cancelBooking(booking.id, 'Schedule conflict');

      expect(cancelled.status).toBe('cancelled');
      expect(cancelled.cancellationReason).toBe('Schedule conflict');
    });

    it('THE BookingService SHALL NOT cancel already cancelled booking', async () => {
      await service.cancelBooking(booking.id);

      await expect(service.cancelBooking(booking.id)).rejects.toThrow(
        'Booking is already cancelled',
      );
    });

    it('THE BookingService SHALL decrement enrollment on cancellation', async () => {
      await service.cancelBooking(booking.id);

      const gymClass = await classRepository.findById('class-yoga-001');
      expect(gymClass?.currentEnrollment).toBe(0);
    });
  });

  describe('REQ-GYM-007: 予約変更', () => {
    let booking: Booking;

    beforeEach(async () => {
      const start = new Date();
      start.setHours(start.getHours() + 24);
      const end = new Date(start);
      end.setHours(end.getHours() + 1);

      booking = await service.createBooking({
        memberId: 'member-001',
        resourceType: 'equipment',
        resourceId: 'treadmill-001',
        scheduledStart: start,
        scheduledEnd: end,
      });
    });

    it('THE BookingService SHALL reschedule a booking', async () => {
      const newStart = new Date();
      newStart.setHours(newStart.getHours() + 48);
      const newEnd = new Date(newStart);
      newEnd.setHours(newEnd.getHours() + 1);

      const rescheduled = await service.rescheduleBooking(booking.id, newStart, newEnd);

      expect(rescheduled.scheduledStart).toEqual(newStart);
      expect(rescheduled.scheduledEnd).toEqual(newEnd);
    });

    it('THE BookingService SHALL NOT reschedule non-existent booking', async () => {
      const newStart = new Date();
      const newEnd = new Date(newStart);
      newEnd.setHours(newEnd.getHours() + 1);

      await expect(service.rescheduleBooking('non-existent', newStart, newEnd)).rejects.toThrow(
        'Booking not found',
      );
    });
  });

  describe('REQ-GYM-008: 空き状況確認', () => {
    it('THE BookingService SHALL return available time slots', async () => {
      const tomorrow = new Date();
      tomorrow.setDate(tomorrow.getDate() + 1);

      const slots = await service.checkAvailability('equipment', 'treadmill-001', tomorrow);

      expect(slots.length).toBeGreaterThan(0);
      expect(slots.every((s) => typeof s.available === 'boolean')).toBe(true);
    });

    it('THE BookingService SHALL mark booked slots as unavailable', async () => {
      const tomorrow = new Date();
      tomorrow.setDate(tomorrow.getDate() + 1);
      tomorrow.setHours(10, 0, 0, 0);

      const end = new Date(tomorrow);
      end.setHours(11, 0, 0, 0);

      await service.createBooking({
        memberId: 'member-001',
        resourceType: 'equipment',
        resourceId: 'treadmill-001',
        scheduledStart: tomorrow,
        scheduledEnd: end,
      });

      const slots = await service.checkAvailability('equipment', 'treadmill-001', tomorrow);
      const bookedSlot = slots.find(
        (s) => s.startTime.getHours() === 10 && s.startTime.getDate() === tomorrow.getDate(),
      );

      expect(bookedSlot?.available).toBe(false);
    });
  });

  describe('ウェイトリスト', () => {
    it('THE BookingService SHALL add member to waitlist', async () => {
      const entry = await service.addToWaitlist('member-001', 'class-yoga-001');

      expect(entry).toBeDefined();
      expect(entry.memberId).toBe('member-001');
      expect(entry.classId).toBe('class-yoga-001');
      expect(entry.position).toBe(1);
    });

    it('THE BookingService SHALL NOT add duplicate waitlist entry', async () => {
      await service.addToWaitlist('member-001', 'class-yoga-001');

      await expect(service.addToWaitlist('member-001', 'class-yoga-001')).rejects.toThrow(
        'Already on the waitlist',
      );
    });

    it('THE BookingService SHALL return waitlist position', async () => {
      await service.addToWaitlist('member-001', 'class-yoga-001');
      await service.addToWaitlist('member-002', 'class-yoga-001');

      const position = await service.getWaitlistPosition('member-002', 'class-yoga-001');
      expect(position).toBe(2);
    });
  });

  describe('出席管理', () => {
    let booking: Booking;

    beforeEach(async () => {
      const start = new Date();
      start.setHours(start.getHours() + 24);
      const end = new Date(start);
      end.setHours(end.getHours() + 1);

      booking = await service.createBooking({
        memberId: 'member-001',
        resourceType: 'class',
        resourceId: 'class-yoga-001',
        scheduledStart: start,
        scheduledEnd: end,
      });
    });

    it('THE BookingService SHALL mark attendance as completed', async () => {
      const marked = await service.markAttendance(booking.id, true);
      expect(marked.status).toBe('completed');
    });

    it('THE BookingService SHALL mark no-show', async () => {
      const marked = await service.markAttendance(booking.id, false);
      expect(marked.status).toBe('no-show');
    });
  });
});
