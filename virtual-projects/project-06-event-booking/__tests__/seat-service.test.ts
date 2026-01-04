/**
 * SeatService Unit Tests
 *
 * @module __tests__/seat-service.test
 * @traces REQ-EVENT-009, REQ-EVENT-010, REQ-EVENT-011
 */

import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest';
import {
  SeatService,
  type Seat,
  type VenueLayout,
  type SeatReservation,
  type ISeatRepository,
  type ILayoutRepository,
  type IReservationRepository,
} from '../src/seat-service';

// ============================================================
// Mock Implementations
// ============================================================

function createMockSeatRepository(): ISeatRepository {
  const seats = new Map<string, Seat>();

  return {
    save: vi.fn(async (seat: Seat) => {
      seats.set(seat.id, { ...seat });
      return seat;
    }),
    saveMany: vi.fn(async (seatList: Seat[]) => {
      seatList.forEach((s) => seats.set(s.id, { ...s }));
      return seatList;
    }),
    findById: vi.fn(async (id: string) => {
      const seat = seats.get(id);
      return seat ? { ...seat } : null;
    }),
    findByEvent: vi.fn(async (eventId: string) => {
      return Array.from(seats.values()).filter((s) => s.eventId === eventId);
    }),
    findAvailable: vi.fn(async (eventId: string, section?: string) => {
      let result = Array.from(seats.values()).filter(
        (s) => s.eventId === eventId && s.status === 'available'
      );
      if (section) {
        result = result.filter((s) => s.section === section);
      }
      return result;
    }),
    update: vi.fn(async (id: string, data: Partial<Seat>) => {
      const seat = seats.get(id);
      if (!seat) throw new Error('Seat not found');
      const updated = { ...seat, ...data };
      seats.set(id, updated);
      return updated;
    }),
    updateMany: vi.fn(async (ids: string[], data: Partial<Seat>) => {
      return ids.map((id) => {
        const seat = seats.get(id);
        if (!seat) throw new Error('Seat not found');
        const updated = { ...seat, ...data };
        seats.set(id, updated);
        return updated;
      });
    }),
  };
}

function createMockLayoutRepository(): ILayoutRepository {
  const layouts = new Map<string, VenueLayout>();

  return {
    save: vi.fn(async (layout: VenueLayout) => {
      layouts.set(layout.id, { ...layout });
      return layout;
    }),
    findById: vi.fn(async (id: string) => {
      const layout = layouts.get(id);
      return layout ? { ...layout } : null;
    }),
    findByEvent: vi.fn(async (eventId: string) => {
      const layout = Array.from(layouts.values()).find((l) => l.eventId === eventId);
      return layout || null;
    }),
  };
}

function createMockReservationRepository(): IReservationRepository {
  const reservations = new Map<string, SeatReservation>();

  return {
    save: vi.fn(async (reservation: SeatReservation) => {
      reservations.set(reservation.id, { ...reservation });
      return reservation;
    }),
    findById: vi.fn(async (id: string) => {
      const reservation = reservations.get(id);
      return reservation ? { ...reservation } : null;
    }),
    findByUser: vi.fn(async (userId: string) => {
      return Array.from(reservations.values()).filter(
        (r) => r.userId === userId && r.status === 'active'
      );
    }),
    findExpired: vi.fn(async () => {
      const now = new Date();
      return Array.from(reservations.values()).filter(
        (r) => r.status === 'active' && r.expiresAt < now
      );
    }),
    update: vi.fn(async (id: string, data: Partial<SeatReservation>) => {
      const reservation = reservations.get(id);
      if (!reservation) throw new Error('Reservation not found');
      const updated = { ...reservation, ...data };
      reservations.set(id, updated);
      return updated;
    }),
    delete: vi.fn(async (id: string) => {
      reservations.delete(id);
      return true;
    }),
  };
}

// ============================================================
// Test Suites
// ============================================================

describe('SeatService', () => {
  let service: SeatService;
  let seatRepo: ISeatRepository;
  let layoutRepo: ILayoutRepository;
  let reservationRepo: IReservationRepository;

  beforeEach(() => {
    vi.useFakeTimers();
    vi.setSystemTime(new Date('2025-06-15T10:00:00Z'));
    
    seatRepo = createMockSeatRepository();
    layoutRepo = createMockLayoutRepository();
    reservationRepo = createMockReservationRepository();
    service = new SeatService(seatRepo, layoutRepo, reservationRepo);
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  // ==========================================================
  // REQ-EVENT-009: 座席レイアウト
  // ==========================================================
  describe('REQ-EVENT-009: Seat Layout Creation', () => {
    it('should create venue layout with sections', async () => {
      const input = {
        eventId: 'evt-001',
        name: 'Concert Hall Layout',
        sections: [
          {
            name: 'Section A - Front',
            category: 'vip' as const,
            rows: [
              { rowId: 'A1', seats: 20, priceModifier: 1.0 },
              { rowId: 'A2', seats: 20, priceModifier: 1.0 },
            ],
            basePrice: 200,
          },
          {
            name: 'Section B - Middle',
            category: 'premium' as const,
            rows: [
              { rowId: 'B1', seats: 30, priceModifier: 1.0 },
              { rowId: 'B2', seats: 30, priceModifier: 1.0 },
            ],
            basePrice: 150,
          },
        ],
      };

      const layout = await service.createLayout(input);

      expect(layout).toBeDefined();
      expect(layout.id).toBeDefined();
      expect(layout.sections.length).toBe(2);
      expect(layout.totalCapacity).toBe(100);
    });

    it('should calculate total capacity correctly', async () => {
      const input = {
        eventId: 'evt-002',
        name: 'Small Theater',
        sections: [
          {
            name: 'Main Hall',
            category: 'standard' as const,
            rows: [
              { rowId: 'R1', seats: 10, priceModifier: 1.0 },
              { rowId: 'R2', seats: 12, priceModifier: 1.0 },
              { rowId: 'R3', seats: 14, priceModifier: 1.0 },
            ],
            basePrice: 100,
          },
        ],
      };

      const layout = await service.createLayout(input);

      expect(layout.totalCapacity).toBe(36);
    });
  });

  // ==========================================================
  // REQ-EVENT-010: 座席予約（10分タイムアウト）
  // ==========================================================
  describe('REQ-EVENT-010: Seat Reservation with Timeout', () => {
    beforeEach(async () => {
      // Create test seats
      for (let i = 1; i <= 5; i++) {
        await seatRepo.save({
          id: `seat-${i}`,
          eventId: 'evt-001',
          section: 'A',
          row: '1',
          seatNumber: `${i}`,
          category: 'standard',
          price: 50,
          status: 'available',
          reservedBy: null,
          reservedAt: null,
          reservationExpiry: null,
          bookedBy: null,
        });
      }
    });

    it('should reserve seats with default 10-minute expiration', async () => {
      const result = await service.reserveSeats({
        eventId: 'evt-001',
        seatIds: ['seat-1', 'seat-2'],
        userId: 'user-001',
      });

      expect(result).toBeDefined();
      expect(result.seats.length).toBe(2);
      expect(result.status).toBe('active');
      
      // Check expiration is ~10 minutes from now
      const expectedExpiry = new Date('2025-06-15T10:10:00Z');
      expect(result.expiresAt.getTime()).toBe(expectedExpiry.getTime());
    });

    it('should mark seats as reserved', async () => {
      await service.reserveSeats({
        eventId: 'evt-001',
        seatIds: ['seat-3'],
        userId: 'user-002',
      });

      const seats = await seatRepo.findByEvent('evt-001');
      const seat3 = seats.find((s) => s.id === 'seat-3');
      
      expect(seat3?.status).toBe('reserved');
      expect(seat3?.reservedBy).toBe('user-002');
    });

    it('should reject reservation for unavailable seats', async () => {
      // Reserve seat first
      await service.reserveSeats({
        eventId: 'evt-001',
        seatIds: ['seat-1'],
        userId: 'user-001',
      });

      // Try to reserve same seat
      await expect(
        service.reserveSeats({
          eventId: 'evt-001',
          seatIds: ['seat-1'],
          userId: 'user-002',
        })
      ).rejects.toThrow();
    });

    it('should allow custom duration for reservation', async () => {
      const result = await service.reserveSeats({
        eventId: 'evt-001',
        seatIds: ['seat-4'],
        userId: 'user-003',
        durationMinutes: 5,
      });

      const expectedExpiry = new Date('2025-06-15T10:05:00Z');
      expect(result.expiresAt.getTime()).toBe(expectedExpiry.getTime());
    });
  });

  // ==========================================================
  // REQ-EVENT-011: 座席確定
  // ==========================================================
  describe('REQ-EVENT-011: Seat Booking Confirmation', () => {
    let testReservation: SeatReservation;

    beforeEach(async () => {
      // Create test seats
      for (let i = 1; i <= 3; i++) {
        await seatRepo.save({
          id: `confirm-seat-${i}`,
          eventId: 'evt-002',
          section: 'A',
          row: '1',
          seatNumber: `${i}`,
          category: 'standard',
          price: 75,
          status: 'available',
          reservedBy: null,
          reservedAt: null,
          reservationExpiry: null,
          bookedBy: null,
        });
      }

      // Make a reservation
      testReservation = await service.reserveSeats({
        eventId: 'evt-002',
        seatIds: ['confirm-seat-1', 'confirm-seat-2'],
        userId: 'booking-user',
      });
    });

    it('should confirm reservation and book seats', async () => {
      const result = await service.confirmReservation(
        testReservation.id,
        'booking-user'
      );

      expect(result.length).toBe(2);
      expect(result.every((s) => s.status === 'booked')).toBe(true);
    });

    it('should update reservation status to converted', async () => {
      await service.confirmReservation(testReservation.id, 'booking-user');

      const reservation = await reservationRepo.findById(testReservation.id);
      expect(reservation?.status).toBe('converted');
    });

    it('should reject confirmation from wrong user', async () => {
      await expect(
        service.confirmReservation(testReservation.id, 'wrong-user')
      ).rejects.toThrow();
    });
  });

  // ==========================================================
  // Seat Availability Tests
  // ==========================================================
  describe('Seat Availability', () => {
    beforeEach(async () => {
      await seatRepo.save({
        id: 'avail-1',
        eventId: 'evt-003',
        section: 'A',
        row: '1',
        seatNumber: '1',
        category: 'standard',
        price: 50,
        status: 'available',
        reservedBy: null,
        reservedAt: null,
        reservationExpiry: null,
        bookedBy: null,
      });
      await seatRepo.save({
        id: 'avail-2',
        eventId: 'evt-003',
        section: 'A',
        row: '1',
        seatNumber: '2',
        category: 'standard',
        price: 50,
        status: 'booked',
        reservedBy: null,
        reservedAt: null,
        reservationExpiry: null,
        bookedBy: 'some-user',
      });
      await seatRepo.save({
        id: 'avail-3',
        eventId: 'evt-003',
        section: 'B',
        row: '1',
        seatNumber: '1',
        category: 'premium',
        price: 75,
        status: 'available',
        reservedBy: null,
        reservedAt: null,
        reservationExpiry: null,
        bookedBy: null,
      });
    });

    it('should get available seats for event', async () => {
      const availableSeats = await service.getAvailableSeats('evt-003');

      expect(availableSeats.length).toBe(2);
      expect(availableSeats.every((s) => s.status === 'available')).toBe(true);
    });

    it('should filter by section', async () => {
      const sectionASeats = await service.getAvailableSeats('evt-003', 'A');

      expect(sectionASeats.length).toBe(1);
      expect(sectionASeats[0].section).toBe('A');
    });

    it('should get all seats for event', async () => {
      const allSeats = await service.getSeatsByEvent('evt-003');

      expect(allSeats.length).toBe(3);
    });
  });

  // ==========================================================
  // Reservation Release Tests
  // ==========================================================
  describe('Reservation Release', () => {
    it('should release reservation and free seats', async () => {
      await seatRepo.save({
        id: 'release-1',
        eventId: 'evt-004',
        section: 'A',
        row: '1',
        seatNumber: '1',
        category: 'standard',
        price: 50,
        status: 'available',
        reservedBy: null,
        reservedAt: null,
        reservationExpiry: null,
        bookedBy: null,
      });

      const reservation = await service.reserveSeats({
        eventId: 'evt-004',
        seatIds: ['release-1'],
        userId: 'release-user',
      });

      const released = await service.releaseReservation(reservation.id);

      expect(released).toBe(true);
    });
  });

  // ==========================================================
  // Seat Blocking Tests
  // ==========================================================
  describe('Seat Blocking', () => {
    beforeEach(async () => {
      await seatRepo.save({
        id: 'block-1',
        eventId: 'evt-005',
        section: 'A',
        row: '1',
        seatNumber: '1',
        category: 'standard',
        price: 50,
        status: 'available',
        reservedBy: null,
        reservedAt: null,
        reservationExpiry: null,
        bookedBy: null,
      });
    });

    it('should block seats for maintenance', async () => {
      const blocked = await service.blockSeats('evt-005', ['block-1'], 'Maintenance');

      expect(blocked.length).toBe(1);
      expect(blocked[0].status).toBe('blocked');
    });

    it('should unblock seats', async () => {
      await service.blockSeats('evt-005', ['block-1'], 'Maintenance');
      
      const unblocked = await service.unblockSeats(['block-1']);

      expect(unblocked.length).toBe(1);
      expect(unblocked[0].status).toBe('available');
    });
  });
});
