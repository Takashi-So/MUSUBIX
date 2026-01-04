/**
 * Reservation Entity Tests
 * Traces to: REQ-TR-020, REQ-TR-021, REQ-TR-022, REQ-TR-023, REQ-TR-024, REQ-TR-025, REQ-TR-026
 */
import { describe, it, expect, beforeEach } from 'vitest';
import {
  createReservation,
  confirmReservation,
  cancelReservation,
  expireReservation,
  isReservationExpired,
  isValidReservationTransition,
  resetReservationCounter,
  CreateReservationInput,
  ReservationStatus,
} from '../../../src/domain/entities/reservation.js';
import { createPrice } from '../../../src/domain/value-objects/price.js';
import { EventId } from '../../../src/domain/entities/event.js';
import { SeatId } from '../../../src/domain/entities/seat.js';

describe('Reservation Entity', () => {
  beforeEach(() => {
    resetReservationCounter();
  });

  const createValidInput = (): CreateReservationInput | null => {
    const price = createPrice(5000);
    if (price.isErr()) return null;
    
    return {
      userId: 'USER-001',
      eventId: 'EVT-20250101-001' as EventId,
      seatIds: ['SEAT-20250101-001' as SeatId, 'SEAT-20250101-002' as SeatId],
      totalPrice: price.value,
    };
  };

  describe('createReservation', () => {
    it('should create reservation with valid input', () => {
      const input = createValidInput();
      if (!input) throw new Error('Failed to create input');

      const result = createReservation(input);
      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.userId).toBe('USER-001');
        expect(result.value.status).toBe('pending');
        expect(result.value.seatIds).toHaveLength(2);
        expect(result.value.id).toMatch(/^RSV-\d{8}-001$/);
        expect(result.value.expiresAt.getTime()).toBeGreaterThan(Date.now());
      }
    });

    it('should set expiration to 15 minutes from now', () => {
      const input = createValidInput();
      if (!input) throw new Error('Failed to create input');

      const before = Date.now();
      const result = createReservation(input);
      const after = Date.now();
      
      if (result.isOk()) {
        const expectedMin = before + 15 * 60 * 1000;
        const expectedMax = after + 15 * 60 * 1000;
        expect(result.value.expiresAt.getTime()).toBeGreaterThanOrEqual(expectedMin);
        expect(result.value.expiresAt.getTime()).toBeLessThanOrEqual(expectedMax);
      }
    });

    it('should reject empty seat list', () => {
      const input = createValidInput();
      if (!input) throw new Error('Failed to create input');

      const result = createReservation({ ...input, seatIds: [] });
      expect(result.isErr()).toBe(true);
      if (result.isErr()) {
        expect(result.error.message).toContain('At least one seat');
      }
    });

    it('should reject more than 10 seats (REQ-TR-026)', () => {
      const input = createValidInput();
      if (!input) throw new Error('Failed to create input');

      const manySeats = Array.from({ length: 11 }, (_, i) => 
        `SEAT-20250101-${String(i + 1).padStart(3, '0')}` as SeatId
      );
      
      const result = createReservation({ ...input, seatIds: manySeats });
      expect(result.isErr()).toBe(true);
      if (result.isErr()) {
        expect(result.error.message).toContain('10');
      }
    });

    it('should reject duplicate seats', () => {
      const input = createValidInput();
      if (!input) throw new Error('Failed to create input');

      const duplicateSeats = [
        'SEAT-20250101-001' as SeatId,
        'SEAT-20250101-001' as SeatId,
      ];
      
      const result = createReservation({ ...input, seatIds: duplicateSeats });
      expect(result.isErr()).toBe(true);
      if (result.isErr()) {
        expect(result.error.message).toContain('Duplicate');
      }
    });

    it('should accept exactly 10 seats', () => {
      const input = createValidInput();
      if (!input) throw new Error('Failed to create input');

      const tenSeats = Array.from({ length: 10 }, (_, i) => 
        `SEAT-20250101-${String(i + 1).padStart(3, '0')}` as SeatId
      );
      
      const result = createReservation({ ...input, seatIds: tenSeats });
      expect(result.isOk()).toBe(true);
    });
  });

  describe('Status Transitions', () => {
    describe('isValidReservationTransition', () => {
      it('should allow pending -> confirmed', () => {
        expect(isValidReservationTransition('pending', 'confirmed')).toBe(true);
      });

      it('should allow pending -> cancelled', () => {
        expect(isValidReservationTransition('pending', 'cancelled')).toBe(true);
      });

      it('should allow pending -> expired', () => {
        expect(isValidReservationTransition('pending', 'expired')).toBe(true);
      });

      it('should allow confirmed -> cancelled', () => {
        expect(isValidReservationTransition('confirmed', 'cancelled')).toBe(true);
      });

      it('should disallow cancelled -> any', () => {
        expect(isValidReservationTransition('cancelled', 'pending')).toBe(false);
        expect(isValidReservationTransition('cancelled', 'confirmed')).toBe(false);
      });

      it('should disallow expired -> any', () => {
        expect(isValidReservationTransition('expired', 'pending')).toBe(false);
        expect(isValidReservationTransition('expired', 'confirmed')).toBe(false);
      });
    });

    describe('confirmReservation', () => {
      it('should confirm pending reservation', () => {
        const input = createValidInput();
        if (!input) throw new Error('Failed to create input');

        const reservationResult = createReservation(input);
        if (reservationResult.isErr()) throw new Error('Failed to create reservation');

        const result = confirmReservation(reservationResult.value);
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.status).toBe('confirmed');
        }
      });

      it('should reject confirming cancelled reservation', () => {
        const input = createValidInput();
        if (!input) throw new Error('Failed to create input');

        const reservationResult = createReservation(input);
        if (reservationResult.isErr()) throw new Error('Failed to create reservation');

        const eventDateTime = new Date(Date.now() + 86400000 * 7); // 7 days from now
        const cancelledResult = cancelReservation(reservationResult.value, eventDateTime);
        if (cancelledResult.isErr()) throw new Error('Failed to cancel');

        const result = confirmReservation(cancelledResult.value);
        expect(result.isErr()).toBe(true);
      });
    });

    describe('cancelReservation', () => {
      it('should cancel pending reservation', () => {
        const input = createValidInput();
        if (!input) throw new Error('Failed to create input');

        const reservationResult = createReservation(input);
        if (reservationResult.isErr()) throw new Error('Failed to create reservation');

        const eventDateTime = new Date(Date.now() + 86400000 * 7);
        const result = cancelReservation(reservationResult.value, eventDateTime);
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.status).toBe('cancelled');
        }
      });

      it('should cancel confirmed reservation more than 24 hours before event', () => {
        const input = createValidInput();
        if (!input) throw new Error('Failed to create input');

        const reservationResult = createReservation(input);
        if (reservationResult.isErr()) throw new Error('Failed to create reservation');

        const confirmedResult = confirmReservation(reservationResult.value);
        if (confirmedResult.isErr()) throw new Error('Failed to confirm');

        const eventDateTime = new Date(Date.now() + 86400000 * 7); // 7 days from now
        const result = cancelReservation(confirmedResult.value, eventDateTime);
        expect(result.isOk()).toBe(true);
      });

      it('should reject cancelling confirmed reservation within 24 hours (REQ-TR-025)', () => {
        const input = createValidInput();
        if (!input) throw new Error('Failed to create input');

        const reservationResult = createReservation(input);
        if (reservationResult.isErr()) throw new Error('Failed to create reservation');

        const confirmedResult = confirmReservation(reservationResult.value);
        if (confirmedResult.isErr()) throw new Error('Failed to confirm');

        const eventDateTime = new Date(Date.now() + 3600000 * 12); // 12 hours from now
        const result = cancelReservation(confirmedResult.value, eventDateTime);
        expect(result.isErr()).toBe(true);
        if (result.isErr()) {
          expect(result.error.message).toContain('24 hours');
        }
      });
    });

    describe('expireReservation', () => {
      it('should expire pending reservation', () => {
        const input = createValidInput();
        if (!input) throw new Error('Failed to create input');

        const reservationResult = createReservation(input);
        if (reservationResult.isErr()) throw new Error('Failed to create reservation');

        const result = expireReservation(reservationResult.value);
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.status).toBe('expired');
        }
      });

      it('should reject expiring confirmed reservation', () => {
        const input = createValidInput();
        if (!input) throw new Error('Failed to create input');

        const reservationResult = createReservation(input);
        if (reservationResult.isErr()) throw new Error('Failed to create reservation');

        const confirmedResult = confirmReservation(reservationResult.value);
        if (confirmedResult.isErr()) throw new Error('Failed to confirm');

        const result = expireReservation(confirmedResult.value);
        expect(result.isErr()).toBe(true);
      });
    });
  });

  describe('isReservationExpired', () => {
    it('should return false for non-expired pending reservation', () => {
      const input = createValidInput();
      if (!input) throw new Error('Failed to create input');

      const reservationResult = createReservation(input);
      if (reservationResult.isErr()) throw new Error('Failed to create reservation');

      expect(isReservationExpired(reservationResult.value)).toBe(false);
    });

    it('should return false for confirmed reservation', () => {
      const input = createValidInput();
      if (!input) throw new Error('Failed to create input');

      const reservationResult = createReservation(input);
      if (reservationResult.isErr()) throw new Error('Failed to create reservation');

      const confirmedResult = confirmReservation(reservationResult.value);
      if (confirmedResult.isErr()) throw new Error('Failed to confirm');

      expect(isReservationExpired(confirmedResult.value)).toBe(false);
    });
  });
});
