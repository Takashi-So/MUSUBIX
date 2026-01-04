/**
 * Seat Entity Tests
 * Traces to: REQ-TR-013, REQ-TR-014, REQ-TR-015, REQ-TR-016, REQ-TR-017
 */
import { describe, it, expect, beforeEach } from 'vitest';
import {
  createSeat,
  reserveSeat,
  sellSeat,
  releaseSeat,
  markSeatUnavailable,
  isValidSeatTransition,
  resetSeatCounter,
  CreateSeatInput,
} from '../../../src/domain/entities/seat.js';
import { createSeatCode } from '../../../src/domain/value-objects/seat-code.js';
import { createPrice } from '../../../src/domain/value-objects/price.js';

describe('Seat Entity', () => {
  beforeEach(() => {
    resetSeatCounter();
  });

  const createValidInput = (): CreateSeatInput | null => {
    const seatCode = createSeatCode('A', 1);
    const price = createPrice(5000);
    
    if (seatCode.isErr() || price.isErr()) return null;
    
    return {
      eventId: 'EVT-20250101-001' as any,
      seatCode: seatCode.value,
      price: price.value,
    };
  };

  describe('createSeat', () => {
    it('should create seat with valid input', () => {
      const input = createValidInput();
      if (!input) throw new Error('Failed to create input');

      const result = createSeat(input);
      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.seatCode.code).toBe('A-1');
        expect(result.value.status).toBe('available');
        expect(result.value.version).toBe(1);
        expect(result.value.id).toMatch(/^SEAT-\d{8}-001$/);
      }
    });

    it('should generate sequential IDs', () => {
      const input = createValidInput();
      if (!input) throw new Error('Failed to create input');

      const s1 = createSeat(input);
      const s2 = createSeat(input);
      
      if (s1.isOk() && s2.isOk()) {
        expect(s1.value.id).toMatch(/-001$/);
        expect(s2.value.id).toMatch(/-002$/);
      }
    });
  });

  describe('Status Transitions', () => {
    describe('isValidSeatTransition', () => {
      it('should allow available -> reserved', () => {
        expect(isValidSeatTransition('available', 'reserved')).toBe(true);
      });

      it('should allow available -> unavailable', () => {
        expect(isValidSeatTransition('available', 'unavailable')).toBe(true);
      });

      it('should allow reserved -> available (release)', () => {
        expect(isValidSeatTransition('reserved', 'available')).toBe(true);
      });

      it('should allow reserved -> sold', () => {
        expect(isValidSeatTransition('reserved', 'sold')).toBe(true);
      });

      it('should allow sold -> available (refund)', () => {
        expect(isValidSeatTransition('sold', 'available')).toBe(true);
      });

      it('should disallow available -> sold directly', () => {
        expect(isValidSeatTransition('available', 'sold')).toBe(false);
      });
    });

    describe('reserveSeat', () => {
      it('should reserve available seat', () => {
        const input = createValidInput();
        if (!input) throw new Error('Failed to create input');

        const seatResult = createSeat(input);
        if (seatResult.isErr()) throw new Error('Failed to create seat');

        const result = reserveSeat(seatResult.value);
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.status).toBe('reserved');
          expect(result.value.version).toBe(2); // Incremented
        }
      });

      it('should reject reserving already reserved seat', () => {
        const input = createValidInput();
        if (!input) throw new Error('Failed to create input');

        const seatResult = createSeat(input);
        if (seatResult.isErr()) throw new Error('Failed to create seat');

        const reservedResult = reserveSeat(seatResult.value);
        if (reservedResult.isErr()) throw new Error('Failed to reserve');

        const result = reserveSeat(reservedResult.value);
        expect(result.isErr()).toBe(true);
      });
    });

    describe('sellSeat', () => {
      it('should sell reserved seat', () => {
        const input = createValidInput();
        if (!input) throw new Error('Failed to create input');

        const seatResult = createSeat(input);
        if (seatResult.isErr()) throw new Error('Failed to create seat');

        const reservedResult = reserveSeat(seatResult.value);
        if (reservedResult.isErr()) throw new Error('Failed to reserve');

        const result = sellSeat(reservedResult.value);
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.status).toBe('sold');
          expect(result.value.version).toBe(3);
        }
      });

      it('should reject selling available seat directly', () => {
        const input = createValidInput();
        if (!input) throw new Error('Failed to create input');

        const seatResult = createSeat(input);
        if (seatResult.isErr()) throw new Error('Failed to create seat');

        const result = sellSeat(seatResult.value);
        expect(result.isErr()).toBe(true);
      });
    });

    describe('releaseSeat', () => {
      it('should release reserved seat', () => {
        const input = createValidInput();
        if (!input) throw new Error('Failed to create input');

        const seatResult = createSeat(input);
        if (seatResult.isErr()) throw new Error('Failed to create seat');

        const reservedResult = reserveSeat(seatResult.value);
        if (reservedResult.isErr()) throw new Error('Failed to reserve');

        const result = releaseSeat(reservedResult.value);
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.status).toBe('available');
        }
      });

      it('should release sold seat (refund)', () => {
        const input = createValidInput();
        if (!input) throw new Error('Failed to create input');

        const seatResult = createSeat(input);
        if (seatResult.isErr()) throw new Error('Failed to create seat');

        const reservedResult = reserveSeat(seatResult.value);
        if (reservedResult.isErr()) throw new Error('Failed to reserve');

        const soldResult = sellSeat(reservedResult.value);
        if (soldResult.isErr()) throw new Error('Failed to sell');

        const result = releaseSeat(soldResult.value);
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.status).toBe('available');
        }
      });
    });

    describe('markSeatUnavailable', () => {
      it('should mark available seat as unavailable', () => {
        const input = createValidInput();
        if (!input) throw new Error('Failed to create input');

        const seatResult = createSeat(input);
        if (seatResult.isErr()) throw new Error('Failed to create seat');

        const result = markSeatUnavailable(seatResult.value);
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.status).toBe('unavailable');
        }
      });

      it('should reject marking reserved seat as unavailable', () => {
        const input = createValidInput();
        if (!input) throw new Error('Failed to create input');

        const seatResult = createSeat(input);
        if (seatResult.isErr()) throw new Error('Failed to create seat');

        const reservedResult = reserveSeat(seatResult.value);
        if (reservedResult.isErr()) throw new Error('Failed to reserve');

        const result = markSeatUnavailable(reservedResult.value);
        expect(result.isErr()).toBe(true);
      });
    });
  });
});
