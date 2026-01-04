/**
 * Seat Entity
 * Traces to: REQ-TR-010, REQ-TR-011, REQ-TR-012, REQ-TR-013, REQ-TR-014
 * 
 * Represents a single seat in an event venue with status and pricing.
 */
import { Result, ok, err, ValidationError } from '../../shared/result.js';
import { Price } from '../value-objects/price.js';
import { SeatCode } from '../value-objects/seat-code.js';
import { EventId } from './event.js';

// ============================================================================
// Type Definitions
// ============================================================================

export type SeatId = string & { readonly __brand: unique symbol };
export type SeatStatus = 'available' | 'reserved' | 'sold' | 'unavailable';

export interface Seat {
  id: SeatId;
  eventId: EventId;
  seatCode: SeatCode;
  price: Price;
  status: SeatStatus;
  version: number; // Optimistic locking (REQ-TR-NF-002)
  createdAt: Date;
  updatedAt: Date;
}

// ============================================================================
// Status Transition Map (BP-DESIGN-001)
// ============================================================================

const validSeatTransitions: Record<SeatStatus, SeatStatus[]> = {
  available: ['reserved', 'unavailable'],
  reserved: ['available', 'sold'],
  sold: ['available'], // refund case
  unavailable: ['available'],
};

export function isValidSeatTransition(from: SeatStatus, to: SeatStatus): boolean {
  return validSeatTransitions[from].includes(to);
}

// ============================================================================
// ID Generation (BP-CODE-002)
// ============================================================================

let seatCounter = 0;

export function generateSeatId(): SeatId {
  seatCounter++;
  const date = new Date().toISOString().slice(0, 10).replace(/-/g, '');
  return `SEAT-${date}-${seatCounter.toString().padStart(3, '0')}` as SeatId;
}

export function resetSeatCounter(): void {
  seatCounter = 0;
}

// ============================================================================
// Entity Input DTO (BP-CODE-001)
// ============================================================================

export interface CreateSeatInput {
  eventId: EventId;
  seatCode: SeatCode;
  price: Price;
}

// ============================================================================
// Factory Function
// ============================================================================

export function createSeat(input: CreateSeatInput): Result<Seat, ValidationError> {
  const now = new Date();
  
  return ok({
    id: generateSeatId(),
    eventId: input.eventId,
    seatCode: input.seatCode,
    price: input.price,
    status: 'available' as SeatStatus,
    version: 1,
    createdAt: now,
    updatedAt: now,
  });
}

// ============================================================================
// Status Transition Functions
// ============================================================================

export function reserveSeat(seat: Seat): Result<Seat, ValidationError> {
  if (!isValidSeatTransition(seat.status, 'reserved')) {
    return err(new ValidationError(
      `Cannot reserve seat ${seat.seatCode.code} with status ${seat.status}`
    ));
  }

  return ok({
    ...seat,
    status: 'reserved' as SeatStatus,
    version: seat.version + 1,
    updatedAt: new Date(),
  });
}

export function sellSeat(seat: Seat): Result<Seat, ValidationError> {
  if (!isValidSeatTransition(seat.status, 'sold')) {
    return err(new ValidationError(
      `Cannot sell seat ${seat.seatCode.code} with status ${seat.status}`
    ));
  }

  return ok({
    ...seat,
    status: 'sold' as SeatStatus,
    version: seat.version + 1,
    updatedAt: new Date(),
  });
}

export function releaseSeat(seat: Seat): Result<Seat, ValidationError> {
  if (!isValidSeatTransition(seat.status, 'available')) {
    return err(new ValidationError(
      `Cannot release seat ${seat.seatCode.code} with status ${seat.status}`
    ));
  }

  return ok({
    ...seat,
    status: 'available' as SeatStatus,
    version: seat.version + 1,
    updatedAt: new Date(),
  });
}

export function markSeatUnavailable(seat: Seat): Result<Seat, ValidationError> {
  if (!isValidSeatTransition(seat.status, 'unavailable')) {
    return err(new ValidationError(
      `Cannot mark seat ${seat.seatCode.code} as unavailable with status ${seat.status}`
    ));
  }

  return ok({
    ...seat,
    status: 'unavailable' as SeatStatus,
    version: seat.version + 1,
    updatedAt: new Date(),
  });
}
