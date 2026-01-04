/**
 * Reservation Entity
 * Traces to: REQ-TR-020, REQ-TR-021, REQ-TR-022, REQ-TR-023, REQ-TR-024, REQ-TR-025, REQ-TR-026
 * 
 * Represents a ticket reservation with one or more seats.
 */
import { Result, ok, err, ValidationError } from '../../shared/result.js';
import { Price } from '../value-objects/price.js';
import { EventId } from './event.js';
import { SeatId } from './seat.js';

// ============================================================================
// Type Definitions
// ============================================================================

export type ReservationId = string & { readonly __brand: unique symbol };
export type UserId = string & { readonly __brand: unique symbol };
export type ReservationStatus = 'pending' | 'confirmed' | 'cancelled' | 'expired';

const MAX_SEATS_PER_RESERVATION = 10; // REQ-TR-026
const RESERVATION_EXPIRY_MINUTES = 15; // REQ-TR-022

export interface Reservation {
  id: ReservationId;
  userId: UserId;
  eventId: EventId;
  seatIds: SeatId[];
  totalPrice: Price;
  status: ReservationStatus;
  expiresAt: Date;
  createdAt: Date;
  updatedAt: Date;
}

// ============================================================================
// Status Transition Map (BP-DESIGN-001)
// ============================================================================

const validReservationTransitions: Record<ReservationStatus, ReservationStatus[]> = {
  pending: ['confirmed', 'cancelled', 'expired'],
  confirmed: ['cancelled'],
  cancelled: [],
  expired: [],
};

export function isValidReservationTransition(from: ReservationStatus, to: ReservationStatus): boolean {
  return validReservationTransitions[from].includes(to);
}

// ============================================================================
// ID Generation (BP-CODE-002)
// ============================================================================

let reservationCounter = 0;

export function generateReservationId(): ReservationId {
  reservationCounter++;
  const date = new Date().toISOString().slice(0, 10).replace(/-/g, '');
  return `RSV-${date}-${reservationCounter.toString().padStart(3, '0')}` as ReservationId;
}

export function resetReservationCounter(): void {
  reservationCounter = 0;
}

// ============================================================================
// Entity Input DTO (BP-CODE-001)
// ============================================================================

export interface CreateReservationInput {
  userId: string;
  eventId: EventId;
  seatIds: SeatId[];
  totalPrice: Price;
}

// ============================================================================
// Factory Function
// ============================================================================

export function createReservation(
  input: CreateReservationInput
): Result<Reservation, ValidationError> {
  // Validate seat count (REQ-TR-026)
  if (input.seatIds.length === 0) {
    return err(new ValidationError('At least one seat must be selected'));
  }

  if (input.seatIds.length > MAX_SEATS_PER_RESERVATION) {
    return err(new ValidationError(
      `Cannot reserve more than ${MAX_SEATS_PER_RESERVATION} seats at once`
    ));
  }

  // Check for duplicate seats
  const uniqueSeats = new Set(input.seatIds);
  if (uniqueSeats.size !== input.seatIds.length) {
    return err(new ValidationError('Duplicate seats in reservation'));
  }

  const now = new Date();
  const expiresAt = new Date(now.getTime() + RESERVATION_EXPIRY_MINUTES * 60 * 1000);

  return ok({
    id: generateReservationId(),
    userId: input.userId as UserId,
    eventId: input.eventId,
    seatIds: input.seatIds,
    totalPrice: input.totalPrice,
    status: 'pending' as ReservationStatus,
    expiresAt,
    createdAt: now,
    updatedAt: now,
  });
}

// ============================================================================
// Status Transition Functions
// ============================================================================

export function confirmReservation(reservation: Reservation): Result<Reservation, ValidationError> {
  if (!isValidReservationTransition(reservation.status, 'confirmed')) {
    return err(new ValidationError(
      `Cannot confirm reservation with status ${reservation.status}`
    ));
  }

  // Check if expired
  if (new Date() > reservation.expiresAt) {
    return err(new ValidationError('Reservation has expired'));
  }

  return ok({
    ...reservation,
    status: 'confirmed' as ReservationStatus,
    updatedAt: new Date(),
  });
}

export function cancelReservation(
  reservation: Reservation,
  eventDateTime: Date
): Result<Reservation, ValidationError> {
  if (!isValidReservationTransition(reservation.status, 'cancelled')) {
    return err(new ValidationError(
      `Cannot cancel reservation with status ${reservation.status}`
    ));
  }

  // REQ-TR-025: Cannot cancel within 24 hours of event
  const now = new Date();
  const hoursUntilEvent = (eventDateTime.getTime() - now.getTime()) / (1000 * 60 * 60);
  
  if (hoursUntilEvent < 24 && reservation.status === 'confirmed') {
    return err(new ValidationError(
      'Cannot cancel confirmed reservation within 24 hours of event'
    ));
  }

  return ok({
    ...reservation,
    status: 'cancelled' as ReservationStatus,
    updatedAt: new Date(),
  });
}

export function expireReservation(reservation: Reservation): Result<Reservation, ValidationError> {
  if (!isValidReservationTransition(reservation.status, 'expired')) {
    return err(new ValidationError(
      `Cannot expire reservation with status ${reservation.status}`
    ));
  }

  return ok({
    ...reservation,
    status: 'expired' as ReservationStatus,
    updatedAt: new Date(),
  });
}

/**
 * Check if a reservation is expired (for pending reservations)
 */
export function isReservationExpired(reservation: Reservation): boolean {
  return reservation.status === 'pending' && new Date() > reservation.expiresAt;
}
