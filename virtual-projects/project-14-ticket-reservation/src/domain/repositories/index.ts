/**
 * Repository Interfaces
 * Traces to: REQ-TR-006, REQ-TR-007, REQ-TR-008, REQ-TR-009
 * 
 * Port definitions for persistence (Hexagonal Architecture)
 */
import { Result, ValidationError } from '../../shared/result.js';
import { Event, EventId } from '../entities/event.js';
import { Seat, SeatId } from '../entities/seat.js';
import { Reservation, ReservationId, UserId } from '../entities/reservation.js';
import { SeatCode } from '../value-objects/seat-code.js';

// ============================================================================
// Event Repository (REQ-TR-006, REQ-TR-007)
// ============================================================================

export interface EventRepository {
  /**
   * Find event by ID
   */
  findById(id: EventId): Promise<Event | null>;

  /**
   * Find all active events
   */
  findAllActive(): Promise<Event[]>;

  /**
   * Find events by date range
   */
  findByDateRange(startDate: Date, endDate: Date): Promise<Event[]>;

  /**
   * Save new event
   */
  save(event: Event): Promise<Result<Event, ValidationError>>;

  /**
   * Update existing event
   */
  update(event: Event): Promise<Result<Event, ValidationError>>;

  /**
   * Delete event (soft delete)
   */
  delete(id: EventId): Promise<Result<void, ValidationError>>;
}

// ============================================================================
// Seat Repository (REQ-TR-008)
// ============================================================================

export interface SeatRepository {
  /**
   * Find seat by ID
   */
  findById(id: SeatId): Promise<Seat | null>;

  /**
   * Find seat by event and seat code
   */
  findByEventAndCode(eventId: EventId, seatCode: SeatCode): Promise<Seat | null>;

  /**
   * Find all seats for an event
   */
  findByEventId(eventId: EventId): Promise<Seat[]>;

  /**
   * Find available seats for an event
   */
  findAvailableByEventId(eventId: EventId): Promise<Seat[]>;

  /**
   * Save new seat
   */
  save(seat: Seat): Promise<Result<Seat, ValidationError>>;

  /**
   * Batch save seats
   */
  saveAll(seats: Seat[]): Promise<Result<Seat[], ValidationError>>;

  /**
   * Update seat with optimistic locking
   */
  update(seat: Seat): Promise<Result<Seat, ValidationError>>;

  /**
   * Batch update seats with optimistic locking
   */
  updateAll(seats: Seat[]): Promise<Result<Seat[], ValidationError>>;
}

// ============================================================================
// Reservation Repository (REQ-TR-009)
// ============================================================================

export interface ReservationRepository {
  /**
   * Find reservation by ID
   */
  findById(id: ReservationId): Promise<Reservation | null>;

  /**
   * Find reservations by user
   */
  findByUserId(userId: UserId): Promise<Reservation[]>;

  /**
   * Find reservations by event
   */
  findByEventId(eventId: EventId): Promise<Reservation[]>;

  /**
   * Find pending reservations that have expired
   */
  findExpiredPending(): Promise<Reservation[]>;

  /**
   * Save new reservation
   */
  save(reservation: Reservation): Promise<Result<Reservation, ValidationError>>;

  /**
   * Update reservation
   */
  update(reservation: Reservation): Promise<Result<Reservation, ValidationError>>;
}
