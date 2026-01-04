/**
 * Event Entity
 * Traces to: REQ-TR-001, REQ-TR-003, REQ-TR-004, REQ-TR-005
 * 
 * Represents a ticketed event with venue and seat configuration.
 */
import { Result, ok, err, ValidationError } from '../../shared/result.js';
import { Price, createPrice } from '../value-objects/price.js';
import { SeatConfig, createSeatConfig } from '../value-objects/seat-config.js';

// ============================================================================
// Type Definitions
// ============================================================================

export type EventId = string & { readonly __brand: unique symbol };
export type EventStatus = 'draft' | 'active' | 'completed' | 'cancelled';

export interface Event {
  id: EventId;
  name: string;
  description: string;
  venue: string;
  dateTime: Date;
  price: Price;
  seatConfig: SeatConfig;
  status: EventStatus;
  createdAt: Date;
  updatedAt: Date;
}

// ============================================================================
// Status Transition Map (BP-DESIGN-001)
// ============================================================================

const validEventTransitions: Record<EventStatus, EventStatus[]> = {
  draft: ['active', 'cancelled'],
  active: ['completed', 'cancelled'],
  completed: [],
  cancelled: [],
};

export function isValidEventTransition(from: EventStatus, to: EventStatus): boolean {
  return validEventTransitions[from].includes(to);
}

// ============================================================================
// ID Generation (BP-CODE-002)
// ============================================================================

let eventCounter = 0;

export function generateEventId(): EventId {
  eventCounter++;
  const date = new Date().toISOString().slice(0, 10).replace(/-/g, '');
  return `EVT-${date}-${eventCounter.toString().padStart(3, '0')}` as EventId;
}

export function resetEventCounter(): void {
  eventCounter = 0;
}

// ============================================================================
// Entity Input DTO (BP-CODE-001)
// ============================================================================

export interface CreateEventInput {
  name: string;
  description: string;
  dateTime: Date;
  venue: string;
  price: Price;
  seatConfig: SeatConfig;
}

// ============================================================================
// Factory Function
// ============================================================================

const MIN_HOURS_BEFORE_EVENT = 24;

export function createEvent(input: CreateEventInput): Result<Event, ValidationError> {
  // Validate name
  if (!input.name || input.name.trim().length === 0) {
    return err(new ValidationError('Event name is required'));
  }

  // Validate venue
  if (!input.venue || input.venue.trim().length === 0) {
    return err(new ValidationError('Venue is required'));
  }

  // Validate dateTime - must be in the future
  const now = new Date();
  if (input.dateTime <= now) {
    return err(new ValidationError('Event dateTime must be in the future'));
  }

  // Must be at least 24 hours from now
  const hoursUntilEvent = (input.dateTime.getTime() - now.getTime()) / (1000 * 60 * 60);
  if (hoursUntilEvent < MIN_HOURS_BEFORE_EVENT) {
    return err(new ValidationError(
      `Event must be scheduled at least ${MIN_HOURS_BEFORE_EVENT} hours in advance`
    ));
  }

  return ok({
    id: generateEventId(),
    name: input.name.trim(),
    description: input.description || '',
    venue: input.venue.trim(),
    dateTime: input.dateTime,
    price: input.price,
    seatConfig: input.seatConfig,
    status: 'draft' as EventStatus,
    createdAt: now,
    updatedAt: now,
  });
}

// ============================================================================
// Status Transition Functions
// ============================================================================

export function activateEvent(event: Event): Result<Event, ValidationError> {
  if (!isValidEventTransition(event.status, 'active')) {
    return err(new ValidationError(`Cannot activate event with status ${event.status}`));
  }

  return ok({
    ...event,
    status: 'active' as EventStatus,
    updatedAt: new Date(),
  });
}

export function completeEvent(event: Event): Result<Event, ValidationError> {
  if (!isValidEventTransition(event.status, 'completed')) {
    return err(new ValidationError(`Cannot complete event with status ${event.status}`));
  }

  return ok({
    ...event,
    status: 'completed' as EventStatus,
    updatedAt: new Date(),
  });
}

export function cancelEvent(event: Event): Result<Event, ValidationError> {
  if (!isValidEventTransition(event.status, 'cancelled')) {
    return err(new ValidationError(`Cannot cancel event with status ${event.status}`));
  }

  return ok({
    ...event,
    status: 'cancelled' as EventStatus,
    updatedAt: new Date(),
  });
}
