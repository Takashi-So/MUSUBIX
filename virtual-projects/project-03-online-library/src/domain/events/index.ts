/**
 * Domain Events
 * @design DES-LIBRARY-001 §7
 * @task TSK-LIB-016, TSK-LIB-017, TSK-LIB-018
 */

// Base Event
export abstract class DomainEvent<T = unknown> {
  readonly eventId: string;
  readonly occurredAt: Date;
  abstract readonly eventName: string;

  constructor(public readonly payload: T) {
    this.eventId = crypto.randomUUID();
    this.occurredAt = new Date();
  }
}

// Event Handler Type
export type EventHandler<T extends DomainEvent> = (event: T) => void | Promise<void>;

// Event Bus
export class EventBus {
  private handlers: Map<string, Set<EventHandler<DomainEvent>>> = new Map();

  subscribe<T extends DomainEvent>(
    eventName: string,
    handler: EventHandler<T>
  ): () => void {
    if (!this.handlers.has(eventName)) {
      this.handlers.set(eventName, new Set());
    }
    this.handlers.get(eventName)!.add(handler as EventHandler<DomainEvent>);

    return () => {
      this.handlers.get(eventName)?.delete(handler as EventHandler<DomainEvent>);
    };
  }

  publish(event: DomainEvent): void {
    const handlers = this.handlers.get(event.eventName);
    if (handlers) {
      handlers.forEach((handler) => handler(event));
    }
  }

  async publishAsync(event: DomainEvent): Promise<void> {
    const handlers = this.handlers.get(event.eventName);
    if (handlers) {
      await Promise.all([...handlers].map((handler) => handler(event)));
    }
  }
}

// Book Checked Out Event
export interface BookCheckedOutPayload {
  loanId: string;
  memberId: string;
  copyId: string;
  bookTitle: string;
  dueDate: Date;
}

export class BookCheckedOutEvent extends DomainEvent<BookCheckedOutPayload> {
  readonly eventName = 'BookCheckedOutEvent';
}

// Book Returned Event
export interface BookReturnedPayload {
  loanId: string;
  memberId: string;
  copyId: string;
  returnedAt: Date;
  isOverdue?: boolean;
  overdueDays?: number;
}

export class BookReturnedEvent extends DomainEvent<BookReturnedPayload> {
  readonly eventName = 'BookReturnedEvent';
}

// Book Reserved Event
export interface BookReservedPayload {
  reservationId: string;
  memberId: string;
  bookId: string;
  bookTitle: string;
  position: number;
}

export class BookReservedEvent extends DomainEvent<BookReservedPayload> {
  readonly eventName = 'BookReservedEvent';
}

// Reservation Ready Event
export interface ReservationReadyPayload {
  reservationId: string;
  memberId: string;
  bookTitle: string;
  expiresAt: Date;
}

export class ReservationReadyEvent extends DomainEvent<ReservationReadyPayload> {
  readonly eventName = 'ReservationReadyEvent';
}

// Loan Overdue Event
export interface LoanOverduePayload {
  loanId: string;
  memberId: string;
  bookTitle: string;
  daysOverdue: number;
  dueDate: Date;
}

export class LoanOverdueEvent extends DomainEvent<LoanOverduePayload> {
  readonly eventName = 'LoanOverdueEvent';
}

// Penalty Applied Event
export interface PenaltyAppliedPayload {
  penaltyId: string;
  memberId: string;
  reason: string;
  suspensionDays: number;
  expiresAt: Date;
}

export class PenaltyAppliedEvent extends DomainEvent<PenaltyAppliedPayload> {
  readonly eventName = 'PenaltyAppliedEvent';
}
