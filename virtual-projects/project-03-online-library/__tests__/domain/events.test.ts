/**
 * Domain Events Tests
 * @task TSK-LIB-016, TSK-LIB-017, TSK-LIB-018
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import {
  DomainEvent,
  EventBus,
  BookCheckedOutEvent,
  BookReturnedEvent,
  BookReservedEvent,
  ReservationReadyEvent,
  LoanOverdueEvent,
  PenaltyAppliedEvent,
} from '../../src/domain/events';

describe('Domain Events', () => {
  let eventBus: EventBus;

  beforeEach(() => {
    eventBus = new EventBus();
  });

  describe('EventBus', () => {
    it('should register and dispatch events', () => {
      const handler = vi.fn();
      eventBus.subscribe('BookCheckedOutEvent', handler);

      const event = new BookCheckedOutEvent({
        loanId: 'loan-1',
        memberId: 'member-1',
        copyId: 'copy-1',
        bookTitle: 'Test Book',
        dueDate: new Date(),
      });

      eventBus.publish(event);

      expect(handler).toHaveBeenCalledWith(event);
    });

    it('should support multiple handlers for same event', () => {
      const handler1 = vi.fn();
      const handler2 = vi.fn();

      eventBus.subscribe('BookReturnedEvent', handler1);
      eventBus.subscribe('BookReturnedEvent', handler2);

      const event = new BookReturnedEvent({
        loanId: 'loan-1',
        memberId: 'member-1',
        copyId: 'copy-1',
        returnedAt: new Date(),
      });

      eventBus.publish(event);

      expect(handler1).toHaveBeenCalled();
      expect(handler2).toHaveBeenCalled();
    });

    it('should allow unsubscribing', () => {
      const handler = vi.fn();
      const unsubscribe = eventBus.subscribe('BookCheckedOutEvent', handler);

      unsubscribe();

      const event = new BookCheckedOutEvent({
        loanId: 'loan-1',
        memberId: 'member-1',
        copyId: 'copy-1',
        bookTitle: 'Test',
        dueDate: new Date(),
      });

      eventBus.publish(event);
      expect(handler).not.toHaveBeenCalled();
    });
  });

  describe('BookCheckedOutEvent', () => {
    it('should contain checkout details', () => {
      const dueDate = new Date('2024-02-15');
      const event = new BookCheckedOutEvent({
        loanId: 'loan-123',
        memberId: 'member-456',
        copyId: 'copy-789',
        bookTitle: 'Domain-Driven Design',
        dueDate,
      });

      expect(event.eventName).toBe('BookCheckedOutEvent');
      expect(event.payload.loanId).toBe('loan-123');
      expect(event.payload.bookTitle).toBe('Domain-Driven Design');
      expect(event.occurredAt).toBeInstanceOf(Date);
    });
  });

  describe('BookReturnedEvent', () => {
    it('should include overdue info if applicable', () => {
      const event = new BookReturnedEvent({
        loanId: 'loan-1',
        memberId: 'member-1',
        copyId: 'copy-1',
        returnedAt: new Date(),
        isOverdue: true,
        overdueDays: 5,
      });

      expect(event.payload.isOverdue).toBe(true);
      expect(event.payload.overdueDays).toBe(5);
    });
  });

  describe('BookReservedEvent', () => {
    it('should include reservation position', () => {
      const event = new BookReservedEvent({
        reservationId: 'res-1',
        memberId: 'member-1',
        bookId: 'book-1',
        bookTitle: 'Clean Code',
        position: 3,
      });

      expect(event.payload.position).toBe(3);
    });
  });

  describe('ReservationReadyEvent', () => {
    it('should include pickup deadline', () => {
      const expiresAt = new Date('2024-02-20');
      const event = new ReservationReadyEvent({
        reservationId: 'res-1',
        memberId: 'member-1',
        bookTitle: 'Test Book',
        expiresAt,
      });

      expect(event.payload.expiresAt).toBe(expiresAt);
    });
  });

  describe('LoanOverdueEvent', () => {
    it('should include days overdue', () => {
      const event = new LoanOverdueEvent({
        loanId: 'loan-1',
        memberId: 'member-1',
        bookTitle: 'Test Book',
        daysOverdue: 3,
        dueDate: new Date('2024-02-01'),
      });

      expect(event.payload.daysOverdue).toBe(3);
    });
  });

  describe('PenaltyAppliedEvent', () => {
    it('should include suspension details', () => {
      const event = new PenaltyAppliedEvent({
        penaltyId: 'pen-1',
        memberId: 'member-1',
        reason: 'Overdue return',
        suspensionDays: 10,
        expiresAt: new Date('2024-02-20'),
      });

      expect(event.payload.suspensionDays).toBe(10);
      expect(event.payload.reason).toBe('Overdue return');
    });
  });
});
