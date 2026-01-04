/**
 * Loan and Reservation Entity Tests
 * @requirements REQ-LOAN-001〜006, REQ-RESERVE-001〜005
 * @design DES-LIBRARY-001 §3.2
 * @task TSK-LIB-005, TSK-LIB-006
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { Loan, LoanId, LoanStatus } from '../../src/domain/loan/Loan';
import { Reservation, ReservationId, ReservationStatus } from '../../src/domain/loan/Reservation';
import { MemberId } from '../../src/domain/member/Member';
import { CopyId } from '../../src/domain/book/BookCopy';
import { BookId } from '../../src/domain/book/Book';

describe('Loan Entity', () => {
  let memberId: MemberId;
  let copyId: CopyId;

  beforeEach(() => {
    memberId = MemberId.generate();
    copyId = CopyId.generate();
  });

  describe('creation', () => {
    it('should create loan with active status', () => {
      const loan = Loan.create({
        memberId,
        copyId,
        loanDays: 14,
      });

      expect(loan.id).toBeDefined();
      expect(loan.status).toBe(LoanStatus.ACTIVE);
      expect(loan.memberId.equals(memberId)).toBe(true);
      expect(loan.copyId.equals(copyId)).toBe(true);
    });

    it('should set due date correctly', () => {
      const loan = Loan.create({
        memberId,
        copyId,
        loanDays: 14,
      });

      const expectedDueDate = new Date(loan.loanDate);
      expectedDueDate.setDate(expectedDueDate.getDate() + 14);
      expect(loan.dueDate.toDateString()).toBe(expectedDueDate.toDateString());
    });

    it('should have zero extension count', () => {
      const loan = Loan.create({
        memberId,
        copyId,
        loanDays: 14,
      });

      expect(loan.extensionCount).toBe(0);
    });
  });

  describe('return', () => {
    it('should mark loan as returned', () => {
      const loan = Loan.create({
        memberId,
        copyId,
        loanDays: 14,
      });

      loan.return();
      expect(loan.status).toBe(LoanStatus.RETURNED);
      expect(loan.returnedAt).toBeDefined();
    });

    it('should not return already returned loan', () => {
      const loan = Loan.create({
        memberId,
        copyId,
        loanDays: 14,
      });

      loan.return();
      expect(() => loan.return()).toThrow('Loan is already returned');
    });
  });

  describe('extension', () => {
    it('should extend loan by 14 days', () => {
      const loan = Loan.create({
        memberId,
        copyId,
        loanDays: 14,
      });

      const originalDueDate = new Date(loan.dueDate);
      loan.extend();

      expect(loan.extensionCount).toBe(1);
      const expectedDueDate = new Date(originalDueDate);
      expectedDueDate.setDate(expectedDueDate.getDate() + 14);
      expect(loan.dueDate.toDateString()).toBe(expectedDueDate.toDateString());
    });

    it('should not extend more than 2 times', () => {
      const loan = Loan.create({
        memberId,
        copyId,
        loanDays: 14,
      });

      loan.extend();
      loan.extend();
      expect(() => loan.extend()).toThrow('Maximum extensions reached');
    });

    it('should not extend returned loan', () => {
      const loan = Loan.create({
        memberId,
        copyId,
        loanDays: 14,
      });

      loan.return();
      expect(() => loan.extend()).toThrow('Cannot extend returned loan');
    });
  });

  describe('overdue', () => {
    it('should mark as overdue', () => {
      const loan = Loan.create({
        memberId,
        copyId,
        loanDays: 14,
      });

      loan.markOverdue();
      expect(loan.status).toBe(LoanStatus.OVERDUE);
    });

    it('should calculate overdue days', () => {
      const loan = Loan.create({
        memberId,
        copyId,
        loanDays: 14,
      });

      // Manually set due date to past
      const pastDueDate = new Date();
      pastDueDate.setDate(pastDueDate.getDate() - 5);
      loan.setDueDateForTest(pastDueDate);

      expect(loan.getOverdueDays()).toBe(5);
    });

    it('should return 0 for non-overdue loan', () => {
      const loan = Loan.create({
        memberId,
        copyId,
        loanDays: 14,
      });

      expect(loan.getOverdueDays()).toBe(0);
    });
  });
});

describe('Reservation Entity', () => {
  let memberId: MemberId;
  let bookId: BookId;

  beforeEach(() => {
    memberId = MemberId.generate();
    bookId = BookId.generate();
  });

  describe('creation', () => {
    it('should create reservation with waiting status', () => {
      const reservation = Reservation.create({
        memberId,
        bookId,
        position: 1,
      });

      expect(reservation.id).toBeDefined();
      expect(reservation.status).toBe(ReservationStatus.WAITING);
      expect(reservation.position).toBe(1);
    });
  });

  describe('ready', () => {
    it('should mark as ready', () => {
      const reservation = Reservation.create({
        memberId,
        bookId,
        position: 1,
      });

      reservation.markReady();
      expect(reservation.status).toBe(ReservationStatus.READY);
      expect(reservation.readyAt).toBeDefined();
    });

    it('should calculate expiry date (7 days)', () => {
      const reservation = Reservation.create({
        memberId,
        bookId,
        position: 1,
      });

      reservation.markReady();
      const expectedExpiry = new Date(reservation.readyAt!);
      expectedExpiry.setDate(expectedExpiry.getDate() + 7);
      expect(reservation.getExpiryDate()?.toDateString()).toBe(expectedExpiry.toDateString());
    });
  });

  describe('complete', () => {
    it('should mark as completed', () => {
      const reservation = Reservation.create({
        memberId,
        bookId,
        position: 1,
      });

      reservation.markReady();
      reservation.complete();
      expect(reservation.status).toBe(ReservationStatus.COMPLETED);
    });
  });

  describe('cancel', () => {
    it('should cancel waiting reservation', () => {
      const reservation = Reservation.create({
        memberId,
        bookId,
        position: 1,
      });

      reservation.cancel();
      expect(reservation.status).toBe(ReservationStatus.CANCELLED);
    });

    it('should cancel ready reservation (expired)', () => {
      const reservation = Reservation.create({
        memberId,
        bookId,
        position: 1,
      });

      reservation.markReady();
      reservation.cancel();
      expect(reservation.status).toBe(ReservationStatus.CANCELLED);
    });
  });

  describe('position update', () => {
    it('should update position', () => {
      const reservation = Reservation.create({
        memberId,
        bookId,
        position: 3,
      });

      reservation.updatePosition(2);
      expect(reservation.position).toBe(2);
    });
  });

  describe('expiry check', () => {
    it('should detect expired reservation', () => {
      const reservation = Reservation.create({
        memberId,
        bookId,
        position: 1,
      });

      reservation.markReady();
      // Set readyAt to 8 days ago (past the 7-day expiry)
      const eightDaysAgo = new Date(Date.now() - 8 * 24 * 60 * 60 * 1000);
      reservation.setReadyAtForTest(eightDaysAgo);
      expect(reservation.isExpired()).toBe(true);
    });

    it('should not be expired when not ready', () => {
      const reservation = Reservation.create({
        memberId,
        bookId,
        position: 1,
      });

      expect(reservation.isExpired()).toBe(false);
    });
  });
});

describe('LoanId Value Object', () => {
  it('should generate unique ID', () => {
    const id1 = LoanId.generate();
    const id2 = LoanId.generate();
    expect(id1.equals(id2)).toBe(false);
  });
});

describe('ReservationId Value Object', () => {
  it('should generate unique ID', () => {
    const id1 = ReservationId.generate();
    const id2 = ReservationId.generate();
    expect(id1.equals(id2)).toBe(false);
  });
});
