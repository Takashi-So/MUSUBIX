/**
 * Domain Services Tests
 * @design DES-LIBRARY-001 §4 Domain Services
 * @task TSK-LIB-007, TSK-LIB-008, TSK-LIB-009
 */
import { describe, it, expect, beforeEach, vi } from 'vitest';
import { LoanService } from '../../src/domain/services/LoanService';
import { ReservationService } from '../../src/domain/services/ReservationService';
import { MemberService } from '../../src/domain/services/MemberService';
import { Book, BookId, ISBN } from '../../src/domain/book/Book';
import { BookCopy, CopyId, CopyStatus } from '../../src/domain/book/BookCopy';
import { Member, MemberId, MemberType, MemberStatus } from '../../src/domain/member/Member';
import { Loan, LoanId, LoanStatus } from '../../src/domain/loan/Loan';
import { Reservation, ReservationId, ReservationStatus } from '../../src/domain/loan/Reservation';
import { Penalty, PenaltyId, PenaltyStatus } from '../../src/domain/member/Penalty';

// ============================================================
// LoanService Tests
// ============================================================
describe('LoanService', () => {
  let loanService: LoanService;
  let member: Member;
  let book: Book;
  let copy: BookCopy;

  beforeEach(() => {
    loanService = new LoanService();
    member = Member.create({
      email: 'test@example.com',
      name: 'Test User',
      phone: '090-1234-5678',
      address: 'Tokyo, Japan',
      birthDate: new Date('1990-01-01'),
      memberType: MemberType.GENERAL,
    });
    book = Book.create({
      isbn: new ISBN('9784000000000'),
      title: 'Test Book',
      author: 'Test Author',
    });
    copy = BookCopy.create({
      bookId: book.id,
      location: 'A-1-1',
    });
  });

  describe('checkOut', () => {
    it('should create a loan when member is eligible', () => {
      const result = loanService.checkOut(member, copy, []);
      expect(result.success).toBe(true);
      expect(result.loan).toBeDefined();
      expect(result.loan!.memberId.equals(member.id)).toBe(true);
      expect(result.loan!.copyId.equals(copy.id)).toBe(true);
    });

    it('should reject when member has reached loan limit', () => {
      // Create max loans for general member (5)
      const existingLoans: Loan[] = [];
      for (let i = 0; i < 5; i++) {
        const tempCopy = BookCopy.create({ bookId: book.id, location: `A-${i}` });
        existingLoans.push(Loan.create({ memberId: member.id, copyId: tempCopy.id }));
      }

      const result = loanService.checkOut(member, copy, existingLoans);
      expect(result.success).toBe(false);
      expect(result.error).toContain('loan limit');
    });

    it('should reject when copy is not available', () => {
      copy.checkout(); // Make copy unavailable
      const result = loanService.checkOut(member, copy, []);
      expect(result.success).toBe(false);
      expect(result.error).toContain('not available');
    });

    it('should reject when member is suspended', () => {
      member.suspend('Test suspension');
      const result = loanService.checkOut(member, copy, []);
      expect(result.success).toBe(false);
      expect(result.error).toContain('not eligible');
    });

    it('should allow students to borrow up to 10 books', () => {
      const student = Member.create({
        email: 'student@example.com',
        name: 'Student',
        phone: '090-5678-1234',
        address: 'Osaka, Japan',
        birthDate: new Date('2000-01-01'),
        memberType: MemberType.STUDENT,
      });

      const existingLoans: Loan[] = [];
      for (let i = 0; i < 9; i++) {
        const tempCopy = BookCopy.create({ bookId: book.id, location: `B-${i}` });
        existingLoans.push(Loan.create({ memberId: student.id, copyId: tempCopy.id }));
      }

      const result = loanService.checkOut(student, copy, existingLoans);
      expect(result.success).toBe(true);
    });
  });

  describe('returnBook', () => {
    it('should return book successfully', () => {
      const loan = Loan.create({ memberId: member.id, copyId: copy.id });
      copy.checkout();

      const result = loanService.returnBook(loan, copy);
      expect(result.success).toBe(true);
      expect(loan.status).toBe(LoanStatus.RETURNED);
      expect(copy.status).toBe(CopyStatus.AVAILABLE);
    });

    it('should calculate penalty for overdue return', () => {
      const loan = Loan.create({ memberId: member.id, copyId: copy.id });
      copy.checkout();
      
      // Set due date to past
      const pastDate = new Date();
      pastDate.setDate(pastDate.getDate() - 3);
      loan.setDueDateForTest(pastDate);

      const result = loanService.returnBook(loan, copy);
      expect(result.success).toBe(true);
      expect(result.penalty).toBeDefined();
      expect(result.penalty!.overdueDays).toBe(3);
      // 停止期間は overdueDays * 2 = 6日
      expect(result.penalty!.getRemainingDays()).toBeGreaterThan(0);
    });
  });

  describe('extendLoan', () => {
    it('should extend loan successfully', () => {
      const loan = Loan.create({ memberId: member.id, copyId: copy.id });
      const originalDueDate = new Date(loan.dueDate);

      const result = loanService.extendLoan(loan, []);
      expect(result.success).toBe(true);
      expect(loan.dueDate.getTime()).toBeGreaterThan(originalDueDate.getTime());
    });

    it('should reject extension when book is reserved', () => {
      const loan = Loan.create({ memberId: member.id, copyId: copy.id });
      const reservation = Reservation.create({
        memberId: MemberId.generate(),
        bookId: book.id,
        position: 1,
      });

      const result = loanService.extendLoan(loan, [reservation]);
      expect(result.success).toBe(false);
      expect(result.error).toContain('reserved');
    });

    it('should reject when max extensions reached', () => {
      const loan = Loan.create({ memberId: member.id, copyId: copy.id });
      loan.extend();
      loan.extend();

      const result = loanService.extendLoan(loan, []);
      expect(result.success).toBe(false);
      expect(result.error).toContain('Maximum');
    });
  });
});

// ============================================================
// ReservationService Tests
// ============================================================
describe('ReservationService', () => {
  let reservationService: ReservationService;
  let member: Member;
  let book: Book;

  beforeEach(() => {
    reservationService = new ReservationService();
    member = Member.create({
      email: 'test@example.com',
      name: 'Test User',
      phone: '090-1234-5678',
      address: 'Tokyo, Japan',
      birthDate: new Date('1990-01-01'),
      memberType: MemberType.GENERAL,
    });
    book = Book.create({
      isbn: new ISBN('9784000000000'),
      title: 'Test Book',
      author: 'Test Author',
    });
  });

  describe('createReservation', () => {
    it('should create reservation with correct position', () => {
      const existingReservations: Reservation[] = [];
      
      const result = reservationService.createReservation(member, book, existingReservations);
      expect(result.success).toBe(true);
      expect(result.reservation).toBeDefined();
      expect(result.reservation!.position).toBe(1);
    });

    it('should set position based on existing reservations', () => {
      const existingReservations = [
        Reservation.create({ memberId: MemberId.generate(), bookId: book.id, position: 1 }),
        Reservation.create({ memberId: MemberId.generate(), bookId: book.id, position: 2 }),
      ];

      const result = reservationService.createReservation(member, book, existingReservations);
      expect(result.success).toBe(true);
      expect(result.reservation!.position).toBe(3);
    });

    it('should reject when member is not eligible', () => {
      member.suspend('Test');
      const result = reservationService.createReservation(member, book, []);
      expect(result.success).toBe(false);
      expect(result.error).toContain('not eligible');
    });

    it('should reject duplicate reservation', () => {
      const existingReservations = [
        Reservation.create({ memberId: member.id, bookId: book.id, position: 1 }),
      ];

      const result = reservationService.createReservation(member, book, existingReservations);
      expect(result.success).toBe(false);
      expect(result.error).toContain('already reserved');
    });
  });

  describe('processReturn', () => {
    it('should mark first waiting reservation as ready', () => {
      const reservation1 = Reservation.create({ 
        memberId: MemberId.generate(), 
        bookId: book.id, 
        position: 1 
      });
      const reservation2 = Reservation.create({ 
        memberId: MemberId.generate(), 
        bookId: book.id, 
        position: 2 
      });

      const result = reservationService.processReturn(book.id, [reservation1, reservation2]);
      expect(result.notifiedReservation).toBeDefined();
      expect(result.notifiedReservation!.id.equals(reservation1.id)).toBe(true);
      expect(result.notifiedReservation!.status).toBe(ReservationStatus.READY);
    });

    it('should return null when no waiting reservations', () => {
      const result = reservationService.processReturn(book.id, []);
      expect(result.notifiedReservation).toBeNull();
    });
  });

  describe('cancelReservation', () => {
    it('should cancel and update positions', () => {
      const reservations = [
        Reservation.create({ memberId: MemberId.generate(), bookId: book.id, position: 1 }),
        Reservation.create({ memberId: MemberId.generate(), bookId: book.id, position: 2 }),
        Reservation.create({ memberId: MemberId.generate(), bookId: book.id, position: 3 }),
      ];

      const result = reservationService.cancelReservation(reservations[0], reservations);
      expect(result.success).toBe(true);
      expect(reservations[0].status).toBe(ReservationStatus.CANCELLED);
      expect(reservations[1].position).toBe(1);
      expect(reservations[2].position).toBe(2);
    });
  });
});

// ============================================================
// MemberService Tests
// ============================================================
describe('MemberService', () => {
  let memberService: MemberService;
  let member: Member;

  beforeEach(() => {
    memberService = new MemberService();
    member = Member.create({
      email: 'test@example.com',
      name: 'Test User',
      phone: '090-1234-5678',
      address: 'Tokyo, Japan',
      birthDate: new Date('1990-01-01'),
      memberType: MemberType.GENERAL,
    });
  });

  describe('applyPenalty', () => {
    it('should suspend member for penalty duration', () => {
      const penalty = Penalty.create({
        memberId: member.id,
        reason: 'Test penalty',
        overdueDays: 5,
      });

      memberService.applyPenalty(member, penalty);
      expect(member.status).toBe(MemberStatus.SUSPENDED);
    });
  });

  describe('checkEligibility', () => {
    it('should return eligible for active member', () => {
      const result = memberService.checkEligibility(member, []);
      expect(result.eligible).toBe(true);
    });

    it('should return not eligible when has unpaid penalties', () => {
      const penalty = Penalty.create({
        memberId: member.id,
        reason: 'Overdue penalty',
        overdueDays: 5,
      });

      const result = memberService.checkEligibility(member, [penalty]);
      expect(result.eligible).toBe(false);
      expect(result.reason).toContain('unpaid penalties');
    });

    it('should return not eligible when suspended', () => {
      member.suspend('Test');
      const result = memberService.checkEligibility(member, []);
      expect(result.eligible).toBe(false);
      expect(result.reason).toContain('suspended');
    });
  });

  describe('getRemainingLoanSlots', () => {
    it('should calculate remaining slots correctly', () => {
      const activeLoans = [
        Loan.create({ memberId: member.id, copyId: CopyId.generate() }),
        Loan.create({ memberId: member.id, copyId: CopyId.generate() }),
      ];

      const result = memberService.getRemainingLoanSlots(member, activeLoans);
      expect(result).toBe(3); // 5 (general limit) - 2
    });
  });
});
