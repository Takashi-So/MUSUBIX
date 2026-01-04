/**
 * Repository Tests
 * @design DES-LIBRARY-001 §5 Repositories
 * @task TSK-LIB-010, TSK-LIB-011, TSK-LIB-012
 */
import { describe, it, expect, beforeEach } from 'vitest';
import { InMemoryBookRepository } from '../../src/infrastructure/repositories/InMemoryBookRepository';
import { InMemoryMemberRepository } from '../../src/infrastructure/repositories/InMemoryMemberRepository';
import { InMemoryLoanRepository } from '../../src/infrastructure/repositories/InMemoryLoanRepository';
import { Book, ISBN, BookId } from '../../src/domain/book/Book';
import { BookCopy, CopyId } from '../../src/domain/book/BookCopy';
import { Member, MemberId, MemberType } from '../../src/domain/member/Member';
import { Loan, LoanId } from '../../src/domain/loan/Loan';
import { Reservation, ReservationId } from '../../src/domain/loan/Reservation';

// ============================================================
// BookRepository Tests
// ============================================================
describe('InMemoryBookRepository', () => {
  let repository: InMemoryBookRepository;
  let book: Book;
  let copy: BookCopy;

  beforeEach(() => {
    repository = new InMemoryBookRepository();
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

  describe('save and findById', () => {
    it('should save and retrieve a book', async () => {
      await repository.save(book);
      const found = await repository.findById(book.id);
      expect(found).toBeDefined();
      expect(found!.id.equals(book.id)).toBe(true);
    });

    it('should return null for non-existent book', async () => {
      const found = await repository.findById(BookId.generate());
      expect(found).toBeNull();
    });
  });

  describe('findByISBN', () => {
    it('should find book by ISBN', async () => {
      await repository.save(book);
      const found = await repository.findByISBN(book.isbn);
      expect(found).toBeDefined();
      expect(found!.isbn.equals(book.isbn)).toBe(true);
    });
  });

  describe('search', () => {
    it('should search books by title', async () => {
      await repository.save(book);
      const results = await repository.search({ title: 'Test' });
      expect(results.length).toBe(1);
    });

    it('should search books by author', async () => {
      await repository.save(book);
      const results = await repository.search({ author: 'Author' });
      expect(results.length).toBe(1);
    });
  });

  describe('copy management', () => {
    it('should save and find copies', async () => {
      await repository.save(book);
      await repository.saveCopy(copy);
      const copies = await repository.findCopiesByBookId(book.id);
      expect(copies.length).toBe(1);
    });

    it('should find available copies', async () => {
      await repository.save(book);
      await repository.saveCopy(copy);
      const available = await repository.findAvailableCopies(book.id);
      expect(available.length).toBe(1);
    });
  });
});

// ============================================================
// MemberRepository Tests
// ============================================================
describe('InMemoryMemberRepository', () => {
  let repository: InMemoryMemberRepository;
  let member: Member;

  beforeEach(() => {
    repository = new InMemoryMemberRepository();
    member = Member.create({
      email: 'test@example.com',
      name: 'Test User',
      phone: '090-1234-5678',
      address: 'Tokyo, Japan',
      birthDate: new Date('1990-01-01'),
      memberType: MemberType.GENERAL,
    });
  });

  describe('save and findById', () => {
    it('should save and retrieve a member', async () => {
      await repository.save(member);
      const found = await repository.findById(member.id);
      expect(found).toBeDefined();
      expect(found!.id.equals(member.id)).toBe(true);
    });
  });

  describe('findByEmail', () => {
    it('should find member by email', async () => {
      await repository.save(member);
      const found = await repository.findByEmail('test@example.com');
      expect(found).toBeDefined();
      expect(found!.email).toBe('test@example.com');
    });
  });

  describe('findActiveMembers', () => {
    it('should return only active members', async () => {
      await repository.save(member);
      const suspendedMember = Member.create({
        email: 'suspended@example.com',
        name: 'Suspended User',
        phone: '090-5678-1234',
        address: 'Osaka, Japan',
        birthDate: new Date('1985-01-01'),
        memberType: MemberType.GENERAL,
      });
      suspendedMember.suspend('Test');
      await repository.save(suspendedMember);

      const activeMembers = await repository.findActiveMembers();
      expect(activeMembers.length).toBe(1);
    });
  });
});

// ============================================================
// LoanRepository Tests
// ============================================================
describe('InMemoryLoanRepository', () => {
  let repository: InMemoryLoanRepository;
  let memberId: MemberId;
  let copyId: CopyId;
  let bookId: BookId;
  let loan: Loan;

  beforeEach(() => {
    repository = new InMemoryLoanRepository();
    memberId = MemberId.generate();
    copyId = CopyId.generate();
    bookId = BookId.generate();
    loan = Loan.create({ memberId, copyId });
  });

  describe('save and findById', () => {
    it('should save and retrieve a loan', async () => {
      await repository.save(loan);
      const found = await repository.findById(loan.id);
      expect(found).toBeDefined();
      expect(found!.id.equals(loan.id)).toBe(true);
    });
  });

  describe('findActiveByMemberId', () => {
    it('should find active loans for member', async () => {
      await repository.save(loan);
      const activeLoans = await repository.findActiveByMemberId(memberId);
      expect(activeLoans.length).toBe(1);
    });

    it('should not include returned loans', async () => {
      loan.return();
      await repository.save(loan);
      const activeLoans = await repository.findActiveByMemberId(memberId);
      expect(activeLoans.length).toBe(0);
    });
  });

  describe('findOverdueLoans', () => {
    it('should find overdue loans', async () => {
      const pastDate = new Date();
      pastDate.setDate(pastDate.getDate() - 20);
      loan.setDueDateForTest(pastDate);
      loan.markOverdue();
      await repository.save(loan);

      const overdueLoans = await repository.findOverdueLoans();
      expect(overdueLoans.length).toBe(1);
    });
  });

  describe('reservation management', () => {
    it('should save and find reservations', async () => {
      const reservation = Reservation.create({
        memberId,
        bookId,
        position: 1,
      });
      await repository.saveReservation(reservation);

      const found = await repository.findReservationById(reservation.id);
      expect(found).toBeDefined();
    });

    it('should find waiting reservations by book', async () => {
      const reservation = Reservation.create({
        memberId,
        bookId,
        position: 1,
      });
      await repository.saveReservation(reservation);

      const waiting = await repository.findWaitingReservationsByBookId(bookId);
      expect(waiting.length).toBe(1);
    });
  });
});
