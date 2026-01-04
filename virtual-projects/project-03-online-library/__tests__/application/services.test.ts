/**
 * Application Services Tests
 * @design DES-LIBRARY-001 §6 Application Services
 * @task TSK-LIB-013, TSK-LIB-014, TSK-LIB-015
 */
import { describe, it, expect, beforeEach } from 'vitest';
import { BookApplicationService } from '../../src/application/BookApplicationService';
import { LoanApplicationService } from '../../src/application/LoanApplicationService';
import { MemberApplicationService } from '../../src/application/MemberApplicationService';
import { InMemoryBookRepository } from '../../src/infrastructure/repositories/InMemoryBookRepository';
import { InMemoryMemberRepository } from '../../src/infrastructure/repositories/InMemoryMemberRepository';
import { InMemoryLoanRepository } from '../../src/infrastructure/repositories/InMemoryLoanRepository';
import { MemberType } from '../../src/domain/member/Member';

// ============================================================
// BookApplicationService Tests
// ============================================================
describe('BookApplicationService', () => {
  let service: BookApplicationService;
  let bookRepository: InMemoryBookRepository;

  beforeEach(() => {
    bookRepository = new InMemoryBookRepository();
    service = new BookApplicationService(bookRepository);
  });

  describe('registerBook', () => {
    it('should register a new book with copies', async () => {
      const result = await service.registerBook({
        isbn: '9784000000000',
        title: 'Test Book',
        author: 'Test Author',
        copyCount: 3,
        location: 'A-1',
      });

      expect(result.success).toBe(true);
      expect(result.book).toBeDefined();
      expect(result.copies?.length).toBe(3);
    });

    it('should reject duplicate ISBN', async () => {
      await service.registerBook({
        isbn: '9784000000000',
        title: 'Test Book',
        author: 'Test Author',
        copyCount: 1,
        location: 'A-1',
      });

      const result = await service.registerBook({
        isbn: '9784000000000',
        title: 'Another Book',
        author: 'Another Author',
        copyCount: 1,
        location: 'B-1',
      });

      expect(result.success).toBe(false);
      expect(result.error).toContain('already exists');
    });
  });

  describe('searchBooks', () => {
    it('should search books by title', async () => {
      await service.registerBook({
        isbn: '9784000000000',
        title: 'TypeScript Guide',
        author: 'John Doe',
        copyCount: 1,
        location: 'A-1',
      });

      const results = await service.searchBooks({ title: 'TypeScript' });
      expect(results.length).toBe(1);
    });
  });
});

// ============================================================
// MemberApplicationService Tests
// ============================================================
describe('MemberApplicationService', () => {
  let service: MemberApplicationService;
  let memberRepository: InMemoryMemberRepository;

  beforeEach(() => {
    memberRepository = new InMemoryMemberRepository();
    service = new MemberApplicationService(memberRepository);
  });

  describe('registerMember', () => {
    it('should register a new member', async () => {
      const result = await service.registerMember({
        email: 'test@example.com',
        name: 'Test User',
        phone: '090-1234-5678',
        address: 'Tokyo',
        birthDate: new Date('1990-01-01'),
        memberType: MemberType.GENERAL,
      });

      expect(result.success).toBe(true);
      expect(result.member).toBeDefined();
    });

    it('should reject duplicate email', async () => {
      await service.registerMember({
        email: 'test@example.com',
        name: 'Test User',
        phone: '090-1234-5678',
        address: 'Tokyo',
        birthDate: new Date('1990-01-01'),
        memberType: MemberType.GENERAL,
      });

      const result = await service.registerMember({
        email: 'test@example.com',
        name: 'Another User',
        phone: '090-5678-1234',
        address: 'Osaka',
        birthDate: new Date('1985-01-01'),
        memberType: MemberType.STUDENT,
      });

      expect(result.success).toBe(false);
      expect(result.error).toContain('already exists');
    });
  });
});

// ============================================================
// LoanApplicationService Tests
// ============================================================
describe('LoanApplicationService', () => {
  let service: LoanApplicationService;
  let bookRepository: InMemoryBookRepository;
  let memberRepository: InMemoryMemberRepository;
  let loanRepository: InMemoryLoanRepository;
  let bookService: BookApplicationService;
  let memberService: MemberApplicationService;

  beforeEach(async () => {
    bookRepository = new InMemoryBookRepository();
    memberRepository = new InMemoryMemberRepository();
    loanRepository = new InMemoryLoanRepository();
    bookService = new BookApplicationService(bookRepository);
    memberService = new MemberApplicationService(memberRepository);
    service = new LoanApplicationService(
      bookRepository,
      memberRepository,
      loanRepository
    );
  });

  describe('checkoutBook', () => {
    it('should checkout book successfully', async () => {
      // Setup: Register book and member
      const bookResult = await bookService.registerBook({
        isbn: '9784000000000',
        title: 'Test Book',
        author: 'Test Author',
        copies: 1,
        location: 'A-1',
      });
      const memberResult = await memberService.registerMember({
        email: 'test@example.com',
        name: 'Test User',
        phone: '090-1234-5678',
        address: 'Tokyo',
        birthDate: new Date('1990-01-01'),
        memberType: MemberType.GENERAL,
      });

      const result = await service.checkoutBook({
        memberId: memberResult.member!.id.value,
        copyId: bookResult.copies![0].id.value,
      });

      expect(result.success).toBe(true);
      expect(result.loan).toBeDefined();
    });
  });

  describe('returnBook', () => {
    it('should return book successfully', async () => {
      // Setup
      const bookResult = await bookService.registerBook({
        isbn: '9784000000000',
        title: 'Test Book',
        author: 'Test Author',
        copies: 1,
        location: 'A-1',
      });
      const memberResult = await memberService.registerMember({
        email: 'test@example.com',
        name: 'Test User',
        phone: '090-1234-5678',
        address: 'Tokyo',
        birthDate: new Date('1990-01-01'),
        memberType: MemberType.GENERAL,
      });
      const checkoutResult = await service.checkoutBook({
        memberId: memberResult.member!.id.value,
        copyId: bookResult.copies![0].id.value,
      });

      const result = await service.returnBook({
        loanId: checkoutResult.loan!.id.value,
      });

      expect(result.success).toBe(true);
    });
  });

  describe('reserveBook', () => {
    it('should create reservation', async () => {
      const bookResult = await bookService.registerBook({
        isbn: '9784000000000',
        title: 'Test Book',
        author: 'Test Author',
        copies: 1,
        location: 'A-1',
      });
      const memberResult = await memberService.registerMember({
        email: 'test@example.com',
        name: 'Test User',
        phone: '090-1234-5678',
        address: 'Tokyo',
        birthDate: new Date('1990-01-01'),
        memberType: MemberType.GENERAL,
      });

      const result = await service.reserveBook({
        memberId: memberResult.member!.id.value,
        bookId: bookResult.book!.id.value,
      });

      expect(result.success).toBe(true);
      expect(result.reservation).toBeDefined();
    });
  });
});
