/**
 * API Tests
 * @task TSK-LIB-019 to TSK-LIB-024
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { Hono } from 'hono';
import { createApp } from '../../src/api/app';
import { InMemoryBookRepository } from '../../src/infrastructure/repositories/InMemoryBookRepository';
import { InMemoryMemberRepository } from '../../src/infrastructure/repositories/InMemoryMemberRepository';
import { InMemoryLoanRepository } from '../../src/infrastructure/repositories/InMemoryLoanRepository';

describe('REST API', () => {
  let app: Hono;
  let bookRepository: InMemoryBookRepository;
  let memberRepository: InMemoryMemberRepository;
  let loanRepository: InMemoryLoanRepository;

  beforeEach(() => {
    bookRepository = new InMemoryBookRepository();
    memberRepository = new InMemoryMemberRepository();
    loanRepository = new InMemoryLoanRepository();
    app = createApp({ bookRepository, memberRepository, loanRepository });
  });

  describe('POST /api/books', () => {
    it('should register a new book', async () => {
      const res = await app.request('/api/books', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          isbn: '978-0-13-468599-1',
          title: 'Test Book',
          author: 'Test Author',
          publisher: 'Test Publisher',
          publishedYear: 2024,
          copies: 3,
        }),
      });

      expect(res.status).toBe(201);
      const body = await res.json();
      expect(body.success).toBe(true);
      expect(body.book.title).toBe('Test Book');
      expect(body.copies.length).toBe(3);
    });

    it('should return 400 for invalid ISBN', async () => {
      const res = await app.request('/api/books', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          isbn: 'invalid-isbn',
          title: 'Test',
          author: 'Test',
          publisher: 'Test',
          publishedYear: 2024,
          copies: 1,
        }),
      });

      expect(res.status).toBe(400);
    });
  });

  describe('GET /api/books', () => {
    it('should search books', async () => {
      // First register a book
      await app.request('/api/books', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          isbn: '978-0-321-12521-7',
          title: 'Domain-Driven Design',
          author: 'Eric Evans',
          publisher: 'Addison-Wesley',
          publishedYear: 2003,
          copies: 2,
        }),
      });

      const res = await app.request('/api/books?query=Domain');
      expect(res.status).toBe(200);
      const body = await res.json();
      expect(body.books.length).toBeGreaterThan(0);
    });
  });

  describe('POST /api/members', () => {
    it('should register a new member', async () => {
      const res = await app.request('/api/members', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          name: 'John Doe',
          email: 'john@example.com',
          phone: '090-1234-5678',
          address: 'Tokyo, Japan',
          birthDate: '1990-01-15',
          memberType: 'GENERAL',
        }),
      });

      expect(res.status).toBe(201);
      const body = await res.json();
      expect(body.success).toBe(true);
      expect(body.member.name).toBe('John Doe');
    });

    it('should return 400 for duplicate email', async () => {
      const memberData = {
        name: 'John Doe',
        email: 'john@example.com',
        phone: '090-1234-5678',
        address: 'Tokyo',
        birthDate: '1990-01-15',
        memberType: 'GENERAL',
      };

      await app.request('/api/members', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(memberData),
      });

      const res = await app.request('/api/members', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(memberData),
      });

      expect(res.status).toBe(400);
    });
  });

  describe('POST /api/loans/checkout', () => {
    it('should checkout a book', async () => {
      // Setup: register book and member
      const bookRes = await app.request('/api/books', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          isbn: '978-0-13-468599-1',
          title: 'Test Book',
          author: 'Test Author',
          publisher: 'Publisher',
          publishedYear: 2024,
          copies: 1,
        }),
      });
      const bookData = await bookRes.json();

      const memberRes = await app.request('/api/members', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          name: 'Test User',
          email: 'test@example.com',
          phone: '090-0000-0000',
          address: 'Address',
          birthDate: '1990-01-01',
          memberType: 'GENERAL',
        }),
      });
      const memberData = await memberRes.json();

      // Checkout
      const res = await app.request('/api/loans/checkout', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          memberId: memberData.member.id,
          copyId: bookData.copies[0].id,
        }),
      });

      expect(res.status).toBe(201);
      const body = await res.json();
      expect(body.success).toBe(true);
      expect(body.loan).toBeDefined();
    });
  });

  describe('POST /api/loans/return', () => {
    it('should return a book', async () => {
      // Setup
      const bookRes = await app.request('/api/books', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          isbn: '978-0-596-51774-8',
          title: 'Test',
          author: 'Author',
          publisher: 'Pub',
          publishedYear: 2024,
          copies: 1,
        }),
      });
      const bookData = await bookRes.json();

      const memberRes = await app.request('/api/members', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          name: 'User',
          email: 'user@test.com',
          phone: '090-1111-1111',
          address: 'Addr',
          birthDate: '1990-01-01',
          memberType: 'GENERAL',
        }),
      });
      const memberData = await memberRes.json();

      const checkoutRes = await app.request('/api/loans/checkout', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          memberId: memberData.member.id,
          copyId: bookData.copies[0].id,
        }),
      });
      const checkoutData = await checkoutRes.json();

      // Return
      const res = await app.request('/api/loans/return', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          loanId: checkoutData.loan.id,
        }),
      });

      expect(res.status).toBe(200);
      const body = await res.json();
      expect(body.success).toBe(true);
    });
  });

  describe('GET /api/health', () => {
    it('should return health status', async () => {
      const res = await app.request('/api/health');
      expect(res.status).toBe(200);
      const body = await res.json();
      expect(body.status).toBe('healthy');
    });
  });
});
