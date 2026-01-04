/**
 * REST API - Hono Application
 * @design DES-LIBRARY-001 §8
 * @task TSK-LIB-019 to TSK-LIB-024
 */

import { Hono } from 'hono';
import { cors } from 'hono/cors';
import { logger } from 'hono/logger';
import { BookApplicationService } from '../application/BookApplicationService';
import { MemberApplicationService } from '../application/MemberApplicationService';
import { LoanApplicationService } from '../application/LoanApplicationService';
import { BookRepository } from '../infrastructure/repositories/BookRepository';
import { MemberRepository } from '../infrastructure/repositories/MemberRepository';
import { LoanRepository } from '../infrastructure/repositories/LoanRepository';

export interface AppDependencies {
  bookRepository: BookRepository;
  memberRepository: MemberRepository;
  loanRepository: LoanRepository;
}

export function createApp(deps: AppDependencies): Hono {
  const app = new Hono();

  // Services
  const bookService = new BookApplicationService(deps.bookRepository);
  const memberService = new MemberApplicationService(deps.memberRepository);
  const loanService = new LoanApplicationService(
    deps.bookRepository,
    deps.memberRepository,
    deps.loanRepository
  );

  // Middleware
  app.use('*', cors());
  app.use('*', logger());

  // Health check
  app.get('/api/health', (c) => {
    return c.json({ status: 'healthy', timestamp: new Date().toISOString() });
  });

  // === Book Routes ===

  // Register book
  app.post('/api/books', async (c) => {
    try {
      const body = await c.req.json();
      const result = await bookService.registerBook({
        isbn: body.isbn,
        title: body.title,
        author: body.author,
        publisher: body.publisher,
        publishedYear: body.publishedYear,
        copyCount: body.copies || 1,
      });

      if (!result.success) {
        return c.json({ success: false, error: result.error }, 400);
      }

      return c.json({
        success: true,
        book: {
          id: result.book!.id.value,
          isbn: result.book!.isbn.value,
          title: result.book!.title,
          author: result.book!.author,
        },
        copies: result.copies!.map((copy) => ({
          id: copy.id.value,
          status: copy.status,
        })),
      }, 201);
    } catch (error) {
      return c.json({ success: false, error: 'Invalid request' }, 400);
    }
  });

  // Search books
  app.get('/api/books', async (c) => {
    const query = c.req.query('query') || '';
    const books = await bookService.searchBooks({ query });
    return c.json({
      books: books.map((b) => ({
        id: b.id.value,
        isbn: b.isbn.value,
        title: b.title,
        author: b.author,
      })),
    });
  });

  // Get book by ID
  app.get('/api/books/:id', async (c) => {
    const book = await bookService.getBookById(c.req.param('id'));
    if (!book) {
      return c.json({ error: 'Book not found' }, 404);
    }
    return c.json({
      id: book.id.value,
      isbn: book.isbn.value,
      title: book.title,
      author: book.author,
      publisher: book.publisher,
      publishedYear: book.publishedYear,
    });
  });

  // === Member Routes ===

  // Register member
  app.post('/api/members', async (c) => {
    try {
      const body = await c.req.json();
      const result = await memberService.registerMember({
        name: body.name,
        email: body.email,
        phone: body.phone,
        address: body.address,
        birthDate: new Date(body.birthDate),
        memberType: body.memberType,
      });

      if (!result.success) {
        return c.json({ success: false, error: result.error }, 400);
      }

      return c.json({
        success: true,
        member: {
          id: result.member!.id.value,
          name: result.member!.name,
          email: result.member!.email,
          memberType: result.member!.memberType,
        },
      }, 201);
    } catch (error) {
      return c.json({ success: false, error: 'Invalid request' }, 400);
    }
  });

  // Get member by ID
  app.get('/api/members/:id', async (c) => {
    const member = await memberService.getMemberById(c.req.param('id'));
    if (!member) {
      return c.json({ error: 'Member not found' }, 404);
    }
    return c.json({
      id: member.id.value,
      name: member.name,
      email: member.email,
      memberType: member.memberType,
      loanCount: member.loanCount,
    });
  });

  // === Loan Routes ===

  // Checkout book
  app.post('/api/loans/checkout', async (c) => {
    try {
      const body = await c.req.json();
      const result = await loanService.checkoutBook({
        memberId: body.memberId,
        copyId: body.copyId,
      });

      if (!result.success) {
        return c.json({ success: false, error: result.error }, 400);
      }

      return c.json({
        success: true,
        loan: {
          id: result.loan!.id.value,
          dueDate: result.loan!.dueDate.toISOString(),
        },
      }, 201);
    } catch (error) {
      return c.json({ success: false, error: 'Checkout failed' }, 400);
    }
  });

  // Return book
  app.post('/api/loans/return', async (c) => {
    try {
      const body = await c.req.json();
      const result = await loanService.returnBook({
        loanId: body.loanId,
      });

      if (!result.success) {
        return c.json({ success: false, error: result.error }, 400);
      }

      return c.json({
        success: true,
        overdueDays: result.overdueDays,
      });
    } catch (error) {
      return c.json({ success: false, error: 'Return failed' }, 400);
    }
  });

  // Reserve book
  app.post('/api/reservations', async (c) => {
    try {
      const body = await c.req.json();
      const result = await loanService.reserveBook({
        memberId: body.memberId,
        bookId: body.bookId,
      });

      if (!result.success) {
        return c.json({ success: false, error: result.error }, 400);
      }

      return c.json({
        success: true,
        reservation: {
          id: result.reservation!.id.value,
          position: result.position,
        },
      }, 201);
    } catch (error) {
      return c.json({ success: false, error: 'Reservation failed' }, 400);
    }
  });

  // Get member loans
  app.get('/api/members/:id/loans', async (c) => {
    const loans = await loanService.getMemberLoans(c.req.param('id'));
    return c.json({
      loans: loans.map((loan) => ({
        id: loan.id.value,
        copyId: loan.copyId.value,
        borrowedAt: loan.borrowedAt.toISOString(),
        dueDate: loan.dueDate.toISOString(),
        status: loan.status,
      })),
    });
  });

  return app;
}
