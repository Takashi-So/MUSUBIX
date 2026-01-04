/**
 * Book Entity and ISBN Value Object Tests
 * @requirements REQ-BOOK-001, REQ-BOOK-004
 * @design DES-LIBRARY-001 §3.1
 * @task TSK-LIB-001, TSK-LIB-002
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { Book, BookId, ISBN } from '../../src/domain/book/Book';
import { BookCopy, CopyId, CopyStatus } from '../../src/domain/book/BookCopy';

describe('ISBN Value Object', () => {
  describe('creation', () => {
    it('should create valid ISBN-13', () => {
      const isbn = new ISBN('978-4-06-519981-7');
      expect(isbn.value).toBe('9784065199817');
    });

    it('should reject invalid ISBN format', () => {
      expect(() => new ISBN('invalid')).toThrow('Invalid ISBN format');
    });

    it('should reject ISBN with wrong checksum', () => {
      expect(() => new ISBN('978-4-06-519981-0')).toThrow('Invalid ISBN checksum');
    });

    it('should normalize ISBN with or without hyphens', () => {
      const isbn1 = new ISBN('978-4-06-519981-7');
      const isbn2 = new ISBN('9784065199817');
      expect(isbn1.equals(isbn2)).toBe(true);
    });
  });

  describe('equality', () => {
    it('should be equal for same ISBN', () => {
      const isbn1 = new ISBN('978-4-06-519981-7');
      const isbn2 = new ISBN('978-4-06-519981-7');
      expect(isbn1.equals(isbn2)).toBe(true);
    });

    it('should not be equal for different ISBN', () => {
      const isbn1 = new ISBN('978-4-06-519981-7');
      const isbn2 = new ISBN('978-4-00-310101-8');
      expect(isbn1.equals(isbn2)).toBe(false);
    });
  });
});

describe('Book Entity', () => {
  let validISBN: ISBN;

  beforeEach(() => {
    validISBN = new ISBN('978-4-06-519981-7');
  });

  describe('creation', () => {
    it('should create book with valid data', () => {
      const book = Book.create({
        isbn: validISBN,
        title: 'Clean Architecture',
        author: 'Robert C. Martin',
        publisher: 'Prentice Hall',
        publishYear: 2017,
        category: 'Technology',
        shelfLocation: 'A-1-01',
      });

      expect(book.id).toBeDefined();
      expect(book.isbn.equals(validISBN)).toBe(true);
      expect(book.title).toBe('Clean Architecture');
      expect(book.author).toBe('Robert C. Martin');
    });

    it('should generate unique BookId', () => {
      const book1 = Book.create({
        isbn: validISBN,
        title: 'Book 1',
        author: 'Author',
        publisher: 'Publisher',
        publishYear: 2020,
        category: 'Tech',
        shelfLocation: 'A-1',
      });
      const book2 = Book.create({
        isbn: new ISBN('978-4-00-310101-8'),
        title: 'Book 2',
        author: 'Author',
        publisher: 'Publisher',
        publishYear: 2021,
        category: 'Tech',
        shelfLocation: 'A-2',
      });
      expect(book1.id.equals(book2.id)).toBe(false);
    });

    it('should reject title exceeding 500 characters', () => {
      expect(() =>
        Book.create({
          isbn: validISBN,
          title: 'a'.repeat(501),
          author: 'Author',
          publisher: 'Publisher',
          publishYear: 2020,
          category: 'Tech',
          shelfLocation: 'A-1',
        })
      ).toThrow('Title must not exceed 500 characters');
    });

    it('should reject invalid publish year', () => {
      expect(() =>
        Book.create({
          isbn: validISBN,
          title: 'Title',
          author: 'Author',
          publisher: 'Publisher',
          publishYear: 3000,
          category: 'Tech',
          shelfLocation: 'A-1',
        })
      ).toThrow('Invalid publish year');
    });
  });

  describe('update', () => {
    it('should update book info', () => {
      const book = Book.create({
        isbn: validISBN,
        title: 'Original Title',
        author: 'Author',
        publisher: 'Publisher',
        publishYear: 2020,
        category: 'Tech',
        shelfLocation: 'A-1',
      });

      book.update({ title: 'Updated Title' });
      expect(book.title).toBe('Updated Title');
    });
  });
});

describe('BookCopy Entity', () => {
  let book: Book;

  beforeEach(() => {
    book = Book.create({
      isbn: new ISBN('978-4-06-519981-7'),
      title: 'Test Book',
      author: 'Author',
      publisher: 'Publisher',
      publishYear: 2020,
      category: 'Tech',
      shelfLocation: 'A-1',
    });
  });

  describe('creation', () => {
    it('should create copy with available status', () => {
      const copy = BookCopy.create({
        bookId: book.id,
        shelfLocation: 'A-1-01',
      });

      expect(copy.id).toBeDefined();
      expect(copy.status).toBe(CopyStatus.AVAILABLE);
      expect(copy.bookId.equals(book.id)).toBe(true);
    });
  });

  describe('status transitions', () => {
    it('should transition from available to on_loan', () => {
      const copy = BookCopy.create({
        bookId: book.id,
        shelfLocation: 'A-1-01',
      });

      copy.checkout();
      expect(copy.status).toBe(CopyStatus.ON_LOAN);
    });

    it('should transition from on_loan to available', () => {
      const copy = BookCopy.create({
        bookId: book.id,
        shelfLocation: 'A-1-01',
      });

      copy.checkout();
      copy.return();
      expect(copy.status).toBe(CopyStatus.AVAILABLE);
    });

    it('should transition to reserved', () => {
      const copy = BookCopy.create({
        bookId: book.id,
        shelfLocation: 'A-1-01',
      });

      copy.reserve();
      expect(copy.status).toBe(CopyStatus.RESERVED);
    });

    it('should transition to maintenance', () => {
      const copy = BookCopy.create({
        bookId: book.id,
        shelfLocation: 'A-1-01',
      });

      copy.setMaintenance();
      expect(copy.status).toBe(CopyStatus.MAINTENANCE);
    });

    it('should transition to retired', () => {
      const copy = BookCopy.create({
        bookId: book.id,
        shelfLocation: 'A-1-01',
      });

      copy.retire();
      expect(copy.status).toBe(CopyStatus.RETIRED);
      expect(copy.retiredAt).toBeDefined();
    });

    it('should not checkout if not available', () => {
      const copy = BookCopy.create({
        bookId: book.id,
        shelfLocation: 'A-1-01',
      });

      copy.checkout();
      expect(() => copy.checkout()).toThrow('Cannot checkout: book is not available');
    });

    it('should not retire if on loan', () => {
      const copy = BookCopy.create({
        bookId: book.id,
        shelfLocation: 'A-1-01',
      });

      copy.checkout();
      expect(() => copy.retire()).toThrow('Cannot retire: book has active loan');
    });
  });

  describe('availability check', () => {
    it('should be available when status is available', () => {
      const copy = BookCopy.create({
        bookId: book.id,
        shelfLocation: 'A-1-01',
      });

      expect(copy.isAvailable()).toBe(true);
    });

    it('should not be available when on loan', () => {
      const copy = BookCopy.create({
        bookId: book.id,
        shelfLocation: 'A-1-01',
      });

      copy.checkout();
      expect(copy.isAvailable()).toBe(false);
    });
  });
});

describe('BookId Value Object', () => {
  it('should generate unique ID', () => {
    const id1 = BookId.generate();
    const id2 = BookId.generate();
    expect(id1.equals(id2)).toBe(false);
  });

  it('should be equal for same ID value', () => {
    const id = BookId.generate();
    const id2 = new BookId(id.value);
    expect(id.equals(id2)).toBe(true);
  });
});
