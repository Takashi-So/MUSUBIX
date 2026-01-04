/**
 * InMemory Book Repository Implementation
 * @design DES-LIBRARY-001 §5.1
 * @task TSK-LIB-010
 */

import { Book, BookId, ISBN } from '../../domain/book/Book';
import { BookCopy, CopyId, CopyStatus } from '../../domain/book/BookCopy';
import { BookRepository, BookSearchCriteria } from './BookRepository';

export class InMemoryBookRepository implements BookRepository {
  private books: Map<string, Book> = new Map();
  private copies: Map<string, BookCopy> = new Map();

  async save(book: Book): Promise<void> {
    this.books.set(book.id.value, book);
  }

  async findById(id: BookId): Promise<Book | null> {
    return this.books.get(id.value) || null;
  }

  async findByISBN(isbn: ISBN): Promise<Book | null> {
    for (const book of this.books.values()) {
      if (book.isbn.equals(isbn)) {
        return book;
      }
    }
    return null;
  }

  async search(criteria: BookSearchCriteria): Promise<Book[]> {
    const results: Book[] = [];
    for (const book of this.books.values()) {
      let matches = true;

      if (criteria.title) {
        matches = matches && book.title.toLowerCase().includes(criteria.title.toLowerCase());
      }
      if (criteria.author) {
        matches = matches && book.author.toLowerCase().includes(criteria.author.toLowerCase());
      }
      if (criteria.isbn) {
        matches = matches && book.isbn.value.includes(criteria.isbn);
      }

      if (matches) {
        results.push(book);
      }
    }
    return results;
  }

  async findAll(): Promise<Book[]> {
    return Array.from(this.books.values());
  }

  async delete(id: BookId): Promise<void> {
    this.books.delete(id.value);
  }

  // Copy management
  async saveCopy(copy: BookCopy): Promise<void> {
    this.copies.set(copy.id.value, copy);
  }

  async findCopyById(id: CopyId): Promise<BookCopy | null> {
    return this.copies.get(id.value) || null;
  }

  async findCopiesByBookId(bookId: BookId): Promise<BookCopy[]> {
    const results: BookCopy[] = [];
    for (const copy of this.copies.values()) {
      if (copy.bookId.equals(bookId)) {
        results.push(copy);
      }
    }
    return results;
  }

  async findAvailableCopies(bookId: BookId): Promise<BookCopy[]> {
    const results: BookCopy[] = [];
    for (const copy of this.copies.values()) {
      if (copy.bookId.equals(bookId) && copy.status === CopyStatus.AVAILABLE) {
        results.push(copy);
      }
    }
    return results;
  }

  async deleteCopy(id: CopyId): Promise<void> {
    this.copies.delete(id.value);
  }
}
