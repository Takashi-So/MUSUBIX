/**
 * Book Application Service
 * @design DES-LIBRARY-001 §6.1
 * @task TSK-LIB-013
 */

import { Book, ISBN } from '../domain/book/Book';
import { BookCopy } from '../domain/book/BookCopy';
import { BookRepository, BookSearchCriteria } from '../infrastructure/repositories/BookRepository';

export interface RegisterBookCommand {
  isbn: string;
  title: string;
  author: string;
  publisher?: string;
  publishedYear?: number;
  copyCount: number;
  location?: string;
}

export interface RegisterBookResult {
  success: boolean;
  book?: Book;
  copies?: BookCopy[];
  error?: string;
}

export class BookApplicationService {
  constructor(private readonly bookRepository: BookRepository) {}

  async registerBook(command: RegisterBookCommand): Promise<RegisterBookResult> {
    try {
      const isbn = new ISBN(command.isbn);

      // Check for duplicate ISBN
      const existing = await this.bookRepository.findByISBN(isbn);
      if (existing) {
        return {
          success: false,
          error: 'Book with this ISBN already exists',
        };
      }

      // Create book
      const book = Book.create({
        isbn,
        title: command.title,
        author: command.author,
        publisher: command.publisher,
        publishedYear: command.publishedYear,
      });

      await this.bookRepository.save(book);

      // Create copies
      const copies: BookCopy[] = [];
      const copyCount = command.copyCount || 1;
      for (let i = 0; i < copyCount; i++) {
        const copy = BookCopy.create({
          bookId: book.id,
          location: command.location ? `${command.location}-${i + 1}` : `SHELF-${i + 1}`,
        });
        await this.bookRepository.saveCopy(copy);
        copies.push(copy);
      }

      return { success: true, book, copies };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Failed to register book',
      };
    }
  }

  async searchBooks(criteria: BookSearchCriteria): Promise<Book[]> {
    return this.bookRepository.search(criteria);
  }

  async getBookById(bookId: string): Promise<Book | null> {
    const { BookId } = await import('../domain/book/Book');
    return this.bookRepository.findById(new BookId(bookId));
  }

  async getAvailableCopies(bookId: string): Promise<BookCopy[]> {
    const { BookId } = await import('../domain/book/Book');
    return this.bookRepository.findAvailableCopies(new BookId(bookId));
  }
}
