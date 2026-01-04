/**
 * Book Repository Interface
 * @design DES-LIBRARY-001 §5.1
 */

import { Book, BookId, ISBN } from '../../domain/book/Book';
import { BookCopy, CopyId } from '../../domain/book/BookCopy';

export interface BookSearchCriteria {
  title?: string;
  author?: string;
  isbn?: string;
}

export interface BookRepository {
  save(book: Book): Promise<void>;
  findById(id: BookId): Promise<Book | null>;
  findByISBN(isbn: ISBN): Promise<Book | null>;
  search(criteria: BookSearchCriteria): Promise<Book[]>;
  findAll(): Promise<Book[]>;
  delete(id: BookId): Promise<void>;

  // Copy management
  saveCopy(copy: BookCopy): Promise<void>;
  findCopyById(id: CopyId): Promise<BookCopy | null>;
  findCopiesByBookId(bookId: BookId): Promise<BookCopy[]>;
  findAvailableCopies(bookId: BookId): Promise<BookCopy[]>;
  deleteCopy(id: CopyId): Promise<void>;
}
