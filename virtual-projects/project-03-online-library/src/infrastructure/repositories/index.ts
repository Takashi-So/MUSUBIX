/**
 * Repository Exports
 * @design DES-LIBRARY-001 §5 Repositories
 */

export type { BookRepository, BookSearchCriteria } from './BookRepository';
export { InMemoryBookRepository } from './InMemoryBookRepository';

export type { MemberRepository } from './MemberRepository';
export { InMemoryMemberRepository } from './InMemoryMemberRepository';

export type { LoanRepository } from './LoanRepository';
export { InMemoryLoanRepository } from './InMemoryLoanRepository';
