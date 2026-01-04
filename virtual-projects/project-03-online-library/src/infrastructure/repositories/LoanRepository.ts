/**
 * Loan Repository Interface
 * @design DES-LIBRARY-001 §5.3
 */

import { Loan, LoanId } from '../../domain/loan/Loan';
import { Reservation, ReservationId } from '../../domain/loan/Reservation';
import { MemberId } from '../../domain/member/Member';
import { CopyId } from '../../domain/book/BookCopy';
import { BookId } from '../../domain/book/Book';

export interface LoanRepository {
  save(loan: Loan): Promise<void>;
  findById(id: LoanId): Promise<Loan | null>;
  findActiveByMemberId(memberId: MemberId): Promise<Loan[]>;
  findActiveByCopyId(copyId: CopyId): Promise<Loan | null>;
  findOverdueLoans(): Promise<Loan[]>;
  findAll(): Promise<Loan[]>;

  // Reservation management
  saveReservation(reservation: Reservation): Promise<void>;
  findReservationById(id: ReservationId): Promise<Reservation | null>;
  findReservationsByMemberId(memberId: MemberId): Promise<Reservation[]>;
  findWaitingReservationsByBookId(bookId: BookId): Promise<Reservation[]>;
  findReadyReservationsByBookId(bookId: BookId): Promise<Reservation[]>;
}
