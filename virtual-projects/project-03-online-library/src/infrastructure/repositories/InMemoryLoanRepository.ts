/**
 * InMemory Loan Repository Implementation
 * @design DES-LIBRARY-001 §5.3
 * @task TSK-LIB-012
 */

import { Loan, LoanId, LoanStatus } from '../../domain/loan/Loan';
import { Reservation, ReservationId, ReservationStatus } from '../../domain/loan/Reservation';
import { MemberId } from '../../domain/member/Member';
import { CopyId } from '../../domain/book/BookCopy';
import { BookId } from '../../domain/book/Book';
import { LoanRepository } from './LoanRepository';

export class InMemoryLoanRepository implements LoanRepository {
  private loans: Map<string, Loan> = new Map();
  private reservations: Map<string, Reservation> = new Map();

  async save(loan: Loan): Promise<void> {
    this.loans.set(loan.id.value, loan);
  }

  async findById(id: LoanId): Promise<Loan | null> {
    return this.loans.get(id.value) || null;
  }

  async findActiveByMemberId(memberId: MemberId): Promise<Loan[]> {
    const results: Loan[] = [];
    for (const loan of this.loans.values()) {
      if (
        loan.memberId.equals(memberId) &&
        (loan.status === LoanStatus.ACTIVE || loan.status === LoanStatus.OVERDUE)
      ) {
        results.push(loan);
      }
    }
    return results;
  }

  async findActiveByCopyId(copyId: CopyId): Promise<Loan | null> {
    for (const loan of this.loans.values()) {
      if (
        loan.copyId.equals(copyId) &&
        (loan.status === LoanStatus.ACTIVE || loan.status === LoanStatus.OVERDUE)
      ) {
        return loan;
      }
    }
    return null;
  }

  async findOverdueLoans(): Promise<Loan[]> {
    const results: Loan[] = [];
    for (const loan of this.loans.values()) {
      if (loan.status === LoanStatus.OVERDUE) {
        results.push(loan);
      }
    }
    return results;
  }

  async findAll(): Promise<Loan[]> {
    return Array.from(this.loans.values());
  }

  // Reservation management
  async saveReservation(reservation: Reservation): Promise<void> {
    this.reservations.set(reservation.id.value, reservation);
  }

  async findReservationById(id: ReservationId): Promise<Reservation | null> {
    return this.reservations.get(id.value) || null;
  }

  async findReservationsByMemberId(memberId: MemberId): Promise<Reservation[]> {
    const results: Reservation[] = [];
    for (const reservation of this.reservations.values()) {
      if (reservation.memberId.equals(memberId)) {
        results.push(reservation);
      }
    }
    return results;
  }

  async findWaitingReservationsByBookId(bookId: BookId): Promise<Reservation[]> {
    const results: Reservation[] = [];
    for (const reservation of this.reservations.values()) {
      if (
        reservation.bookId.equals(bookId) &&
        reservation.status === ReservationStatus.WAITING
      ) {
        results.push(reservation);
      }
    }
    return results.sort((a, b) => a.position - b.position);
  }

  async findReadyReservationsByBookId(bookId: BookId): Promise<Reservation[]> {
    const results: Reservation[] = [];
    for (const reservation of this.reservations.values()) {
      if (
        reservation.bookId.equals(bookId) &&
        reservation.status === ReservationStatus.READY
      ) {
        results.push(reservation);
      }
    }
    return results;
  }
}
