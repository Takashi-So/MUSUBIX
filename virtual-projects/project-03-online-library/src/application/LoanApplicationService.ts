/**
 * Loan Application Service
 * @design DES-LIBRARY-001 §6.3
 * @task TSK-LIB-015
 */

import { Loan, LoanId } from '../domain/loan/Loan';
import { Reservation } from '../domain/loan/Reservation';
import { MemberId } from '../domain/member/Member';
import { BookId } from '../domain/book/Book';
import { CopyId } from '../domain/book/BookCopy';
import { LoanService } from '../domain/services/LoanService';
import { ReservationService } from '../domain/services/ReservationService';
import { BookRepository } from '../infrastructure/repositories/BookRepository';
import { MemberRepository } from '../infrastructure/repositories/MemberRepository';
import { LoanRepository } from '../infrastructure/repositories/LoanRepository';

export interface CheckoutCommand {
  memberId: string;
  copyId: string;
}

export interface CheckoutResult {
  success: boolean;
  loan?: Loan;
  error?: string;
}

export interface ReturnCommand {
  loanId: string;
}

export interface ReturnResult {
  success: boolean;
  overdueDays?: number;
  error?: string;
}

export interface ReserveCommand {
  memberId: string;
  bookId: string;
}

export interface ReserveResult {
  success: boolean;
  reservation?: Reservation;
  position?: number;
  error?: string;
}

export class LoanApplicationService {
  private readonly loanService: LoanService;
  private readonly reservationService: ReservationService;

  constructor(
    private readonly bookRepository: BookRepository,
    private readonly memberRepository: MemberRepository,
    private readonly loanRepository: LoanRepository
  ) {
    this.loanService = new LoanService();
    this.reservationService = new ReservationService();
  }

  async checkoutBook(command: CheckoutCommand): Promise<CheckoutResult> {
    try {
      // Find member and copy
      const member = await this.memberRepository.findById(new MemberId(command.memberId));
      if (!member) {
        return { success: false, error: 'Member not found' };
      }

      const copy = await this.bookRepository.findCopyById(new CopyId(command.copyId));
      if (!copy) {
        return { success: false, error: 'Copy not found' };
      }

      // Get active loans for member
      const activeLoans = await this.loanRepository.findActiveByMemberId(member.id);

      // Execute checkout via domain service
      const result = this.loanService.checkOut(member, copy, activeLoans);

      if (!result.success) {
        return { success: false, error: result.error };
      }

      // Save loan and update copy
      await this.loanRepository.save(result.loan!);
      await this.bookRepository.saveCopy(copy);

      return { success: true, loan: result.loan };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Checkout failed',
      };
    }
  }

  async returnBook(command: ReturnCommand): Promise<ReturnResult> {
    try {
      // Find loan
      const loan = await this.loanRepository.findById(new LoanId(command.loanId));
      if (!loan) {
        return { success: false, error: 'Loan not found' };
      }

      // Find copy
      const copy = await this.bookRepository.findCopyById(loan.copyId);
      if (!copy) {
        return { success: false, error: 'Copy not found' };
      }

      // Execute return via domain service
      const result = this.loanService.returnBook(loan, copy);

      // Save updates
      await this.loanRepository.save(loan);
      await this.bookRepository.saveCopy(copy);

      // Handle penalty if any
      if (result.penalty) {
        await this.memberRepository.savePenalty(result.penalty);
        return {
          success: true,
          overdueDays: result.penalty.overdueDays,
        };
      }

      return { success: true };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Return failed',
      };
    }
  }

  async reserveBook(command: ReserveCommand): Promise<ReserveResult> {
    try {
      // Find member and book
      const member = await this.memberRepository.findById(new MemberId(command.memberId));
      if (!member) {
        return { success: false, error: 'Member not found' };
      }

      const book = await this.bookRepository.findById(new BookId(command.bookId));
      if (!book) {
        return { success: false, error: 'Book not found' };
      }

      // Get existing reservations
      const existingReservations = await this.loanRepository.findWaitingReservationsByBookId(book.id);

      // Create reservation via domain service
      const result = this.reservationService.createReservation(
        member,
        book,
        existingReservations
      );

      if (!result.success) {
        return { success: false, error: result.error };
      }

      await this.loanRepository.saveReservation(result.reservation!);

      return {
        success: true,
        reservation: result.reservation,
        position: result.reservation!.position,
      };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Reservation failed',
      };
    }
  }

  async extendLoan(loanId: string): Promise<{ success: boolean; newDueDate?: Date; error?: string }> {
    try {
      const loan = await this.loanRepository.findById(new LoanId(loanId));
      if (!loan) {
        return { success: false, error: 'Loan not found' };
      }

      // Get book info to check reservations
      const copy = await this.bookRepository.findCopyById(loan.copyId);
      if (!copy) {
        return { success: false, error: 'Copy not found' };
      }

      const reservations = await this.loanRepository.findWaitingReservationsByBookId(copy.bookId);
      const result = this.loanService.extendLoan(loan, reservations);

      if (!result.success) {
        return { success: false, error: result.error };
      }

      await this.loanRepository.save(loan);
      return { success: true, newDueDate: loan.dueDate };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Extension failed',
      };
    }
  }

  async getMemberLoans(memberId: string): Promise<Loan[]> {
    return this.loanRepository.findActiveByMemberId(new MemberId(memberId));
  }

  async getMemberReservations(memberId: string): Promise<Reservation[]> {
    return this.loanRepository.findReservationsByMemberId(new MemberId(memberId));
  }
}
