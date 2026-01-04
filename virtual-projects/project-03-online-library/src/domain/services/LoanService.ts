/**
 * LoanService - 貸出ドメインサービス
 * @requirements REQ-LOAN-001, REQ-LOAN-002, REQ-LOAN-003, REQ-LOAN-004, REQ-LOAN-005
 * @design DES-LIBRARY-001 §4.1 LoanService
 * @task TSK-LIB-007
 */

import { Loan } from '../loan/Loan';
import { Reservation } from '../loan/Reservation';
import { Member } from '../member/Member';
import { Penalty } from '../member/Penalty';
import { BookCopy, CopyStatus } from '../book/BookCopy';

export interface CheckOutResult {
  success: boolean;
  loan?: Loan;
  error?: string;
}

export interface ReturnResult {
  success: boolean;
  penalty?: Penalty;
  error?: string;
}

export interface ExtendResult {
  success: boolean;
  error?: string;
}

/**
 * LoanService - 貸出ビジネスロジック
 * 
 * @requirements REQ-LOAN-001 貸出処理
 * @requirements REQ-LOAN-002 返却処理
 * @requirements REQ-LOAN-003 延長処理（最大2回、予約なし）
 * @requirements REQ-LOAN-004 延滞時ペナルティ
 */
export class LoanService {
  /**
   * 貸出処理
   * @requirements REQ-LOAN-001
   */
  checkOut(member: Member, copy: BookCopy, activeLoans: Loan[]): CheckOutResult {
    // 会員が貸出可能か確認
    if (!member.isEligibleForLoan()) {
      return {
        success: false,
        error: 'Member is not eligible to borrow',
      };
    }

    // 貸出上限チェック
    const memberLoans = activeLoans.filter((loan) =>
      loan.memberId.equals(member.id)
    );
    if (memberLoans.length >= member.getLoanLimit()) {
      return {
        success: false,
        error: 'Member has reached loan limit',
      };
    }

    // 蔵書が貸出可能か確認
    if (copy.status !== CopyStatus.AVAILABLE) {
      return {
        success: false,
        error: 'Copy is not available',
      };
    }

    // 貸出実行
    const loan = Loan.create({
      memberId: member.id,
      copyId: copy.id,
    });
    copy.checkout();

    return {
      success: true,
      loan,
    };
  }

  /**
   * 返却処理
   * @requirements REQ-LOAN-002, REQ-LOAN-004
   */
  returnBook(loan: Loan, copy: BookCopy): ReturnResult {
    // 延滞日数チェック
    const overdueDays = loan.getOverdueDays();
    
    // 返却処理
    loan.return();
    copy.return();

    // 延滞ペナルティの作成
    if (overdueDays > 0) {
      const penalty = Penalty.create({
        memberId: loan.memberId,
        reason: `Overdue: ${overdueDays} days late`,
        overdueDays,
      });

      return {
        success: true,
        penalty,
      };
    }

    return { success: true };
  }

  /**
   * 延長処理
   * @requirements REQ-LOAN-003 (最大2回、14日間、予約者がいない場合のみ)
   */
  extendLoan(loan: Loan, reservationsForBook: Reservation[]): ExtendResult {
    // 予約がある場合は延長不可
    const activeReservations = reservationsForBook.filter(
      (r) =>
        r.status === 'waiting' || r.status === 'ready'
    );
    if (activeReservations.length > 0) {
      return {
        success: false,
        error: 'Cannot extend: book is reserved by other members',
      };
    }

    // 延長可能かチェック
    if (!loan.canExtend()) {
      return {
        success: false,
        error: 'Maximum extensions reached or loan not active',
      };
    }

    try {
      loan.extend();
      return { success: true };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Extension failed',
      };
    }
  }

  /**
   * 延滞貸出の検出とマーク
   * @requirements REQ-LOAN-004
   */
  processOverdueLoans(activeLoans: Loan[]): Loan[] {
    const overdueLoans: Loan[] = [];

    for (const loan of activeLoans) {
      if (loan.getOverdueDays() > 0 && loan.status !== 'overdue') {
        loan.markOverdue();
        overdueLoans.push(loan);
      }
    }

    return overdueLoans;
  }
}
