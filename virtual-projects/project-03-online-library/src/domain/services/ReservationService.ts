/**
 * ReservationService - 予約ドメインサービス
 * @requirements REQ-RESERVE-001, REQ-RESERVE-002, REQ-RESERVE-003, REQ-RESERVE-004, REQ-RESERVE-005
 * @design DES-LIBRARY-001 §4.2 ReservationService
 * @task TSK-LIB-008
 */

import { BookId } from '../book/Book';
import { Reservation, ReservationStatus } from '../loan/Reservation';
import { Member } from '../member/Member';
import { Book } from '../book/Book';

export interface CreateReservationResult {
  success: boolean;
  reservation?: Reservation;
  error?: string;
}

export interface ProcessReturnResult {
  notifiedReservation: Reservation | null;
}

export interface CancelReservationResult {
  success: boolean;
  error?: string;
}

/**
 * ReservationService - 予約ビジネスロジック
 * 
 * @requirements REQ-RESERVE-001 予約キュー管理
 * @requirements REQ-RESERVE-002 貸出可能通知
 * @requirements REQ-RESERVE-003 予約からの貸出
 * @requirements REQ-RESERVE-005 予約期限管理
 */
export class ReservationService {
  /**
   * 予約作成
   * @requirements REQ-RESERVE-001
   */
  createReservation(
    member: Member,
    book: Book,
    existingReservations: Reservation[]
  ): CreateReservationResult {
    // 会員が予約可能か確認
    if (!member.isEligibleForLoan()) {
      return {
        success: false,
        error: 'Member is not eligible to reserve',
      };
    }

    // 同じ本への重複予約チェック
    const hasDuplicate = existingReservations.some(
      (r) =>
        r.memberId.equals(member.id) &&
        r.bookId.equals(book.id) &&
        (r.status === ReservationStatus.WAITING || r.status === ReservationStatus.READY)
    );
    if (hasDuplicate) {
      return {
        success: false,
        error: 'Member has already reserved this book',
      };
    }

    // 待機位置を計算（アクティブな予約のみカウント）
    const activeReservations = existingReservations.filter(
      (r) =>
        r.bookId.equals(book.id) &&
        (r.status === ReservationStatus.WAITING || r.status === ReservationStatus.READY)
    );
    const position = activeReservations.length + 1;

    // 予約作成
    const reservation = Reservation.create({
      memberId: member.id,
      bookId: book.id,
      position,
    });

    return {
      success: true,
      reservation,
    };
  }

  /**
   * 返却時の予約処理
   * 最初の待機者をREADY状態にして通知
   * @requirements REQ-RESERVE-002
   */
  processReturn(bookId: BookId, reservations: Reservation[]): ProcessReturnResult {
    // 該当書籍の待機中予約を取得（位置順）
    const waitingReservations = reservations
      .filter(
        (r) =>
          r.bookId.equals(bookId) && r.status === ReservationStatus.WAITING
      )
      .sort((a, b) => a.position - b.position);

    if (waitingReservations.length === 0) {
      return { notifiedReservation: null };
    }

    // 最初の待機者をREADY状態に
    const firstReservation = waitingReservations[0];
    firstReservation.markReady();

    return { notifiedReservation: firstReservation };
  }

  /**
   * 予約キャンセル
   * @requirements REQ-RESERVE-004
   */
  cancelReservation(
    reservation: Reservation,
    allReservations: Reservation[]
  ): CancelReservationResult {
    const cancelledPosition = reservation.position;
    const bookId = reservation.bookId;

    // キャンセル実行
    reservation.cancel();

    // 同じ本の後続予約の位置を更新
    const subsequentReservations = allReservations.filter(
      (r) =>
        r.bookId.equals(bookId) &&
        r.status === ReservationStatus.WAITING &&
        r.position > cancelledPosition
    );

    for (const r of subsequentReservations) {
      r.updatePosition(r.position - 1);
    }

    return { success: true };
  }

  /**
   * 期限切れ予約の処理
   * @requirements REQ-RESERVE-005
   */
  processExpiredReservations(reservations: Reservation[]): Reservation[] {
    const expired: Reservation[] = [];

    for (const reservation of reservations) {
      if (reservation.isExpired()) {
        this.cancelReservation(reservation, reservations);
        expired.push(reservation);
      }
    }

    return expired;
  }
}
