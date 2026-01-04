/**
 * ReservationService - 予約管理のビジネスロジック
 * 
 * @requirement REQ-RESERVE-001, REQ-RESERVE-002, REQ-RESERVE-003, REQ-RESERVE-004
 * @design DES-PETCLINIC-001 Section 3.2
 * @pattern Service
 */

import type { 
  Reservation, 
  CreateReservationInput,
  RescheduleReservationInput,
  ReservationError 
} from '../types/Reservation.js';
import { RESERVATION_ERRORS } from '../types/Reservation.js';
import { ReservationRepository } from '../repositories/ReservationRepository.js';
import { reservationWorkflow, type ReservationStatus } from '../utils/StatusWorkflow.js';

export interface ReservationServiceResult<T> {
  success: boolean;
  data?: T;
  error?: ReservationError;
  requiresFee?: boolean;
}

export class ReservationService {
  constructor(private readonly reservationRepo: ReservationRepository) {}

  /**
   * 予約を作成
   * @requirement REQ-RESERVE-001, REQ-RESERVE-004
   * @param input 予約情報
   * @returns 作成結果
   */
  book(input: CreateReservationInput): ReservationServiceResult<Reservation> {
    // 重複チェック (REQ-RESERVE-004)
    const hasDuplicate = this.reservationRepo.checkDuplicate(
      input.petId,
      input.startTime,
      input.endTime
    );
    if (hasDuplicate) {
      return { success: false, error: RESERVATION_ERRORS.DUPLICATE };
    }

    // 時間枠の空き確認
    const conflicts = this.reservationRepo.findByVetAndTimeRange(
      input.vetId,
      input.startTime,
      input.endTime
    );
    if (conflicts.length > 0) {
      return { success: false, error: RESERVATION_ERRORS.SLOT_UNAVAILABLE };
    }

    // 予約作成
    const reservation = this.reservationRepo.save(input);

    // ステータスをconfirmedに更新
    const confirmed = this.reservationRepo.updateStatus(reservation.id, 'confirmed');

    return { success: true, data: confirmed ?? reservation };
  }

  /**
   * 予約を変更
   * @requirement REQ-RESERVE-002
   * @param input 変更情報
   * @returns 変更結果
   */
  reschedule(input: RescheduleReservationInput): ReservationServiceResult<Reservation> {
    const reservation = this.reservationRepo.findById(input.reservationId);
    if (!reservation) {
      return { success: false, error: { code: 'ERR-NOT-FOUND', message: '予約が見つかりません' } };
    }

    // 24時間前チェック
    const hoursUntil = (reservation.startTime.getTime() - Date.now()) / (1000 * 60 * 60);
    if (hoursUntil < 24) {
      return { success: false, error: RESERVATION_ERRORS.TOO_LATE_TO_RESCHEDULE };
    }

    // ステータスチェック
    try {
      reservationWorkflow.transition(reservation.status, 'reschedule');
    } catch {
      return { success: false, error: RESERVATION_ERRORS.INVALID_STATUS };
    }

    // 重複チェック（自身を除外）
    const hasDuplicate = this.reservationRepo.checkDuplicate(
      reservation.petId,
      input.newStartTime,
      input.newEndTime,
      reservation.id
    );
    if (hasDuplicate) {
      return { success: false, error: RESERVATION_ERRORS.DUPLICATE };
    }

    // 更新
    const updated = this.reservationRepo.update(reservation.id, {
      startTime: input.newStartTime,
      endTime: input.newEndTime,
      status: 'rescheduled',
    });

    return { success: true, data: updated ?? reservation };
  }

  /**
   * 予約をキャンセル
   * @requirement REQ-RESERVE-003
   * @param reservationId 予約ID
   * @returns キャンセル結果
   */
  cancel(reservationId: string): ReservationServiceResult<Reservation> {
    const reservation = this.reservationRepo.findById(reservationId);
    if (!reservation) {
      return { success: false, error: { code: 'ERR-NOT-FOUND', message: '予約が見つかりません' } };
    }

    // 24時間前チェック
    const hoursUntil = (reservation.startTime.getTime() - Date.now()) / (1000 * 60 * 60);
    const requiresFee = hoursUntil < 24;

    // ステータス更新
    let newStatus: ReservationStatus;
    try {
      newStatus = requiresFee 
        ? reservationWorkflow.transition(reservation.status, 'cancel_with_fee')
        : reservationWorkflow.transition(reservation.status, 'cancel');
    } catch {
      return { success: false, error: RESERVATION_ERRORS.INVALID_STATUS };
    }

    const updated = this.reservationRepo.updateStatus(reservationId, newStatus);

    return { 
      success: true, 
      data: updated ?? reservation,
      requiresFee,
    };
  }

  /**
   * 診療完了
   * @param reservationId 予約ID
   * @returns 完了結果
   */
  complete(reservationId: string): ReservationServiceResult<Reservation> {
    const reservation = this.reservationRepo.findById(reservationId);
    if (!reservation) {
      return { success: false, error: { code: 'ERR-NOT-FOUND', message: '予約が見つかりません' } };
    }

    try {
      const newStatus = reservationWorkflow.transition(reservation.status, 'complete');
      const updated = this.reservationRepo.updateStatus(reservationId, newStatus);
      return { success: true, data: updated ?? reservation };
    } catch {
      return { success: false, error: RESERVATION_ERRORS.INVALID_STATUS };
    }
  }

  /**
   * ペットの予約一覧を取得
   * @param petId ペットID
   * @returns 予約一覧
   */
  findByPet(petId: string): Reservation[] {
    return this.reservationRepo.findByPet(petId);
  }

  /**
   * IDで予約を取得
   * @param id 予約ID
   * @returns 予約
   */
  findById(id: string): Reservation | null {
    return this.reservationRepo.findById(id);
  }
}
