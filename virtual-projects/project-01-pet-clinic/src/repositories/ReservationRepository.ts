/**
 * ReservationRepository - 予約データの永続化
 * 
 * @requirement REQ-RESERVE-001, REQ-RESERVE-004
 * @design DES-PETCLINIC-001 Section 3.2
 * @pattern Repository
 */

import type { Reservation, CreateReservationInput } from '../types/Reservation.js';
import type { ReservationStatus } from '../utils/StatusWorkflow.js';
import { idGenerators } from '../utils/IdGenerator.js';

export class ReservationRepository {
  private reservations: Map<string, Reservation> = new Map();

  /**
   * 予約を保存
   * @param input 作成データ
   * @returns 作成された予約
   */
  save(input: CreateReservationInput): Reservation {
    const now = new Date();
    const reservation: Reservation = {
      id: idGenerators.reservation.generate(),
      petId: input.petId,
      vetId: input.vetId,
      ownerId: input.ownerId,
      startTime: input.startTime,
      endTime: input.endTime,
      type: input.type,
      status: 'pending',
      notes: input.notes,
      createdAt: now,
      updatedAt: now,
    };
    this.reservations.set(reservation.id, reservation);
    return reservation;
  }

  /**
   * 予約情報を更新
   * @param id 予約ID
   * @param updates 更新データ
   * @returns 更新された予約、存在しない場合はnull
   */
  update(id: string, updates: Partial<Reservation>): Reservation | null {
    const reservation = this.reservations.get(id);
    if (!reservation) return null;

    const updated: Reservation = {
      ...reservation,
      ...updates,
      updatedAt: new Date(),
    };
    this.reservations.set(id, updated);
    return updated;
  }

  /**
   * ステータスを更新
   */
  updateStatus(id: string, status: ReservationStatus): Reservation | null {
    return this.update(id, { status });
  }

  /**
   * IDで予約を検索
   */
  findById(id: string): Reservation | null {
    return this.reservations.get(id) ?? null;
  }

  /**
   * ペットIDで予約を検索
   */
  findByPet(petId: string): Reservation[] {
    return Array.from(this.reservations.values()).filter(
      (r) => r.petId === petId
    );
  }

  /**
   * 獣医師IDと日時範囲で予約を検索
   */
  findByVetAndTimeRange(vetId: string, start: Date, end: Date): Reservation[] {
    return Array.from(this.reservations.values()).filter(
      (r) =>
        r.vetId === vetId &&
        r.status !== 'cancelled' &&
        r.status !== 'cancelled_with_fee' &&
        r.startTime < end &&
        r.endTime > start
    );
  }

  /**
   * 重複予約をチェック
   * @requirement REQ-RESERVE-004
   */
  checkDuplicate(petId: string, start: Date, end: Date, excludeId?: string): boolean {
    return Array.from(this.reservations.values()).some(
      (r) =>
        r.id !== excludeId &&
        r.petId === petId &&
        r.status !== 'cancelled' &&
        r.status !== 'cancelled_with_fee' &&
        r.startTime < end &&
        r.endTime > start
    );
  }

  /**
   * 全予約を取得（テスト用）
   */
  findAll(): Reservation[] {
    return Array.from(this.reservations.values());
  }

  /**
   * リポジトリをクリア（テスト用）
   */
  clear(): void {
    this.reservations.clear();
  }
}
