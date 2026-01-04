/**
 * Reservation Types - 予約エンティティの型定義
 * 
 * @requirement REQ-RESERVE-001, REQ-RESERVE-002, REQ-RESERVE-003, REQ-RESERVE-004
 * @design DES-PETCLINIC-001 Section 4.1
 */

import type { ReservationStatus } from '../utils/StatusWorkflow.js';

export type ReservationType = 'checkup' | 'vaccination' | 'surgery' | 'emergency' | 'grooming';

export interface Reservation {
  id: string;
  petId: string;
  vetId: string;
  ownerId: string;
  startTime: Date;
  endTime: Date;
  type: ReservationType;
  status: ReservationStatus;
  notes?: string;
  createdAt: Date;
  updatedAt: Date;
}

export interface CreateReservationInput {
  petId: string;
  vetId: string;
  ownerId: string;
  startTime: Date;
  endTime: Date;
  type: ReservationType;
  notes?: string;
}

export interface RescheduleReservationInput {
  reservationId: string;
  newStartTime: Date;
  newEndTime: Date;
}

export interface ReservationError {
  code: string;
  message: string;
}

// エラーコード定義
export const RESERVATION_ERRORS = {
  DUPLICATE: { code: 'ERR-DUP-001', message: '同一ペットの同一日時に既存予約があります' },
  SLOT_UNAVAILABLE: { code: 'ERR-SLOT-001', message: '指定された時間枠は利用できません' },
  TOO_LATE_TO_RESCHEDULE: { code: 'ERR-TIME-001', message: '予約変更は24時間前までです' },
  TOO_LATE_TO_CANCEL: { code: 'ERR-TIME-002', message: 'キャンセル料が発生します' },
  INVALID_STATUS: { code: 'ERR-STATUS-001', message: '現在のステータスではこの操作はできません' },
} as const;
