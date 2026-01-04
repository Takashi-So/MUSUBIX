/**
 * Reservation Entity
 * @requirements REQ-RESERVE-001, REQ-RESERVE-002, REQ-RESERVE-003, REQ-RESERVE-004
 * @design DES-LIBRARY-001 §3.3
 * @task TSK-LIB-006
 */

import { MemberId } from '../member/Member';
import { BookId } from '../book/Book';

/**
 * ReservationId - 予約ID値オブジェクト
 */
export class ReservationId {
  private static counter = 0;

  constructor(public readonly value: string) {}

  static generate(): ReservationId {
    ReservationId.counter++;
    const timestamp = Date.now();
    const seq = String(ReservationId.counter).padStart(4, '0');
    return new ReservationId(`RESV-${timestamp}-${seq}`);
  }

  equals(other: ReservationId): boolean {
    return this.value === other.value;
  }

  toString(): string {
    return this.value;
  }
}

/**
 * ReservationStatus - 予約ステータス
 * @design DES-LIBRARY-001 §5.3 Reservation Status
 */
export enum ReservationStatus {
  WAITING = 'waiting',
  READY = 'ready',
  COMPLETED = 'completed',
  CANCELLED = 'cancelled',
}

/**
 * CreateReservationParams - 予約作成パラメータ
 */
export interface CreateReservationParams {
  memberId: MemberId;
  bookId: BookId;
  position: number;
}

/**
 * Reservation - 予約エンティティ
 * @requirements REQ-RESERVE-001〜005
 * @design DES-LIBRARY-001 §3.3 Reservation Entity
 */
export class Reservation {
  private static readonly EXPIRY_DAYS = 7;

  private constructor(
    public readonly id: ReservationId,
    public readonly memberId: MemberId,
    public readonly bookId: BookId,
    public readonly reservedAt: Date,
    private _position: number,
    private _status: ReservationStatus,
    private _readyAt: Date | null,
    private _completedAt: Date | null,
    private _cancelledAt: Date | null
  ) {}

  static create(params: CreateReservationParams): Reservation {
    return new Reservation(
      ReservationId.generate(),
      params.memberId,
      params.bookId,
      new Date(),
      params.position,
      ReservationStatus.WAITING,
      null,
      null,
      null
    );
  }

  // Getters
  get position(): number {
    return this._position;
  }

  get status(): ReservationStatus {
    return this._status;
  }

  get readyAt(): Date | null {
    return this._readyAt;
  }

  get completedAt(): Date | null {
    return this._completedAt;
  }

  get cancelledAt(): Date | null {
    return this._cancelledAt;
  }

  /**
   * 貸出可能状態にする
   * @requirements REQ-RESERVE-002
   */
  markReady(): void {
    if (this._status !== ReservationStatus.WAITING) {
      throw new Error('Only waiting reservations can be marked ready');
    }
    this._status = ReservationStatus.READY;
    this._readyAt = new Date();
  }

  /**
   * 予約完了（貸出実行）
   * @requirements REQ-RESERVE-003
   */
  complete(): void {
    if (this._status !== ReservationStatus.READY) {
      throw new Error('Only ready reservations can be completed');
    }
    this._status = ReservationStatus.COMPLETED;
    this._completedAt = new Date();
  }

  /**
   * 予約キャンセル
   * @requirements REQ-RESERVE-004
   */
  cancel(): void {
    if (this._status === ReservationStatus.COMPLETED) {
      throw new Error('Cannot cancel completed reservation');
    }
    if (this._status === ReservationStatus.CANCELLED) {
      throw new Error('Reservation is already cancelled');
    }
    this._status = ReservationStatus.CANCELLED;
    this._cancelledAt = new Date();
  }

  /**
   * 待機順位を更新
   * @requirements REQ-RESERVE-001 (キュー管理)
   */
  updatePosition(newPosition: number): void {
    if (this._status !== ReservationStatus.WAITING) {
      throw new Error('Cannot update position of non-waiting reservation');
    }
    if (newPosition < 1) {
      throw new Error('Position must be positive');
    }
    this._position = newPosition;
  }

  /**
   * 期限切れかどうか
   * @requirements REQ-RESERVE-005 (7日間の取り置き期限)
   */
  isExpired(): boolean {
    if (this._status !== ReservationStatus.READY || !this._readyAt) {
      return false;
    }
    const expiryDate = new Date(this._readyAt);
    expiryDate.setDate(expiryDate.getDate() + Reservation.EXPIRY_DAYS);
    return new Date() > expiryDate;
  }

  /**
   * 取り置き期限日を取得
   */
  getExpiryDate(): Date | null {
    if (!this._readyAt) {
      return null;
    }
    const expiryDate = new Date(this._readyAt);
    expiryDate.setDate(expiryDate.getDate() + Reservation.EXPIRY_DAYS);
    return expiryDate;
  }

  /**
   * テスト用: readyAt を設定
   */
  setReadyAtForTest(date: Date): void {
    this._readyAt = date;
  }

  /**
   * 復元用ファクトリメソッド
   */
  static reconstruct(
    id: ReservationId,
    memberId: MemberId,
    bookId: BookId,
    reservedAt: Date,
    position: number,
    status: ReservationStatus,
    readyAt: Date | null,
    completedAt: Date | null,
    cancelledAt: Date | null
  ): Reservation {
    return new Reservation(
      id,
      memberId,
      bookId,
      reservedAt,
      position,
      status,
      readyAt,
      completedAt,
      cancelledAt
    );
  }
}
