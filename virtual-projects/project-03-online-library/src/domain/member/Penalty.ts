/**
 * Penalty Entity
 * @requirements REQ-MEMBER-005 (延滞ペナルティ期間: 延滞日数×2日間)
 * @design DES-LIBRARY-001 §3.3
 * @task TSK-LIB-004
 */

import { MemberId } from './Member';

/**
 * PenaltyId - ペナルティID値オブジェクト
 */
export class PenaltyId {
  private static counter = 0;

  constructor(public readonly value: string) {}

  static generate(): PenaltyId {
    PenaltyId.counter++;
    const timestamp = Date.now();
    const seq = String(PenaltyId.counter).padStart(3, '0');
    return new PenaltyId(`PEN-${timestamp}-${seq}`);
  }

  equals(other: PenaltyId): boolean {
    return this.value === other.value;
  }

  toString(): string {
    return this.value;
  }
}

/**
 * PenaltyStatus - ペナルティステータス
 */
export enum PenaltyStatus {
  ACTIVE = 'active',
  COMPLETED = 'completed',
  WAIVED = 'waived',
}

/**
 * CreatePenaltyParams - ペナルティ作成パラメータ
 */
export interface CreatePenaltyParams {
  memberId: MemberId;
  reason: string;
  overdueDays: number;
}

/**
 * Penalty - ペナルティエンティティ
 * @requirements REQ-MEMBER-005
 * @design DES-LIBRARY-001 §3.3 Penalty Entity
 */
export class Penalty {
  private constructor(
    public readonly id: PenaltyId,
    public readonly memberId: MemberId,
    public readonly reason: string,
    public readonly overdueDays: number,
    public readonly startDate: Date,
    public readonly endDate: Date,
    private _status: PenaltyStatus
  ) {}

  /**
   * ペナルティを作成
   * @requirements REQ-MEMBER-005 (延滞日数×2日間)
   */
  static create(params: CreatePenaltyParams): Penalty {
    const startDate = new Date();
    const penaltyDays = params.overdueDays * 2; // 延滞日数×2
    const endDate = new Date(startDate);
    endDate.setDate(endDate.getDate() + penaltyDays);

    return new Penalty(
      PenaltyId.generate(),
      params.memberId,
      params.reason,
      params.overdueDays,
      startDate,
      endDate,
      PenaltyStatus.ACTIVE
    );
  }

  // Getters
  get status(): PenaltyStatus {
    return this._status;
  }

  /**
   * ペナルティが有効かどうか
   */
  isActive(): boolean {
    if (this._status !== PenaltyStatus.ACTIVE) {
      return false;
    }
    const now = new Date();
    return now < this.endDate;
  }

  /**
   * 残りペナルティ日数を取得
   */
  getRemainingDays(): number {
    if (!this.isActive()) {
      return 0;
    }
    const now = new Date();
    const diffTime = this.endDate.getTime() - now.getTime();
    const diffDays = Math.ceil(diffTime / (1000 * 60 * 60 * 24));
    return Math.max(0, diffDays);
  }

  /**
   * ペナルティを完了
   */
  complete(): void {
    this._status = PenaltyStatus.COMPLETED;
  }

  /**
   * ペナルティを免除
   */
  waive(): void {
    this._status = PenaltyStatus.WAIVED;
  }

  /**
   * 復元用ファクトリメソッド
   */
  static reconstruct(
    id: PenaltyId,
    memberId: MemberId,
    reason: string,
    overdueDays: number,
    startDate: Date,
    endDate: Date,
    status: PenaltyStatus
  ): Penalty {
    return new Penalty(id, memberId, reason, overdueDays, startDate, endDate, status);
  }
}
