/**
 * Loan Entity
 * @requirements REQ-LOAN-001, REQ-LOAN-002, REQ-LOAN-003, REQ-LOAN-004
 * @design DES-LIBRARY-001 §3.2
 * @task TSK-LIB-005
 */

import { MemberId } from '../member/Member';
import { CopyId } from '../book/BookCopy';

/**
 * LoanId - 貸出ID値オブジェクト
 */
export class LoanId {
  private static counter = 0;

  constructor(public readonly value: string) {}

  static generate(): LoanId {
    LoanId.counter++;
    const timestamp = Date.now();
    const seq = String(LoanId.counter).padStart(4, '0');
    return new LoanId(`LOAN-${timestamp}-${seq}`);
  }

  equals(other: LoanId): boolean {
    return this.value === other.value;
  }

  toString(): string {
    return this.value;
  }
}

/**
 * LoanStatus - 貸出ステータス
 * @design DES-LIBRARY-001 §5.2 Loan Status
 */
export enum LoanStatus {
  ACTIVE = 'active',
  RETURNED = 'returned',
  OVERDUE = 'overdue',
}

/**
 * CreateLoanParams - 貸出作成パラメータ
 */
export interface CreateLoanParams {
  memberId: MemberId;
  copyId: CopyId;
  loanDays?: number;
}

/**
 * Loan - 貸出エンティティ（集約ルート）
 * @requirements REQ-LOAN-001〜006
 * @design DES-LIBRARY-001 §3.2 Loan Entity (Aggregate Root)
 */
export class Loan {
  private static readonly DEFAULT_LOAN_DAYS = 14;
  private static readonly EXTENSION_DAYS = 14;
  private static readonly MAX_EXTENSIONS = 2;

  private constructor(
    public readonly id: LoanId,
    public readonly memberId: MemberId,
    public readonly copyId: CopyId,
    public readonly loanDate: Date,
    private _dueDate: Date,
    private _returnedAt: Date | null,
    private _status: LoanStatus,
    private _extensionCount: number
  ) {}

  static create(params: CreateLoanParams): Loan {
    const loanDate = new Date();
    const loanDays = params.loanDays ?? Loan.DEFAULT_LOAN_DAYS;
    const dueDate = new Date(loanDate);
    dueDate.setDate(dueDate.getDate() + loanDays);

    return new Loan(
      LoanId.generate(),
      params.memberId,
      params.copyId,
      loanDate,
      dueDate,
      null,
      LoanStatus.ACTIVE,
      0
    );
  }

  // Getters
  get dueDate(): Date {
    return this._dueDate;
  }

  get returnedAt(): Date | null {
    return this._returnedAt;
  }

  get status(): LoanStatus {
    return this._status;
  }

  get extensionCount(): number {
    return this._extensionCount;
  }

  /**
   * 返却処理
   * @requirements REQ-LOAN-002
   */
  return(): void {
    if (this._status === LoanStatus.RETURNED) {
      throw new Error('Loan is already returned');
    }
    this._returnedAt = new Date();
    this._status = LoanStatus.RETURNED;
  }

  /**
   * 延長処理
   * @requirements REQ-LOAN-003 (14日間延長、最大2回)
   */
  extend(): void {
    if (this._status === LoanStatus.RETURNED) {
      throw new Error('Cannot extend returned loan');
    }
    if (this._extensionCount >= Loan.MAX_EXTENSIONS) {
      throw new Error('Maximum extensions reached');
    }

    const newDueDate = new Date(this._dueDate);
    newDueDate.setDate(newDueDate.getDate() + Loan.EXTENSION_DAYS);
    this._dueDate = newDueDate;
    this._extensionCount++;
  }

  /**
   * 延滞マーク
   * @requirements REQ-LOAN-004
   */
  markOverdue(): void {
    if (this._status === LoanStatus.ACTIVE) {
      this._status = LoanStatus.OVERDUE;
    }
  }

  /**
   * 延滞日数を取得
   */
  getOverdueDays(): number {
    const now = new Date();
    if (now <= this._dueDate) {
      return 0;
    }
    const diffTime = now.getTime() - this._dueDate.getTime();
    return Math.ceil(diffTime / (1000 * 60 * 60 * 24));
  }

  /**
   * 延滞中かどうか
   */
  isOverdue(): boolean {
    return this._status === LoanStatus.OVERDUE || this.getOverdueDays() > 0;
  }

  /**
   * 延長可能かどうか
   * @requirements REQ-LOAN-003 (返却期限前、最大2回)
   */
  canExtend(): boolean {
    if (this._status === LoanStatus.RETURNED) {
      return false;
    }
    if (this._extensionCount >= Loan.MAX_EXTENSIONS) {
      return false;
    }
    const now = new Date();
    return now <= this._dueDate;
  }

  /**
   * テスト用: 返却期限を設定
   */
  setDueDateForTest(date: Date): void {
    this._dueDate = date;
  }

  /**
   * 復元用ファクトリメソッド
   */
  static reconstruct(
    id: LoanId,
    memberId: MemberId,
    copyId: CopyId,
    loanDate: Date,
    dueDate: Date,
    returnedAt: Date | null,
    status: LoanStatus,
    extensionCount: number
  ): Loan {
    return new Loan(id, memberId, copyId, loanDate, dueDate, returnedAt, status, extensionCount);
  }
}
