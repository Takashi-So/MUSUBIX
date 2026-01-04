/**
 * BookCopy Entity - 蔵書コピーエンティティ
 * @requirements REQ-BOOK-004, REQ-BOOK-005, REQ-LOAN-006
 * @design DES-LIBRARY-001 §3.1, §5.2 (Status Transition)
 * @task TSK-LIB-002
 */

import { BookId } from './Book';

/**
 * CopyId - 蔵書コピーID値オブジェクト
 */
export class CopyId {
  private static counter = 0;

  constructor(public readonly value: string) {}

  static generate(): CopyId {
    CopyId.counter++;
    const timestamp = Date.now();
    const seq = String(CopyId.counter).padStart(3, '0');
    return new CopyId(`COPY-${timestamp}-${seq}`);
  }

  equals(other: CopyId): boolean {
    return this.value === other.value;
  }

  toString(): string {
    return this.value;
  }
}

/**
 * CopyStatus - 蔵書コピーステータス
 * @requirements REQ-BOOK-004 (available, on_loan, reserved, maintenance, retired)
 * @design DES-LIBRARY-001 §5.2 BookCopy Status
 */
export enum CopyStatus {
  AVAILABLE = 'available',
  ON_LOAN = 'on_loan',
  RESERVED = 'reserved',
  MAINTENANCE = 'maintenance',
  RETIRED = 'retired',
}

/**
 * CreateCopyParams - コピー作成パラメータ
 */
export interface CreateCopyParams {
  bookId: BookId;
  shelfLocation: string;
}

/**
 * BookCopy - 蔵書コピーエンティティ
 * @requirements REQ-BOOK-004, REQ-BOOK-005
 * @design DES-LIBRARY-001 §3.1 BookCopy Entity
 * 
 * Status Transitions:
 * - available → on_loan (checkout)
 * - available → reserved (reserve)
 * - available → maintenance (setMaintenance)
 * - available → retired (retire)
 * - on_loan → available (return)
 * - on_loan → overdue (automatic)
 * - reserved → available (release)
 * - reserved → on_loan (checkout)
 * - maintenance → available (release)
 */
export class BookCopy {
  private constructor(
    public readonly id: CopyId,
    public readonly bookId: BookId,
    private _status: CopyStatus,
    private _shelfLocation: string,
    public readonly acquiredAt: Date,
    private _retiredAt: Date | null
  ) {}

  static create(params: CreateCopyParams): BookCopy {
    return new BookCopy(
      CopyId.generate(),
      params.bookId,
      CopyStatus.AVAILABLE,
      params.shelfLocation,
      new Date(),
      null
    );
  }

  // Getters
  get status(): CopyStatus {
    return this._status;
  }

  get shelfLocation(): string {
    return this._shelfLocation;
  }

  get retiredAt(): Date | null {
    return this._retiredAt;
  }

  /**
   * 貸出可能かどうか
   * @requirements REQ-LOAN-006 (available以外は貸出不可)
   */
  isAvailable(): boolean {
    return this._status === CopyStatus.AVAILABLE;
  }

  /**
   * 貸出処理 (available → on_loan)
   * @requirements REQ-LOAN-001, REQ-LOAN-006
   */
  checkout(): void {
    if (this._status !== CopyStatus.AVAILABLE && this._status !== CopyStatus.RESERVED) {
      throw new Error('Cannot checkout: book is not available');
    }
    this._status = CopyStatus.ON_LOAN;
  }

  /**
   * 返却処理 (on_loan → available)
   * @requirements REQ-LOAN-002
   */
  return(): void {
    if (this._status !== CopyStatus.ON_LOAN) {
      throw new Error('Cannot return: book is not on loan');
    }
    this._status = CopyStatus.AVAILABLE;
  }

  /**
   * 予約処理 (available → reserved)
   * @requirements REQ-RESERVE-003
   */
  reserve(): void {
    if (this._status !== CopyStatus.AVAILABLE) {
      throw new Error('Cannot reserve: book is not available');
    }
    this._status = CopyStatus.RESERVED;
  }

  /**
   * 予約解除 (reserved → available)
   * @requirements REQ-RESERVE-004
   */
  releaseReservation(): void {
    if (this._status !== CopyStatus.RESERVED) {
      throw new Error('Cannot release: book is not reserved');
    }
    this._status = CopyStatus.AVAILABLE;
  }

  /**
   * メンテナンス設定 (available → maintenance)
   */
  setMaintenance(): void {
    if (this._status !== CopyStatus.AVAILABLE) {
      throw new Error('Cannot set maintenance: book is not available');
    }
    this._status = CopyStatus.MAINTENANCE;
  }

  /**
   * メンテナンス解除 (maintenance → available)
   */
  releaseMaintenance(): void {
    if (this._status !== CopyStatus.MAINTENANCE) {
      throw new Error('Cannot release maintenance: book is not in maintenance');
    }
    this._status = CopyStatus.AVAILABLE;
  }

  /**
   * 廃棄処理 (available/maintenance → retired)
   * @requirements REQ-BOOK-005 (未返却の貸出がないことを確認)
   */
  retire(): void {
    if (this._status === CopyStatus.ON_LOAN) {
      throw new Error('Cannot retire: book has active loan');
    }
    if (this._status === CopyStatus.RETIRED) {
      throw new Error('Book is already retired');
    }
    this._status = CopyStatus.RETIRED;
    this._retiredAt = new Date();
  }

  /**
   * 棚位置を更新
   */
  updateShelfLocation(location: string): void {
    this._shelfLocation = location;
  }

  /**
   * 復元用ファクトリメソッド
   */
  static reconstruct(
    id: CopyId,
    bookId: BookId,
    status: CopyStatus,
    shelfLocation: string,
    acquiredAt: Date,
    retiredAt: Date | null
  ): BookCopy {
    return new BookCopy(id, bookId, status, shelfLocation, acquiredAt, retiredAt);
  }
}
