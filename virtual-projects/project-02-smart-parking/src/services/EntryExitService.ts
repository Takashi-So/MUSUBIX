/**
 * Entry Exit Service
 * @requirement REQ-ENTRY-001, REQ-ENTRY-002, REQ-ENTRY-003
 * @design DES-PARKING-001 Section 4.2
 * @pattern Service
 */

import { EntryRecord, VehicleType, ENTRY_ERRORS } from '../types/Entry.js';
import { FeeCalculationResult, DiscountCode } from '../types/Fee.js';
import { EntryRepository } from '../repositories/EntryRepository.js';
import { SpaceService } from './SpaceService.js';
import { FeeCalculator } from './FeeCalculator.js';

export interface EntryInput {
  plateNumber: string;
  spaceId: string;
  vehicleType: VehicleType;
}

export interface ExitInput {
  entryId: string;
  discountCode?: DiscountCode;
}

export interface EntryExitResult<T> {
  success: boolean;
  data?: T;
  error?: string;
}

export interface ExitResult {
  entry: EntryRecord;
  fee: FeeCalculationResult;
}

export class EntryExitService {
  constructor(
    private entryRepository: EntryRepository,
    private spaceService: SpaceService,
    private feeCalculator: FeeCalculator
  ) {}

  /**
   * 入庫処理
   * @requirement REQ-ENTRY-001: 入庫時にナンバープレート自動認識
   * @requirement REQ-ENTRY-002: 同一ナンバー重複入庫を防止
   */
  entry(input: EntryInput): EntryExitResult<EntryRecord> {
    // 重複チェック
    if (this.entryRepository.checkDuplicate(input.plateNumber)) {
      return { success: false, error: ENTRY_ERRORS.DUPLICATE_ENTRY };
    }

    // スペースが空いているかチェック
    const space = this.spaceService.getSpace(input.spaceId);
    if (!space) {
      return { success: false, error: ENTRY_ERRORS.SPACE_UNAVAILABLE };
    }

    // スペースを使用中に変更
    const occupyResult = this.spaceService.occupy(input.spaceId);
    if (!occupyResult.success) {
      return { success: false, error: ENTRY_ERRORS.SPACE_UNAVAILABLE };
    }

    // 入庫記録を作成
    const entry = this.entryRepository.create({
      plateNumber: input.plateNumber,
      spaceId: input.spaceId,
      vehicleType: input.vehicleType,
      entryTime: new Date(),
    });

    return { success: true, data: entry };
  }

  /**
   * 出庫処理
   * @requirement REQ-ENTRY-003: 出庫時に料金自動計算
   */
  exit(input: ExitInput): EntryExitResult<ExitResult> {
    const entry = this.entryRepository.findById(input.entryId);
    if (!entry) {
      return { success: false, error: ENTRY_ERRORS.NOT_FOUND };
    }

    if (entry.status !== 'active') {
      return { success: false, error: ENTRY_ERRORS.ALREADY_EXITED };
    }

    const exitTime = new Date();

    // 料金計算
    const fee = this.feeCalculator.calculate(
      entry.entryTime,
      exitTime,
      input.discountCode
    );

    // 入庫記録を完了
    const updatedEntry = this.entryRepository.completeExit(
      input.entryId,
      exitTime,
      fee.finalFee
    );

    // スペースを空きに変更
    this.spaceService.release(entry.spaceId);

    return {
      success: true,
      data: {
        entry: updatedEntry!,
        fee,
      },
    };
  }

  /**
   * 現在の駐車料金を見積もり
   */
  estimateFee(entryId: string): EntryExitResult<FeeCalculationResult> {
    const entry = this.entryRepository.findById(entryId);
    if (!entry) {
      return { success: false, error: ENTRY_ERRORS.NOT_FOUND };
    }

    if (entry.status !== 'active') {
      return { success: false, error: ENTRY_ERRORS.ALREADY_EXITED };
    }

    const fee = this.feeCalculator.calculate(entry.entryTime, new Date());
    return { success: true, data: fee };
  }

  /**
   * ナンバープレートでアクティブな入庫記録を検索
   */
  findByPlate(plateNumber: string): EntryRecord | null {
    return this.entryRepository.findActiveByPlate(plateNumber);
  }

  /**
   * アクティブな入庫記録を全て取得
   */
  getActiveEntries(): EntryRecord[] {
    return this.entryRepository.findByStatus('active');
  }

  /**
   * 特定の入庫記録を取得
   */
  getEntry(id: string): EntryRecord | null {
    return this.entryRepository.findById(id);
  }

  /**
   * 日付範囲で履歴を検索
   */
  getHistory(start: Date, end: Date): EntryRecord[] {
    return this.entryRepository.findByDateRange(start, end);
  }
}
