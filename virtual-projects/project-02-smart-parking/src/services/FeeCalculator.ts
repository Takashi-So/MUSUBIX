/**
 * Fee Calculator Utility
 * @requirement REQ-FEE-001, REQ-FEE-002, REQ-FEE-003
 * @design DES-PARKING-001 Section 4.4
 * @pattern Strategy
 */

import { FeeTable, FeeCalculationResult, DiscountCode, DEFAULT_FEE_TABLE } from '../types/Fee.js';

export class FeeCalculator {
  private feeTable: FeeTable;

  constructor(feeTable: FeeTable = DEFAULT_FEE_TABLE) {
    this.feeTable = feeTable;
  }

  /**
   * 料金を計算
   * @requirement REQ-FEE-001: 最初の30分無料
   * @requirement REQ-FEE-002: 30分ごとに200円
   * @requirement REQ-FEE-003: 24時間上限2000円
   */
  calculate(
    entryTime: Date,
    exitTime: Date,
    discountCode?: DiscountCode
  ): FeeCalculationResult {
    const durationMinutes = Math.ceil(
      (exitTime.getTime() - entryTime.getTime()) / (1000 * 60)
    );

    // 無料時間内なら無料
    if (durationMinutes <= this.feeTable.freeMinutes) {
      return {
        durationMinutes,
        baseFee: 0,
        discountAmount: 0,
        finalFee: 0,
        dailyMaxApplied: false,
      };
    }

    // 課金対象時間を計算
    const chargeableMinutes = durationMinutes - this.feeTable.freeMinutes;
    const units = Math.ceil(chargeableMinutes / this.feeTable.unitMinutes);
    let baseFee = units * this.feeTable.ratePerUnit;

    // 24時間上限を適用
    const days = Math.ceil(durationMinutes / (24 * 60));
    const maxFee = days * this.feeTable.dailyMax;
    const dailyMaxApplied = baseFee > maxFee;
    if (dailyMaxApplied) {
      baseFee = maxFee;
    }

    // 割引コードを適用
    let discountAmount = 0;
    if (discountCode && this.isValidDiscount(discountCode, exitTime)) {
      discountAmount = Math.floor(baseFee * (discountCode.discountPercent / 100));
    }

    const finalFee = baseFee - discountAmount;

    return {
      durationMinutes,
      baseFee,
      discountAmount,
      finalFee,
      dailyMaxApplied,
      discountCode: discountCode?.code,
    };
  }

  /**
   * 割引コードの有効性を検証
   */
  private isValidDiscount(code: DiscountCode, currentTime: Date): boolean {
    return currentTime >= code.validFrom && currentTime <= code.validTo;
  }

  /**
   * 見積もり計算（入庫中の現在時点での料金）
   */
  estimate(entryTime: Date, currentTime: Date = new Date()): number {
    const result = this.calculate(entryTime, currentTime);
    return result.finalFee;
  }

  /**
   * 料金テーブルを更新
   */
  updateFeeTable(newTable: Partial<FeeTable>): void {
    this.feeTable = { ...this.feeTable, ...newTable };
  }

  /**
   * 現在の料金テーブルを取得
   */
  getFeeTable(): FeeTable {
    return { ...this.feeTable };
  }
}
