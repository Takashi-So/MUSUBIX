/**
 * Fee Types
 * @requirement REQ-FEE-001, REQ-FEE-002, REQ-FEE-003
 * @design DES-PARKING-001 Section 4
 */

export interface FeeTable {
  freeMinutes: number;      // 最初の無料時間（分）
  ratePerUnit: number;      // 単位あたり料金（円）
  unitMinutes: number;      // 料金単位（分）
  dailyMax: number;         // 24時間上限（円）
}

export interface FeeCalculationResult {
  durationMinutes: number;
  baseFee: number;
  discountAmount: number;
  finalFee: number;
  dailyMaxApplied: boolean;
  discountCode?: string;
}

export interface DiscountCode {
  code: string;
  discountPercent: number;  // 20, 50, 100
  validFrom: Date;
  validTo: Date;
  shopName: string;
}

// デフォルト料金テーブル
export const DEFAULT_FEE_TABLE: FeeTable = {
  freeMinutes: 30,      // 最初の30分無料
  ratePerUnit: 200,     // 30分ごとに200円
  unitMinutes: 30,      // 30分単位
  dailyMax: 2000,       // 24時間最大2000円
};
