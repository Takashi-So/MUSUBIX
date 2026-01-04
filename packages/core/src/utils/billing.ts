/**
 * BillingCalculator - 料金計算・返金ポリシーユーティリティ
 *
 * @description
 * 時間ベースの料金計算、キャンセル返金、延長料金を計算するサービスクラス。
 * 予約システム、SaaS課金、サブスクリプション管理で使用。
 *
 * @example
 * ```typescript
 * const billing = new BillingCalculator({
 *   slotMinutes: 15,
 *   fullRefundHours: 2,
 *   partialRefundPercentage: 50,
 * });
 *
 * // 料金計算
 * const fee = billing.calculateFee(2000, startTime, endTime);
 *
 * // 返金計算
 * const refund = billing.calculateRefund(4000, reservationStart, cancelTime);
 * ```
 *
 * @since 1.0.21
 * @see REQ-LEARN-003 - 繰り返しパターンの抽出
 */

/**
 * BillingCalculatorの設定オプション
 */
export interface BillingConfig {
  /** 課金単位の時間（分）。デフォルト: 15 */
  slotMinutes?: number;
  /** 全額返金可能な時間（予約開始前の時間）。デフォルト: 2 */
  fullRefundHours?: number;
  /** 部分返金の割合（%）。デフォルト: 50 */
  partialRefundPercentage?: number;
  /** 通貨の小数点以下桁数。デフォルト: 0 */
  decimalPlaces?: number;
}

/**
 * 返金計算結果
 */
export interface RefundResult {
  /** 返金額 */
  amount: number;
  /** 返金率（%） */
  percentage: number;
  /** 返金タイプ */
  type: 'full' | 'partial' | 'none';
  /** 予約開始までの時間（時間） */
  hoursUntilStart: number;
}

/**
 * 料金計算結果
 */
export interface FeeResult {
  /** 料金 */
  amount: number;
  /** スロット数 */
  slots: number;
  /** スロット単価 */
  pricePerSlot: number;
  /** 合計時間（分） */
  totalMinutes: number;
}

/**
 * 料金計算サービス
 */
export class BillingCalculator {
  private readonly slotMinutes: number;
  private readonly fullRefundHours: number;
  private readonly partialRefundPercentage: number;
  private readonly decimalPlaces: number;

  constructor(config: BillingConfig = {}) {
    this.slotMinutes = config.slotMinutes ?? 15;
    this.fullRefundHours = config.fullRefundHours ?? 2;
    this.partialRefundPercentage = config.partialRefundPercentage ?? 50;
    this.decimalPlaces = config.decimalPlaces ?? 0;
  }

  /**
   * 予約料金を計算
   *
   * @param hourlyRate - 1時間あたりの料金
   * @param startTime - 開始時刻
   * @param endTime - 終了時刻
   * @returns 料金
   */
  calculateFee(hourlyRate: number, startTime: Date, endTime: Date): number {
    const result = this.calculateFeeDetailed(hourlyRate, startTime, endTime);
    return result.amount;
  }

  /**
   * 予約料金を詳細に計算
   *
   * @param hourlyRate - 1時間あたりの料金
   * @param startTime - 開始時刻
   * @param endTime - 終了時刻
   * @returns 詳細な料金情報
   */
  calculateFeeDetailed(hourlyRate: number, startTime: Date, endTime: Date): FeeResult {
    const totalMinutes = (endTime.getTime() - startTime.getTime()) / (1000 * 60);
    const slots = Math.ceil(totalMinutes / this.slotMinutes);
    const slotsPerHour = 60 / this.slotMinutes;
    const pricePerSlot = hourlyRate / slotsPerHour;
    const amount = this.round(slots * pricePerSlot);

    return {
      amount,
      slots,
      pricePerSlot: this.round(pricePerSlot),
      totalMinutes,
    };
  }

  /**
   * 分単位で料金を計算
   *
   * @param hourlyRate - 1時間あたりの料金
   * @param minutes - 時間（分）
   * @returns 料金
   */
  calculateFeeByMinutes(hourlyRate: number, minutes: number): number {
    const slots = Math.ceil(minutes / this.slotMinutes);
    const slotsPerHour = 60 / this.slotMinutes;
    const pricePerSlot = hourlyRate / slotsPerHour;
    return this.round(slots * pricePerSlot);
  }

  /**
   * キャンセル返金額を計算
   *
   * @param originalAmount - 元の料金
   * @param reservationStartTime - 予約開始時刻
   * @param cancelTime - キャンセル時刻
   * @returns 返金情報
   */
  calculateRefund(
    originalAmount: number,
    reservationStartTime: Date,
    cancelTime: Date
  ): RefundResult {
    const hoursUntilStart =
      (reservationStartTime.getTime() - cancelTime.getTime()) / (1000 * 60 * 60);

    // 予約開始後はキャンセル不可
    if (hoursUntilStart <= 0) {
      return {
        amount: 0,
        percentage: 0,
        type: 'none',
        hoursUntilStart,
      };
    }

    // 全額返金期間内
    if (hoursUntilStart >= this.fullRefundHours) {
      return {
        amount: originalAmount,
        percentage: 100,
        type: 'full',
        hoursUntilStart,
      };
    }

    // 部分返金
    const refundAmount = this.round(originalAmount * (this.partialRefundPercentage / 100));
    return {
      amount: refundAmount,
      percentage: this.partialRefundPercentage,
      type: 'partial',
      hoursUntilStart,
    };
  }

  /**
   * 延長料金を計算
   *
   * @param hourlyRate - 1時間あたりの料金
   * @param additionalMinutes - 追加時間（分）
   * @returns 延長料金
   */
  calculateExtensionFee(hourlyRate: number, additionalMinutes: number): number {
    return this.calculateFeeByMinutes(hourlyRate, additionalMinutes);
  }

  /**
   * 日割り料金を計算
   *
   * @param monthlyRate - 月額料金
   * @param daysUsed - 使用日数
   * @param daysInMonth - 月の日数
   * @returns 日割り料金
   */
  calculateProRata(
    monthlyRate: number,
    daysUsed: number,
    daysInMonth: number = 30
  ): number {
    return this.round((monthlyRate / daysInMonth) * daysUsed);
  }

  /**
   * 数値を丸める
   */
  private round(value: number): number {
    const factor = Math.pow(10, this.decimalPlaces);
    return Math.round(value * factor) / factor;
  }

  /**
   * 設定を取得
   */
  getConfig(): Required<BillingConfig> {
    return {
      slotMinutes: this.slotMinutes,
      fullRefundHours: this.fullRefundHours,
      partialRefundPercentage: this.partialRefundPercentage,
      decimalPlaces: this.decimalPlaces,
    };
  }
}

/**
 * デフォルトのBillingCalculatorインスタンス
 */
export const defaultBillingCalculator = new BillingCalculator();
