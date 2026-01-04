/**
 * TimeWindowValidator - 時間枠検証ユーティリティ
 *
 * @description
 * 操作が許可される時間枠の検証を提供するサービスクラス。
 * チェックイン、変更期限、キャンセル期限などの検証に使用。
 *
 * @example
 * ```typescript
 * const validator = new TimeWindowValidator();
 *
 * // チェックイン可能か確認（開始15分前から15分後まで）
 * const canCheckIn = validator.isWithinWindow(
 *   reservationStart,
 *   checkInTime,
 *   { beforeMinutes: 15, afterMinutes: 15 }
 * );
 *
 * // 変更可能か確認（開始1時間前まで）
 * const canChange = validator.isBeforeDeadline(
 *   reservationStart,
 *   changeTime,
 *   { hoursBeforeDeadline: 1 }
 * );
 * ```
 *
 * @since 1.0.21
 * @see REQ-LEARN-003 - 繰り返しパターンの抽出
 */

/**
 * 時間枠オプション
 */
export interface WindowOptions {
  /** 基準時刻より前の許可時間（分） */
  beforeMinutes?: number;
  /** 基準時刻より後の許可時間（分） */
  afterMinutes?: number;
}

/**
 * 期限オプション
 */
export interface DeadlineOptions {
  /** 基準時刻より前の期限（時間） */
  hoursBeforeDeadline?: number;
  /** 基準時刻より前の期限（分） */
  minutesBeforeDeadline?: number;
}

/**
 * 時間枠検証結果
 */
export interface WindowValidationResult {
  /** 時間枠内かどうか */
  isValid: boolean;
  /** 時間枠の開始時刻 */
  windowStart: Date;
  /** 時間枠の終了時刻 */
  windowEnd: Date;
  /** チェック時刻と時間枠開始の差（分） */
  minutesFromWindowStart: number;
  /** チェック時刻と時間枠終了の差（分） */
  minutesToWindowEnd: number;
}

/**
 * 期限検証結果
 */
export interface DeadlineValidationResult {
  /** 期限内かどうか */
  isValid: boolean;
  /** 期限時刻 */
  deadline: Date;
  /** 期限までの残り時間（時間） */
  hoursRemaining: number;
  /** 期限までの残り時間（分） */
  minutesRemaining: number;
}

/**
 * 時間枠検証サービス
 */
export class TimeWindowValidator {
  /**
   * 時間枠内かどうかを確認
   *
   * @param referenceTime - 基準時刻
   * @param checkTime - チェックする時刻
   * @param options - 時間枠オプション
   * @returns 時間枠内かどうか
   */
  isWithinWindow(
    referenceTime: Date,
    checkTime: Date,
    options: WindowOptions = {}
  ): boolean {
    const result = this.validateWindow(referenceTime, checkTime, options);
    return result.isValid;
  }

  /**
   * 詳細な時間枠検証
   *
   * @param referenceTime - 基準時刻
   * @param checkTime - チェックする時刻
   * @param options - 時間枠オプション
   * @returns 時間枠検証結果
   */
  validateWindow(
    referenceTime: Date,
    checkTime: Date,
    options: WindowOptions = {}
  ): WindowValidationResult {
    const beforeMinutes = options.beforeMinutes ?? 0;
    const afterMinutes = options.afterMinutes ?? 0;

    const windowStart = new Date(referenceTime.getTime() - beforeMinutes * 60 * 1000);
    const windowEnd = new Date(referenceTime.getTime() + afterMinutes * 60 * 1000);

    const isValid = checkTime >= windowStart && checkTime <= windowEnd;
    const minutesFromWindowStart = (checkTime.getTime() - windowStart.getTime()) / (1000 * 60);
    const minutesToWindowEnd = (windowEnd.getTime() - checkTime.getTime()) / (1000 * 60);

    return {
      isValid,
      windowStart,
      windowEnd,
      minutesFromWindowStart,
      minutesToWindowEnd,
    };
  }

  /**
   * 期限前かどうかを確認
   *
   * @param referenceTime - 基準時刻（イベント開始時刻など）
   * @param checkTime - チェックする時刻
   * @param options - 期限オプション
   * @returns 期限前かどうか
   */
  isBeforeDeadline(
    referenceTime: Date,
    checkTime: Date,
    options: DeadlineOptions = {}
  ): boolean {
    const result = this.validateDeadline(referenceTime, checkTime, options);
    return result.isValid;
  }

  /**
   * 詳細な期限検証
   *
   * @param referenceTime - 基準時刻
   * @param checkTime - チェックする時刻
   * @param options - 期限オプション
   * @returns 期限検証結果
   */
  validateDeadline(
    referenceTime: Date,
    checkTime: Date,
    options: DeadlineOptions = {}
  ): DeadlineValidationResult {
    const hoursBeforeDeadline = options.hoursBeforeDeadline ?? 0;
    const minutesBeforeDeadline = options.minutesBeforeDeadline ?? 0;

    const totalMinutesBefore = hoursBeforeDeadline * 60 + minutesBeforeDeadline;
    const deadline = new Date(referenceTime.getTime() - totalMinutesBefore * 60 * 1000);

    const minutesRemaining = (deadline.getTime() - checkTime.getTime()) / (1000 * 60);
    const hoursRemaining = minutesRemaining / 60;
    const isValid = checkTime < deadline;

    return {
      isValid,
      deadline,
      hoursRemaining: Math.max(0, hoursRemaining),
      minutesRemaining: Math.max(0, minutesRemaining),
    };
  }

  /**
   * 基準時刻までの残り時間を取得
   *
   * @param referenceTime - 基準時刻
   * @param checkTime - チェックする時刻
   * @returns 残り時間（時間単位）
   */
  hoursUntil(referenceTime: Date, checkTime: Date = new Date()): number {
    return (referenceTime.getTime() - checkTime.getTime()) / (1000 * 60 * 60);
  }

  /**
   * 基準時刻までの残り時間を取得
   *
   * @param referenceTime - 基準時刻
   * @param checkTime - チェックする時刻
   * @returns 残り時間（分単位）
   */
  minutesUntil(referenceTime: Date, checkTime: Date = new Date()): number {
    return (referenceTime.getTime() - checkTime.getTime()) / (1000 * 60);
  }

  /**
   * 基準時刻からの経過時間を取得
   *
   * @param referenceTime - 基準時刻
   * @param checkTime - チェックする時刻
   * @returns 経過時間（分単位）
   */
  minutesSince(referenceTime: Date, checkTime: Date = new Date()): number {
    return (checkTime.getTime() - referenceTime.getTime()) / (1000 * 60);
  }

  /**
   * 過去かどうかを確認
   *
   * @param time - 確認する時刻
   * @param referenceTime - 基準時刻（デフォルト: 現在時刻）
   * @returns 過去かどうか
   */
  isPast(time: Date, referenceTime: Date = new Date()): boolean {
    return time < referenceTime;
  }

  /**
   * 未来かどうかを確認
   *
   * @param time - 確認する時刻
   * @param referenceTime - 基準時刻（デフォルト: 現在時刻）
   * @returns 未来かどうか
   */
  isFuture(time: Date, referenceTime: Date = new Date()): boolean {
    return time > referenceTime;
  }

  /**
   * 同じ日かどうかを確認
   *
   * @param date1 - 日付1
   * @param date2 - 日付2
   * @returns 同じ日かどうか
   */
  isSameDay(date1: Date, date2: Date): boolean {
    return (
      date1.getFullYear() === date2.getFullYear() &&
      date1.getMonth() === date2.getMonth() &&
      date1.getDate() === date2.getDate()
    );
  }

  /**
   * 営業時間内かどうかを確認
   *
   * @param time - 確認する時刻
   * @param startHour - 営業開始時間（0-23）
   * @param endHour - 営業終了時間（0-24）
   * @returns 営業時間内かどうか
   */
  isWithinBusinessHours(time: Date, startHour: number, endHour: number): boolean {
    const hours = time.getHours();
    const minutes = time.getMinutes();
    const totalMinutes = hours * 60 + minutes;

    const startMinutes = startHour * 60;
    const endMinutes = endHour * 60;

    return totalMinutes >= startMinutes && totalMinutes < endMinutes;
  }
}

/**
 * デフォルトのTimeWindowValidatorインスタンス
 */
export const defaultTimeWindowValidator = new TimeWindowValidator();
