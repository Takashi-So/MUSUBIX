/**
 * TimeSlotService - 時間帯ベースの予約管理ユーティリティ
 *
 * @description
 * 時間スロット生成、重複検出、時間検証を提供するサービスクラス。
 * 予約システム、スケジューリング、リソース管理で使用。
 *
 * @example
 * ```typescript
 * const timeSlotService = new TimeSlotService({
 *   slotMinutes: 15,
 *   bufferMinutes: 5,
 *   minDurationMinutes: 30,
 *   maxDurationMinutes: 480,
 * });
 *
 * // 時間検証
 * timeSlotService.validateDuration(startTime, endTime);
 *
 * // 重複チェック
 * const hasConflict = timeSlotService.hasConflict(
 *   existingStart, existingEnd,
 *   newStart, newEnd
 * );
 *
 * // スロット生成
 * const slots = timeSlotService.generateSlots(date, 9, 18);
 * ```
 *
 * @since 1.0.21
 * @see REQ-LEARN-003 - 繰り返しパターンの抽出
 */

/**
 * TimeSlotServiceの設定オプション
 */
export interface TimeSlotConfig {
  /** スロットの長さ（分）。デフォルト: 15 */
  slotMinutes?: number;
  /** 連続予約間のバッファ時間（分）。デフォルト: 5 */
  bufferMinutes?: number;
  /** 最小予約時間（分）。デフォルト: 30 */
  minDurationMinutes?: number;
  /** 最大予約時間（分）。デフォルト: 480（8時間） */
  maxDurationMinutes?: number;
}

/**
 * 時間スロット
 */
export interface TimeSlot {
  /** スロット開始時刻 */
  startTime: Date;
  /** スロット終了時刻 */
  endTime: Date;
  /** 利用可能かどうか */
  isAvailable: boolean;
}

/**
 * 重複チェック結果
 */
export interface ConflictResult {
  /** 重複があるかどうか */
  hasConflict: boolean;
  /** 重複タイプ */
  conflictType?: 'overlap' | 'buffer_violation' | 'none';
  /** 重複時間（分） */
  overlapMinutes?: number;
}

/**
 * 時間スロット管理サービス
 */
export class TimeSlotService {
  private readonly slotMinutes: number;
  private readonly bufferMinutes: number;
  private readonly minDurationMinutes: number;
  private readonly maxDurationMinutes: number;

  constructor(config: TimeSlotConfig = {}) {
    this.slotMinutes = config.slotMinutes ?? 15;
    this.bufferMinutes = config.bufferMinutes ?? 5;
    this.minDurationMinutes = config.minDurationMinutes ?? 30;
    this.maxDurationMinutes = config.maxDurationMinutes ?? 480;
  }

  /**
   * 予約時間の検証
   *
   * @param startTime - 開始時刻
   * @param endTime - 終了時刻
   * @throws Error - 時間制約違反時
   */
  validateDuration(startTime: Date, endTime: Date): void {
    if (startTime >= endTime) {
      throw new Error('Start time must be before end time');
    }

    const durationMinutes = this.getDurationMinutes(startTime, endTime);

    if (durationMinutes < this.minDurationMinutes) {
      throw new Error(`Minimum duration is ${this.minDurationMinutes} minutes`);
    }

    if (durationMinutes > this.maxDurationMinutes) {
      throw new Error(`Maximum duration is ${this.maxDurationMinutes} minutes (${this.maxDurationMinutes / 60} hours)`);
    }

    if (durationMinutes % this.slotMinutes !== 0) {
      throw new Error(`Duration must be in ${this.slotMinutes} minute increments`);
    }
  }

  /**
   * 時間の重複チェック（バッファ含む）
   *
   * @param existingStart - 既存予約の開始時刻
   * @param existingEnd - 既存予約の終了時刻
   * @param newStart - 新規予約の開始時刻
   * @param newEnd - 新規予約の終了時刻
   * @returns 重複があるかどうか
   */
  hasConflict(
    existingStart: Date,
    existingEnd: Date,
    newStart: Date,
    newEnd: Date
  ): boolean {
    const result = this.checkConflict(existingStart, existingEnd, newStart, newEnd);
    return result.hasConflict;
  }

  /**
   * 詳細な重複チェック
   *
   * @param existingStart - 既存予約の開始時刻
   * @param existingEnd - 既存予約の終了時刻
   * @param newStart - 新規予約の開始時刻
   * @param newEnd - 新規予約の終了時刻
   * @returns 重複チェック結果
   */
  checkConflict(
    existingStart: Date,
    existingEnd: Date,
    newStart: Date,
    newEnd: Date
  ): ConflictResult {
    // バッファを追加した終了時刻
    const bufferedEnd = new Date(existingEnd.getTime() + this.bufferMinutes * 60 * 1000);

    // 直接重複チェック
    if (newStart < existingEnd && newEnd > existingStart) {
      const overlapStart = Math.max(newStart.getTime(), existingStart.getTime());
      const overlapEnd = Math.min(newEnd.getTime(), existingEnd.getTime());
      const overlapMinutes = (overlapEnd - overlapStart) / (1000 * 60);

      return {
        hasConflict: true,
        conflictType: 'overlap',
        overlapMinutes: Math.max(0, overlapMinutes),
      };
    }

    // バッファ期間内チェック
    if (newStart < bufferedEnd && newEnd > existingStart) {
      return {
        hasConflict: true,
        conflictType: 'buffer_violation',
        overlapMinutes: 0,
      };
    }

    return {
      hasConflict: false,
      conflictType: 'none',
    };
  }

  /**
   * 時間スロットを生成
   *
   * @param date - 対象日
   * @param startHour - 開始時間（0-23）
   * @param endHour - 終了時間（0-24）
   * @returns 時間スロットの配列
   */
  generateSlots(date: Date, startHour: number, endHour: number): TimeSlot[] {
    const slots: TimeSlot[] = [];
    const current = new Date(date);
    current.setHours(startHour, 0, 0, 0);

    const end = new Date(date);
    end.setHours(endHour, 0, 0, 0);

    while (current < end) {
      const slotEnd = new Date(current.getTime() + this.slotMinutes * 60 * 1000);
      slots.push({
        startTime: new Date(current),
        endTime: slotEnd,
        isAvailable: true,
      });
      current.setTime(slotEnd.getTime());
    }

    return slots;
  }

  /**
   * 利用可能なスロットを取得
   *
   * @param slots - 全スロット
   * @param reservations - 既存予約（startTime, endTime を持つオブジェクト）
   * @returns 利用可能なスロットのみ
   */
  getAvailableSlots(
    slots: TimeSlot[],
    reservations: Array<{ startTime: Date; endTime: Date }>
  ): TimeSlot[] {
    return slots.map((slot) => {
      const isAvailable = !reservations.some((res) =>
        this.hasConflict(res.startTime, res.endTime, slot.startTime, slot.endTime)
      );
      return { ...slot, isAvailable };
    });
  }

  /**
   * 時間を最も近いスロットに丸める
   *
   * @param time - 元の時刻
   * @param roundUp - 切り上げるかどうか
   * @returns 丸められた時刻
   */
  roundToSlot(time: Date, roundUp = false): Date {
    const ms = time.getTime();
    const slotMs = this.slotMinutes * 60 * 1000;

    if (roundUp) {
      return new Date(Math.ceil(ms / slotMs) * slotMs);
    }
    return new Date(Math.floor(ms / slotMs) * slotMs);
  }

  /**
   * 時間差を分で取得
   */
  getDurationMinutes(startTime: Date, endTime: Date): number {
    return (endTime.getTime() - startTime.getTime()) / (1000 * 60);
  }

  /**
   * 設定を取得
   */
  getConfig(): Required<TimeSlotConfig> {
    return {
      slotMinutes: this.slotMinutes,
      bufferMinutes: this.bufferMinutes,
      minDurationMinutes: this.minDurationMinutes,
      maxDurationMinutes: this.maxDurationMinutes,
    };
  }
}

/**
 * デフォルトのTimeSlotServiceインスタンス
 */
export const defaultTimeSlotService = new TimeSlotService();
