/**
 * ThresholdAlert - 閾値ベースのアラート・監視ユーティリティ
 *
 * @description
 * 値が閾値を超えた/下回った際のアラート判定を行うサービスクラス。
 * 在庫管理、リソース監視、容量管理、SLA監視などで使用。
 *
 * @example
 * ```typescript
 * const alert = new ThresholdAlert({
 *   warningThreshold: 80,
 *   criticalThreshold: 95,
 *   direction: 'above', // 閾値を超えたらアラート
 * });
 *
 * // アラートレベルをチェック
 * const level = alert.check(85); // 'warning'
 * const level2 = alert.check(98); // 'critical'
 *
 * // 詳細な結果を取得
 * const result = alert.evaluate(85);
 * // { level: 'warning', value: 85, threshold: 80, exceeded: true, ... }
 * ```
 *
 * @since 1.1.0
 * @see REQ-LEARN-003 - 繰り返しパターンの抽出
 */

/**
 * アラートレベル
 */
export type AlertLevel = 'normal' | 'warning' | 'critical';

/**
 * 閾値チェックの方向
 */
export type ThresholdDirection = 'above' | 'below';

/**
 * ThresholdAlertの設定オプション
 */
export interface ThresholdConfig {
  /** 警告閾値 */
  warningThreshold: number;
  /** 危険閾値 */
  criticalThreshold: number;
  /** 閾値チェックの方向。'above': 超過でアラート、'below': 下回りでアラート */
  direction?: ThresholdDirection;
  /** ヒステリシス（回復判定のマージン）。デフォルト: 0 */
  hysteresis?: number;
  /** 閾値名（ログ/通知用）。デフォルト: 'value' */
  name?: string;
  /** 単位（表示用）。デフォルト: '' */
  unit?: string;
}

/**
 * アラート評価結果
 */
export interface AlertResult {
  /** アラートレベル */
  level: AlertLevel;
  /** 現在値 */
  value: number;
  /** 超過した閾値（なければundefined） */
  threshold: number | undefined;
  /** 閾値を超過/下回ったか */
  exceeded: boolean;
  /** 閾値チェックの方向 */
  direction: ThresholdDirection;
  /** 警告閾値までの残り */
  marginToWarning: number;
  /** 危険閾値までの残り */
  marginToCritical: number;
  /** 使用率（%）- 0-criticalThresholdの範囲で計算 */
  percentage: number;
  /** メッセージ */
  message: string;
}

/**
 * 複数閾値の評価結果
 */
export interface MultiAlertResult {
  /** 全体のアラートレベル（最も高いレベル） */
  overallLevel: AlertLevel;
  /** 各閾値の評価結果 */
  details: Map<string, AlertResult>;
  /** 警告以上のアラート数 */
  warningCount: number;
  /** 危険アラート数 */
  criticalCount: number;
  /** サマリーメッセージ */
  summary: string;
}

/**
 * 閾値ベースのアラート評価サービス
 */
export class ThresholdAlert {
  private readonly warningThreshold: number;
  private readonly criticalThreshold: number;
  private readonly direction: ThresholdDirection;
  private readonly hysteresis: number;
  private readonly name: string;
  private readonly unit: string;
  private lastLevel: AlertLevel = 'normal';

  constructor(config: ThresholdConfig) {
    this.warningThreshold = config.warningThreshold;
    this.criticalThreshold = config.criticalThreshold;
    this.direction = config.direction ?? 'above';
    this.hysteresis = config.hysteresis ?? 0;
    this.name = config.name ?? 'value';
    this.unit = config.unit ?? '';

    // 閾値の妥当性チェック
    if (this.direction === 'above') {
      if (this.warningThreshold > this.criticalThreshold) {
        throw new Error(
          'For "above" direction, warningThreshold must be <= criticalThreshold'
        );
      }
    } else {
      if (this.warningThreshold < this.criticalThreshold) {
        throw new Error(
          'For "below" direction, warningThreshold must be >= criticalThreshold'
        );
      }
    }
  }

  /**
   * 値のアラートレベルをチェック
   *
   * @param value - チェックする値
   * @returns アラートレベル
   */
  check(value: number): AlertLevel {
    return this.evaluate(value).level;
  }

  /**
   * 値を詳細に評価
   *
   * @param value - 評価する値
   * @returns 詳細な評価結果
   */
  evaluate(value: number): AlertResult {
    let level: AlertLevel;
    let exceeded = false;
    let threshold: number | undefined;

    if (this.direction === 'above') {
      // 超過でアラート（リソース使用率など）
      if (value >= this.criticalThreshold) {
        level = 'critical';
        exceeded = true;
        threshold = this.criticalThreshold;
      } else if (value >= this.warningThreshold) {
        level = 'warning';
        exceeded = true;
        threshold = this.warningThreshold;
      } else {
        level = 'normal';
      }
    } else {
      // 下回りでアラート（在庫数など）
      if (value <= this.criticalThreshold) {
        level = 'critical';
        exceeded = true;
        threshold = this.criticalThreshold;
      } else if (value <= this.warningThreshold) {
        level = 'warning';
        exceeded = true;
        threshold = this.warningThreshold;
      } else {
        level = 'normal';
      }
    }

    // ヒステリシスを適用（チャタリング防止）
    if (this.hysteresis > 0) {
      level = this.applyHysteresis(value, level);
    }

    this.lastLevel = level;

    const marginToWarning = this.calculateMargin(value, this.warningThreshold);
    const marginToCritical = this.calculateMargin(value, this.criticalThreshold);
    const percentage = this.calculatePercentage(value);

    return {
      level,
      value,
      threshold,
      exceeded,
      direction: this.direction,
      marginToWarning,
      marginToCritical,
      percentage,
      message: this.generateMessage(level, value),
    };
  }

  /**
   * 閾値を超過しているかチェック
   *
   * @param value - チェックする値
   * @returns 超過している場合true
   */
  isExceeded(value: number): boolean {
    return this.evaluate(value).exceeded;
  }

  /**
   * 警告レベル以上かチェック
   *
   * @param value - チェックする値
   * @returns 警告以上の場合true
   */
  isWarningOrAbove(value: number): boolean {
    const level = this.check(value);
    return level === 'warning' || level === 'critical';
  }

  /**
   * 危険レベルかチェック
   *
   * @param value - チェックする値
   * @returns 危険レベルの場合true
   */
  isCritical(value: number): boolean {
    return this.check(value) === 'critical';
  }

  /**
   * 閾値までの残り値を計算
   *
   * @param value - 現在値
   * @param threshold - 閾値
   * @returns 残り値（負の場合は超過）
   */
  private calculateMargin(value: number, threshold: number): number {
    if (this.direction === 'above') {
      return threshold - value;
    } else {
      return value - threshold;
    }
  }

  /**
   * 使用率/消費率を計算（パーセンテージ）
   *
   * @param value - 現在値
   * @returns パーセンテージ（0-100+）
   */
  private calculatePercentage(value: number): number {
    if (this.direction === 'above') {
      // 0からcriticalThresholdの範囲で計算
      if (this.criticalThreshold === 0) return 0;
      return Math.round((value / this.criticalThreshold) * 100);
    } else {
      // warningThresholdから0の範囲で計算
      if (this.warningThreshold === 0) return 100;
      const consumed = this.warningThreshold - value;
      return Math.round((consumed / this.warningThreshold) * 100);
    }
  }

  /**
   * ヒステリシスを適用してチャタリングを防止
   *
   * @param value - 現在値
   * @param newLevel - 新しいレベル
   * @returns 調整後のレベル
   */
  private applyHysteresis(value: number, newLevel: AlertLevel): AlertLevel {
    // レベルが下がる場合のみヒステリシスを適用
    if (this.isLevelHigher(this.lastLevel, newLevel)) {
      // 前回のレベルが高かった場合、ヒステリシス分の余裕を持たせる
      if (this.direction === 'above') {
        if (
          this.lastLevel === 'critical' &&
          value > this.criticalThreshold - this.hysteresis
        ) {
          return 'critical';
        }
        if (
          this.lastLevel === 'warning' &&
          value > this.warningThreshold - this.hysteresis
        ) {
          return 'warning';
        }
      } else {
        if (
          this.lastLevel === 'critical' &&
          value < this.criticalThreshold + this.hysteresis
        ) {
          return 'critical';
        }
        if (
          this.lastLevel === 'warning' &&
          value < this.warningThreshold + this.hysteresis
        ) {
          return 'warning';
        }
      }
    }
    return newLevel;
  }

  /**
   * レベルの高低を比較
   */
  private isLevelHigher(level1: AlertLevel, level2: AlertLevel): boolean {
    const order: Record<AlertLevel, number> = {
      normal: 0,
      warning: 1,
      critical: 2,
    };
    return order[level1] > order[level2];
  }

  /**
   * アラートメッセージを生成
   */
  private generateMessage(level: AlertLevel, value: number): string {
    const valueStr = this.unit ? `${value}${this.unit}` : String(value);

    switch (level) {
      case 'critical':
        return `[CRITICAL] ${this.name} is at ${valueStr} (threshold: ${this.criticalThreshold}${this.unit})`;
      case 'warning':
        return `[WARNING] ${this.name} is at ${valueStr} (threshold: ${this.warningThreshold}${this.unit})`;
      default:
        return `[OK] ${this.name} is at ${valueStr}`;
    }
  }

  /**
   * 現在の設定を取得
   */
  getConfig(): ThresholdConfig {
    return {
      warningThreshold: this.warningThreshold,
      criticalThreshold: this.criticalThreshold,
      direction: this.direction,
      hysteresis: this.hysteresis,
      name: this.name,
      unit: this.unit,
    };
  }
}

/**
 * 複数の閾値を一括管理するサービス
 */
export class MultiThresholdAlert {
  private alerts: Map<string, ThresholdAlert> = new Map();

  /**
   * 閾値アラートを登録
   *
   * @param name - 識別名
   * @param config - 閾値設定
   */
  register(name: string, config: ThresholdConfig): void {
    this.alerts.set(name, new ThresholdAlert({ ...config, name }));
  }

  /**
   * 閾値アラートを削除
   *
   * @param name - 識別名
   */
  unregister(name: string): void {
    this.alerts.delete(name);
  }

  /**
   * 単一の値をチェック
   *
   * @param name - 識別名
   * @param value - チェックする値
   * @returns アラートレベル
   */
  check(name: string, value: number): AlertLevel {
    const alert = this.alerts.get(name);
    if (!alert) {
      throw new Error(`Alert "${name}" not registered`);
    }
    return alert.check(value);
  }

  /**
   * 複数の値を一括評価
   *
   * @param values - 名前と値のマップ
   * @returns 一括評価結果
   */
  evaluateAll(values: Map<string, number> | Record<string, number>): MultiAlertResult {
    const details = new Map<string, AlertResult>();
    let overallLevel: AlertLevel = 'normal';
    let warningCount = 0;
    let criticalCount = 0;

    const entries =
      values instanceof Map ? values.entries() : Object.entries(values);

    for (const [name, value] of entries) {
      const alert = this.alerts.get(name);
      if (!alert) continue;

      const result = alert.evaluate(value);
      details.set(name, result);

      if (result.level === 'critical') {
        overallLevel = 'critical';
        criticalCount++;
      } else if (result.level === 'warning') {
        if (overallLevel !== 'critical') {
          overallLevel = 'warning';
        }
        warningCount++;
      }
    }

    const summary = this.generateSummary(overallLevel, warningCount, criticalCount);

    return {
      overallLevel,
      details,
      warningCount,
      criticalCount,
      summary,
    };
  }

  /**
   * 全アラートの名前を取得
   */
  getRegisteredNames(): string[] {
    return Array.from(this.alerts.keys());
  }

  /**
   * サマリーメッセージを生成
   */
  private generateSummary(
    level: AlertLevel,
    warningCount: number,
    criticalCount: number
  ): string {
    if (level === 'critical') {
      return `${criticalCount} critical alert(s), ${warningCount} warning(s)`;
    } else if (level === 'warning') {
      return `${warningCount} warning(s)`;
    }
    return 'All systems normal';
  }
}

// ========================================
// プリセット閾値設定
// ========================================

/**
 * リソース使用率用の閾値設定（CPU、メモリ、ディスクなど）
 */
export const resourceUsageThreshold: ThresholdConfig = {
  warningThreshold: 80,
  criticalThreshold: 95,
  direction: 'above',
  unit: '%',
};

/**
 * 在庫数用の閾値設定
 */
export const inventoryThreshold: ThresholdConfig = {
  warningThreshold: 10,
  criticalThreshold: 5,
  direction: 'below',
  unit: '個',
};

/**
 * レスポンスタイム用の閾値設定（ミリ秒）
 */
export const responseTimeThreshold: ThresholdConfig = {
  warningThreshold: 1000,
  criticalThreshold: 3000,
  direction: 'above',
  unit: 'ms',
};

/**
 * エラー率用の閾値設定（%）
 */
export const errorRateThreshold: ThresholdConfig = {
  warningThreshold: 1,
  criticalThreshold: 5,
  direction: 'above',
  unit: '%',
};

/**
 * 容量使用率用の閾値設定（予約数、座席数など）
 */
export const capacityThreshold: ThresholdConfig = {
  warningThreshold: 80,
  criticalThreshold: 95,
  direction: 'above',
  unit: '%',
};

/**
 * バッテリー残量用の閾値設定
 */
export const batteryThreshold: ThresholdConfig = {
  warningThreshold: 20,
  criticalThreshold: 5,
  direction: 'below',
  unit: '%',
};
