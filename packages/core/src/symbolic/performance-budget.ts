/**
 * @file performance-budget.ts
 * @description PerformanceBudget - 段階別予算/計測/部分結果
 * @requirement REQ-NFR-001
 * @design DES-SYMB-001 §6.1
 * @task TSK-SYMB-018
 */

import type { Explanation, Evidence } from './types.js';

// ============================================================================
// Types
// ============================================================================

/**
 * 計測ステップ
 */
export type BudgetStep = 'parse' | 'vc_gen' | 'z3' | 'explain' | 'audit' | 'other';

/**
 * タイムアウト種別
 */
export type TimeoutKind = 'z3_timeout' | 'overall_timeout' | 'step_timeout';

/**
 * タイムアウト情報
 */
export interface TimeoutInfo {
  /** 種別 */
  kind: TimeoutKind;
  /** 予算（ms） */
  budgetMs: number;
  /** 経過時間（ms） */
  elapsedMs: number;
  /** タイムアウトしたステップ */
  step?: BudgetStep;
  /** メッセージ */
  message: string;
}

/**
 * ステップ計測結果
 */
export interface StepMeasurement {
  /** ステップ名 */
  step: BudgetStep;
  /** 開始時刻 */
  startedAt: string;
  /** 終了時刻 */
  endedAt?: string;
  /** 経過時間（ms） */
  durationMs: number;
  /** 成功/失敗/タイムアウト */
  status: 'completed' | 'failed' | 'timeout' | 'skipped';
  /** エラーメッセージ */
  error?: string;
}

/**
 * パフォーマンス計測結果
 */
export interface PerformanceMeasurement {
  /** 開始時刻 */
  startedAt: string;
  /** 終了時刻 */
  endedAt?: string;
  /** 総経過時間（ms） */
  totalDurationMs: number;
  /** ステップ別計測 */
  steps: StepMeasurement[];
  /** タイムアウト情報（発生した場合） */
  timeout?: TimeoutInfo;
  /** 予算内に収まったか */
  withinBudget: boolean;
  /** 残り予算（ms） */
  remainingBudgetMs: number;
}

/**
 * 部分結果メタデータ
 */
export interface PartialResultMetadata {
  /** 部分結果かどうか */
  isPartial: boolean;
  /** 利用不可だったチェック */
  unavailableChecks: BudgetStep[];
  /** スキップされたチェック */
  skippedChecks: BudgetStep[];
  /** タイムアウト情報 */
  timeout?: TimeoutInfo;
  /** 計測結果 */
  measurement: PerformanceMeasurement;
}

/**
 * パフォーマンス予算設定
 */
export interface PerformanceBudgetConfig {
  /** 単一関数の検証に割り当てる全体予算（ms） */
  perFunctionBudgetMs?: number;
  /** 段階別の上限（ms） */
  stepBudgetsMs?: Partial<Record<BudgetStep, number>>;
  /** SLO評価のサンプル数/集計窓 */
  metricsWindowSize?: number;
  /** タイムアウト時に部分結果を返すか */
  returnPartialOnTimeout?: boolean;
}

/**
 * SLOメトリクス
 */
export interface SloMetrics {
  /** サンプル数 */
  sampleCount: number;
  /** 予算内完了数 */
  withinBudgetCount: number;
  /** 予算内完了率 (%) */
  withinBudgetPercentage: number;
  /** 平均所要時間（ms） */
  averageDurationMs: number;
  /** P95所要時間（ms） */
  p95DurationMs: number;
  /** P99所要時間（ms） */
  p99DurationMs: number;
  /** 最大所要時間（ms） */
  maxDurationMs: number;
  /** ステップ別平均 */
  stepAverages: Partial<Record<BudgetStep, number>>;
}

// ============================================================================
// Constants
// ============================================================================

/**
 * デフォルト設定
 */
export const DEFAULT_BUDGET_CONFIG: Required<PerformanceBudgetConfig> = {
  perFunctionBudgetMs: 5000,
  stepBudgetsMs: {
    parse: 500,
    vc_gen: 1000,
    z3: 3000,
    explain: 300,
    audit: 200,
  },
  metricsWindowSize: 100,
  returnPartialOnTimeout: true,
};

// ============================================================================
// PerformanceBudget Class
// ============================================================================

/**
 * パフォーマンス予算マネージャー
 */
export class PerformanceBudget {
  private readonly config: Required<PerformanceBudgetConfig>;
  private currentMeasurement: PerformanceMeasurement | null = null;
  private currentStepStart: number | null = null;
  private currentStep: BudgetStep | null = null;
  private readonly historicalMeasurements: PerformanceMeasurement[] = [];

  constructor(config: PerformanceBudgetConfig = {}) {
    this.config = {
      ...DEFAULT_BUDGET_CONFIG,
      ...config,
      stepBudgetsMs: {
        ...DEFAULT_BUDGET_CONFIG.stepBudgetsMs,
        ...config.stepBudgetsMs,
      },
    };
  }

  /**
   * 計測を開始
   */
  start(): void {
    this.currentMeasurement = {
      startedAt: new Date().toISOString(),
      totalDurationMs: 0,
      steps: [],
      withinBudget: true,
      remainingBudgetMs: this.config.perFunctionBudgetMs,
    };
  }

  /**
   * ステップを開始
   */
  startStep(step: BudgetStep): void {
    if (!this.currentMeasurement) {
      this.start();
    }

    // 前のステップが未終了なら終了
    if (this.currentStep) {
      this.endStep();
    }

    this.currentStep = step;
    this.currentStepStart = Date.now();
  }

  /**
   * ステップを終了
   */
  endStep(status: 'completed' | 'failed' | 'timeout' | 'skipped' = 'completed', error?: string): StepMeasurement | null {
    if (!this.currentMeasurement || !this.currentStep || this.currentStepStart === null) {
      return null;
    }

    const endTime = Date.now();
    const durationMs = endTime - this.currentStepStart;

    const measurement: StepMeasurement = {
      step: this.currentStep,
      startedAt: new Date(this.currentStepStart).toISOString(),
      endedAt: new Date(endTime).toISOString(),
      durationMs,
      status,
      error,
    };

    this.currentMeasurement.steps.push(measurement);
    this.currentMeasurement.totalDurationMs = this.getElapsedMs();
    this.currentMeasurement.remainingBudgetMs = Math.max(
      0,
      this.config.perFunctionBudgetMs - this.currentMeasurement.totalDurationMs,
    );

    // ステップ予算チェック
    const stepBudget = this.config.stepBudgetsMs[this.currentStep];
    if (stepBudget && durationMs > stepBudget && status === 'completed') {
      // ステップ予算超過だが完了
      measurement.status = 'completed';
    }

    this.currentStep = null;
    this.currentStepStart = null;

    return measurement;
  }

  /**
   * 計測を終了
   */
  end(): PerformanceMeasurement {
    if (!this.currentMeasurement) {
      throw new Error('Measurement not started');
    }

    // 未終了のステップを終了
    if (this.currentStep) {
      this.endStep();
    }

    const endTime = new Date();
    this.currentMeasurement.endedAt = endTime.toISOString();
    this.currentMeasurement.totalDurationMs = this.getElapsedMs();
    this.currentMeasurement.withinBudget = this.currentMeasurement.totalDurationMs <= this.config.perFunctionBudgetMs;
    this.currentMeasurement.remainingBudgetMs = Math.max(
      0,
      this.config.perFunctionBudgetMs - this.currentMeasurement.totalDurationMs,
    );

    // 履歴に追加
    this.historicalMeasurements.push(this.currentMeasurement);
    if (this.historicalMeasurements.length > this.config.metricsWindowSize) {
      this.historicalMeasurements.shift();
    }

    const result = this.currentMeasurement;
    this.currentMeasurement = null;

    return result;
  }

  /**
   * 経過時間を取得
   */
  getElapsedMs(): number {
    if (!this.currentMeasurement) return 0;

    const startTime = new Date(this.currentMeasurement.startedAt).getTime();
    return Date.now() - startTime;
  }

  /**
   * 残り予算を取得
   */
  getRemainingBudgetMs(): number {
    return Math.max(0, this.config.perFunctionBudgetMs - this.getElapsedMs());
  }

  /**
   * 予算内かチェック
   */
  isWithinBudget(): boolean {
    return this.getElapsedMs() <= this.config.perFunctionBudgetMs;
  }

  /**
   * ステップの予算内かチェック
   */
  isStepWithinBudget(step: BudgetStep): boolean {
    const stepBudget = this.config.stepBudgetsMs[step];
    if (!stepBudget) return true;

    const stepMeasurement = this.currentMeasurement?.steps.find((s) => s.step === step);
    return !stepMeasurement || stepMeasurement.durationMs <= stepBudget;
  }

  /**
   * タイムアウトを記録
   */
  recordTimeout(kind: TimeoutKind, step?: BudgetStep): TimeoutInfo {
    const timeout: TimeoutInfo = {
      kind,
      budgetMs: step
        ? (this.config.stepBudgetsMs[step] ?? this.config.perFunctionBudgetMs)
        : this.config.perFunctionBudgetMs,
      elapsedMs: this.getElapsedMs(),
      step,
      message: this.formatTimeoutMessage(kind, step),
    };

    if (this.currentMeasurement) {
      this.currentMeasurement.timeout = timeout;
      this.currentMeasurement.withinBudget = false;
    }

    return timeout;
  }

  /**
   * 部分結果メタデータを生成
   */
  generatePartialResultMetadata(unavailableChecks: BudgetStep[] = [], skippedChecks: BudgetStep[] = []): PartialResultMetadata {
    const measurement = this.currentMeasurement ?? {
      startedAt: new Date().toISOString(),
      totalDurationMs: 0,
      steps: [],
      withinBudget: false,
      remainingBudgetMs: 0,
    };

    return {
      isPartial: unavailableChecks.length > 0 || skippedChecks.length > 0,
      unavailableChecks,
      skippedChecks,
      timeout: measurement.timeout,
      measurement,
    };
  }

  /**
   * SLOメトリクスを計算
   */
  calculateSloMetrics(): SloMetrics {
    const measurements = this.historicalMeasurements;

    if (measurements.length === 0) {
      return {
        sampleCount: 0,
        withinBudgetCount: 0,
        withinBudgetPercentage: 100,
        averageDurationMs: 0,
        p95DurationMs: 0,
        p99DurationMs: 0,
        maxDurationMs: 0,
        stepAverages: {},
      };
    }

    const durations = measurements.map((m) => m.totalDurationMs).sort((a, b) => a - b);
    const withinBudgetCount = measurements.filter((m) => m.withinBudget).length;

    // ステップ別平均を計算
    const stepTotals: Partial<Record<BudgetStep, { total: number; count: number }>> = {};
    for (const m of measurements) {
      for (const step of m.steps) {
        if (!stepTotals[step.step]) {
          stepTotals[step.step] = { total: 0, count: 0 };
        }
        stepTotals[step.step]!.total += step.durationMs;
        stepTotals[step.step]!.count++;
      }
    }

    const stepAverages: Partial<Record<BudgetStep, number>> = {};
    for (const [step, data] of Object.entries(stepTotals)) {
      stepAverages[step as BudgetStep] = Math.round(data.total / data.count);
    }

    return {
      sampleCount: measurements.length,
      withinBudgetCount,
      withinBudgetPercentage: Math.round((withinBudgetCount / measurements.length) * 100),
      averageDurationMs: Math.round(durations.reduce((a, b) => a + b, 0) / durations.length),
      p95DurationMs: durations[Math.floor(durations.length * 0.95)] ?? 0,
      p99DurationMs: durations[Math.floor(durations.length * 0.99)] ?? 0,
      maxDurationMs: durations[durations.length - 1] ?? 0,
      stepAverages,
    };
  }

  /**
   * 設定を取得
   */
  getConfig(): Required<PerformanceBudgetConfig> {
    return { ...this.config };
  }

  /**
   * 予算付きで関数を実行
   */
  async executeWithBudget<T>(
    step: BudgetStep,
    fn: () => Promise<T>,
  ): Promise<{ result: T | null; timedOut: boolean; measurement: StepMeasurement | null }> {
    this.startStep(step);

    const stepBudget = this.config.stepBudgetsMs[step] ?? this.getRemainingBudgetMs();

    try {
      const result = await Promise.race([
        fn(),
        new Promise<'TIMEOUT'>((resolve) => setTimeout(() => resolve('TIMEOUT'), stepBudget)),
      ]);

      if (result === 'TIMEOUT') {
        const measurement = this.endStep('timeout');
        this.recordTimeout('step_timeout', step);
        return { result: null, timedOut: true, measurement };
      }

      const measurement = this.endStep('completed');
      return { result: result as T, timedOut: false, measurement };
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : 'Unknown error';
      this.endStep('failed', errorMessage);
      throw error;
    }
  }

  /**
   * 説明を生成
   */
  generateExplanation(): Explanation {
    const metrics = this.calculateSloMetrics();
    const measurement = this.currentMeasurement;

    const reasoning: string[] = [];
    reasoning.push(`Performance budget: ${this.config.perFunctionBudgetMs}ms`);

    if (measurement) {
      reasoning.push(`Total elapsed: ${measurement.totalDurationMs}ms`);
      reasoning.push(`Within budget: ${measurement.withinBudget ? 'Yes' : 'No'}`);

      if (measurement.timeout) {
        reasoning.push(`Timeout occurred: ${measurement.timeout.message}`);
      }

      for (const step of measurement.steps) {
        reasoning.push(`Step ${step.step}: ${step.durationMs}ms (${step.status})`);
      }
    }

    if (metrics.sampleCount > 0) {
      reasoning.push(`SLO: ${metrics.withinBudgetPercentage}% within budget (${metrics.sampleCount} samples)`);
      reasoning.push(`P95: ${metrics.p95DurationMs}ms, P99: ${metrics.p99DurationMs}ms`);
    }

    const evidence: Evidence[] = [];
    if (measurement) {
      evidence.push({
        type: 'timing',
        content: JSON.stringify(measurement),
        source: 'performance_budget',
        confidence: 1,
      });
    }

    return {
      summary: measurement
        ? `Completed in ${measurement.totalDurationMs}ms (${measurement.withinBudget ? 'within' : 'exceeded'} budget)`
        : 'No measurement available',
      reasoning,
      evidence,
      relatedRequirements: ['REQ-NFR-001'],
    };
  }

  // ============================================================================
  // Private Methods
  // ============================================================================

  /**
   * タイムアウトメッセージを生成
   */
  private formatTimeoutMessage(kind: TimeoutKind, step?: BudgetStep): string {
    switch (kind) {
      case 'z3_timeout':
        return `Z3 solver timed out after ${this.config.stepBudgetsMs.z3}ms`;
      case 'step_timeout':
        return `Step '${step}' timed out after ${this.config.stepBudgetsMs[step!]}ms`;
      case 'overall_timeout':
        return `Overall verification timed out after ${this.config.perFunctionBudgetMs}ms`;
      default:
        return 'Unknown timeout';
    }
  }
}

// ============================================================================
// Factory Functions
// ============================================================================

/**
 * PerformanceBudgetを作成
 */
export function createPerformanceBudget(config?: PerformanceBudgetConfig): PerformanceBudget {
  return new PerformanceBudget(config);
}

/**
 * 予算付き関数実行（簡易関数）
 */
export async function withBudget<T>(
  step: BudgetStep,
  fn: () => Promise<T>,
  budgetMs?: number,
): Promise<{ result: T | null; timedOut: boolean; durationMs: number }> {
  const budget = new PerformanceBudget(
    budgetMs ? { perFunctionBudgetMs: budgetMs, stepBudgetsMs: { [step]: budgetMs } } : {},
  );
  budget.start();

  const { result, timedOut, measurement } = await budget.executeWithBudget(step, fn);
  budget.end();

  return {
    result,
    timedOut,
    durationMs: measurement?.durationMs ?? 0,
  };
}
