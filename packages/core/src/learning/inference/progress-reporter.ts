/**
 * Progress Reporter
 *
 * @module learning/inference/progress-reporter
 * @description 推論進捗レポーター
 * @requirements REQ-ONTO-012
 */

import type { InferenceProgress, IProgressReporter, ProgressCallback } from './types.js';

/**
 * 進捗フェーズ
 */
export type ProgressPhase =
  | 'initializing'
  | 'loading'
  | 'reasoning'
  | 'explaining'
  | 'completed'
  | 'error';

/**
 * 進捗レポートオプション
 */
export interface ProgressReporterOptions {
  /** レポート間隔（ミリ秒）デフォルト: 500ms */
  interval?: number;
  /** 最小レポート間隔（ミリ秒）デフォルト: 100ms */
  minInterval?: number;
  /** 自動レポートを有効にするか */
  autoReport?: boolean;
  /** 詳細ログを出力するか */
  verbose?: boolean;
}

/**
 * 推論進捗レポーター
 * REQ-ONTO-012: 推論進捗フィードバック（500ms間隔）
 */
export class ProgressReporter implements IProgressReporter {
  private callbacks: ProgressCallback[] = [];
  private currentProgress: InferenceProgress;
  private lastReportTime = 0;
  private startTime = 0;
  private options: Required<ProgressReporterOptions>;
  private timer: ReturnType<typeof setInterval> | null = null;
  private isRunning = false;

  constructor(options: ProgressReporterOptions = {}) {
    this.options = {
      interval: options.interval ?? 500,
      minInterval: options.minInterval ?? 100,
      autoReport: options.autoReport ?? true,
      verbose: options.verbose ?? false,
    };

    this.currentProgress = this.createInitialProgress();
  }

  /**
   * 初期進捗状態を作成
   */
  private createInitialProgress(): InferenceProgress {
    return {
      phase: 'initializing',
      totalTriples: 0,
      processedTriples: 0,
      inferredTriples: 0,
      elapsedMs: 0,
      estimatedRemainingMs: 0,
    };
  }

  /**
   * 進捗コールバックを登録
   */
  onProgress(callback: ProgressCallback): () => void {
    this.callbacks.push(callback);
    return () => {
      const index = this.callbacks.indexOf(callback);
      if (index !== -1) {
        this.callbacks.splice(index, 1);
      }
    };
  }

  /**
   * 進捗レポートを開始
   */
  start(totalTriples: number): void {
    this.startTime = Date.now();
    this.lastReportTime = this.startTime;
    this.isRunning = true;

    this.currentProgress = {
      ...this.createInitialProgress(),
      phase: 'loading',
      totalTriples,
    };

    if (this.options.autoReport && this.options.interval > 0) {
      this.timer = setInterval(() => {
        this.autoReportProgress();
      }, this.options.interval);
    }

    this.report();

    if (this.options.verbose) {
      console.log(`[ProgressReporter] Started with ${totalTriples} triples`);
    }
  }

  /**
   * 進捗を更新
   */
  update(partial: Partial<InferenceProgress>): void {
    const now = Date.now();
    const elapsedMs = now - this.startTime;

    this.currentProgress = {
      ...this.currentProgress,
      ...partial,
      elapsedMs,
      estimatedRemainingMs: this.estimateRemainingTime(elapsedMs),
    };

    // 最小間隔を超えていれば報告
    if (now - this.lastReportTime >= this.options.minInterval) {
      this.report();
    }
  }

  /**
   * フェーズを更新
   */
  setPhase(phase: ProgressPhase): void {
    this.update({ phase });

    if (this.options.verbose) {
      console.log(`[ProgressReporter] Phase: ${phase}`);
    }
  }

  /**
   * 処理済みトリプル数を加算
   */
  incrementProcessed(count: number = 1): void {
    this.update({
      processedTriples: this.currentProgress.processedTriples + count,
    });
  }

  /**
   * 推論済みトリプル数を加算
   */
  incrementInferred(count: number = 1): void {
    this.update({
      inferredTriples: this.currentProgress.inferredTriples + count,
    });
  }

  /**
   * 進捗レポートを完了
   */
  complete(inferredTriples: number): void {
    this.isRunning = false;

    if (this.timer) {
      clearInterval(this.timer);
      this.timer = null;
    }

    this.update({
      phase: 'completed',
      processedTriples: this.currentProgress.totalTriples,
      inferredTriples,
      estimatedRemainingMs: 0,
    });

    if (this.options.verbose) {
      console.log(
        `[ProgressReporter] Completed: ${inferredTriples} triples inferred in ${this.currentProgress.elapsedMs}ms`
      );
    }
  }

  /**
   * エラーを報告
   */
  error(message: string): void {
    this.isRunning = false;

    if (this.timer) {
      clearInterval(this.timer);
      this.timer = null;
    }

    this.update({
      phase: 'error',
      message,
    });

    if (this.options.verbose) {
      console.error(`[ProgressReporter] Error: ${message}`);
    }
  }

  /**
   * 残り時間を推定
   */
  private estimateRemainingTime(elapsedMs: number): number {
    const { processedTriples, totalTriples } = this.currentProgress;

    if (processedTriples === 0 || totalTriples === 0) {
      return 0;
    }

    const progressRatio = processedTriples / totalTriples;
    if (progressRatio >= 1) {
      return 0;
    }

    const estimatedTotalMs = elapsedMs / progressRatio;
    return Math.max(0, estimatedTotalMs - elapsedMs);
  }

  /**
   * コールバックに進捗を報告
   */
  report(): void {
    this.lastReportTime = Date.now();

    for (const callback of this.callbacks) {
      try {
        callback(this.currentProgress);
      } catch (error) {
        if (this.options.verbose) {
          console.error('[ProgressReporter] Callback error:', error);
        }
      }
    }
  }

  /**
   * 自動進捗レポート
   */
  private autoReportProgress(): void {
    if (!this.isRunning) {
      return;
    }

    // 経過時間を更新
    this.currentProgress.elapsedMs = Date.now() - this.startTime;
    this.currentProgress.estimatedRemainingMs = this.estimateRemainingTime(
      this.currentProgress.elapsedMs
    );

    this.report();
  }

  /**
   * 現在の進捗を取得
   */
  getProgress(): InferenceProgress {
    return { ...this.currentProgress };
  }

  /**
   * 進捗をフォーマット
   */
  formatProgress(progress?: InferenceProgress): string {
    const p = progress || this.currentProgress;

    const percent =
      p.totalTriples > 0 ? Math.round((p.processedTriples / p.totalTriples) * 100) : 0;

    const phaseLabels: Record<ProgressPhase, string> = {
      initializing: '初期化中',
      loading: '読み込み中',
      reasoning: '推論中',
      explaining: '説明生成中',
      completed: '完了',
      error: 'エラー',
    };

    const parts: string[] = [
      `[${phaseLabels[p.phase as ProgressPhase] || p.phase}]`,
      `${percent}%`,
      `(${p.processedTriples}/${p.totalTriples})`,
      `推論: ${p.inferredTriples}件`,
      `経過: ${this.formatTime(p.elapsedMs)}`,
    ];

    if (p.estimatedRemainingMs > 0 && p.phase !== 'completed') {
      parts.push(`残り: ${this.formatTime(p.estimatedRemainingMs)}`);
    }

    if (p.message) {
      parts.push(`- ${p.message}`);
    }

    return parts.join(' ');
  }

  /**
   * 時間をフォーマット
   */
  private formatTime(ms: number): string {
    if (ms < 1000) {
      return `${Math.round(ms)}ms`;
    }

    const seconds = Math.round(ms / 1000);
    if (seconds < 60) {
      return `${seconds}秒`;
    }

    const minutes = Math.floor(seconds / 60);
    const remainingSeconds = seconds % 60;
    return `${minutes}分${remainingSeconds}秒`;
  }

  /**
   * 進捗バーを生成
   */
  formatProgressBar(width: number = 40): string {
    const p = this.currentProgress;
    const percent =
      p.totalTriples > 0 ? Math.round((p.processedTriples / p.totalTriples) * 100) : 0;

    const filledWidth = Math.round((percent / 100) * width);
    const emptyWidth = width - filledWidth;

    const filled = '█'.repeat(filledWidth);
    const empty = '░'.repeat(emptyWidth);

    return `[${filled}${empty}] ${percent}%`;
  }

  /**
   * JSONサマリーを生成
   */
  toJSON(): InferenceProgress {
    return this.getProgress();
  }

  /**
   * リソースを解放
   */
  dispose(): void {
    if (this.timer) {
      clearInterval(this.timer);
      this.timer = null;
    }

    this.callbacks = [];
    this.isRunning = false;
  }

  /**
   * リセット
   */
  reset(): void {
    this.dispose();
    this.currentProgress = this.createInitialProgress();
    this.lastReportTime = 0;
    this.startTime = 0;
  }
}

/**
 * コンソール進捗レポーター
 * コンソールに進捗を出力するシンプルなレポーター
 */
export class ConsoleProgressReporter extends ProgressReporter {
  constructor(options: ProgressReporterOptions = {}) {
    super({
      ...options,
      verbose: false, // 重複出力を避ける
    });

    this.onProgress((progress) => {
      // プログレスバー付きで出力
      process.stdout.write(`\r${this.formatProgressBar(30)} ${this.formatProgress(progress)}`);

      if (progress.phase === 'completed' || progress.phase === 'error') {
        process.stdout.write('\n');
      }
    });
  }
}

/**
 * サイレント進捗レポーター
 * コールバックのみを使用し、出力を行わないレポーター
 */
export class SilentProgressReporter extends ProgressReporter {
  constructor() {
    super({
      autoReport: false,
      verbose: false,
    });
  }
}
