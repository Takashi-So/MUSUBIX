/**
 * @nahisaho/musubix-expert-delegation
 * Retry Handler
 *
 * DES-DEL-004
 * Traces to: REQ-DEL-003, REQ-DEL-004
 */

import type { DelegationResult, ExpertType } from '../types/index.js';
import { DelegationError, type EscalationResult } from '../types/errors.js';

/**
 * リトライ設定
 */
export interface RetryConfig {
  /** 最大リトライ回数 */
  maxRetries: number;
  /** 初期遅延時間（ミリ秒） */
  initialDelayMs: number;
  /** 最大遅延時間（ミリ秒） */
  maxDelayMs: number;
  /** バックオフ係数 */
  backoffMultiplier: number;
  /** リトライ可能なエラーコード */
  retryableCodes: string[];
}

/**
 * エスカレーション設定
 */
export interface EscalationConfig {
  /** エスカレーション閾値（連続失敗回数） */
  threshold: number;
  /** エスカレーション先のエキスパートマッピング */
  escalationMap: Record<ExpertType, ExpertType | null>;
}

/**
 * デフォルトリトライ設定
 */
export const DEFAULT_RETRY_CONFIG: RetryConfig = {
  maxRetries: 3,
  initialDelayMs: 1000,
  maxDelayMs: 30000,
  backoffMultiplier: 2,
  retryableCodes: [
    'PROVIDER_UNAVAILABLE',
    'RATE_LIMITED',
    'TIMEOUT',
    'MODEL_UNAVAILABLE',
  ],
};

/**
 * デフォルトエスカレーション設定
 */
export const DEFAULT_ESCALATION_CONFIG: EscalationConfig = {
  threshold: 3,
  escalationMap: {
    architect: null, // 最上位、エスカレーション先なし
    'security-analyst': 'architect',
    'code-reviewer': 'architect',
    'plan-reviewer': 'architect',
    'ears-analyst': 'plan-reviewer',
    'formal-verifier': 'architect',
    'ontology-reasoner': 'architect',
  },
};

/**
 * Retry Handler
 *
 * 指数バックオフによるリトライと、
 * 連続失敗時のエスカレーションを管理する。
 */
export class RetryHandler {
  private readonly retryConfig: RetryConfig;
  private readonly escalationConfig: EscalationConfig;
  private failureCounts: Map<string, number> = new Map();

  constructor(
    retryConfig?: Partial<RetryConfig>,
    escalationConfig?: Partial<EscalationConfig>
  ) {
    this.retryConfig = { ...DEFAULT_RETRY_CONFIG, ...retryConfig };
    this.escalationConfig = { ...DEFAULT_ESCALATION_CONFIG, ...escalationConfig };
  }

  /**
   * リトライ付きで操作を実行
   */
  async executeWithRetry<T>(
    operation: () => Promise<T>,
    taskId: string
  ): Promise<T> {
    let lastError: Error | null = null;
    let attempt = 0;

    while (attempt <= this.retryConfig.maxRetries) {
      try {
        const result = await operation();
        // 成功したら失敗カウントをリセット
        this.resetFailureCount(taskId);
        return result;
      } catch (error) {
        lastError = error as Error;

        // リトライ可能かチェック
        if (!this.isRetryable(error)) {
          this.incrementFailureCount(taskId);
          throw error;
        }

        attempt++;

        if (attempt <= this.retryConfig.maxRetries) {
          const delay = this.calculateDelay(attempt);
          await this.sleep(delay);
        }
      }
    }

    // 最大リトライを超えた
    this.incrementFailureCount(taskId);
    throw DelegationError.fromCode('RETRY_EXHAUSTED', {
      attempts: attempt,
      lastError: lastError?.message,
    });
  }

  /**
   * エスカレーションが必要かチェック
   */
  shouldEscalate(taskId: string): boolean {
    const count = this.failureCounts.get(taskId) ?? 0;
    return count >= this.escalationConfig.threshold;
  }

  /**
   * エスカレーション先のエキスパートを取得
   */
  getEscalationTarget(currentExpert: ExpertType): EscalationResult {
    const escalateTo = this.escalationConfig.escalationMap[currentExpert];

    if (escalateTo === null) {
      return {
        shouldEscalate: false,
        reason: `${currentExpert} is the highest level expert`,
      };
    }

    if (escalateTo === undefined) {
      return {
        shouldEscalate: false,
        reason: `No escalation path defined for ${currentExpert}`,
      };
    }

    return {
      shouldEscalate: true,
      targetExpert: escalateTo,
      reason: `Escalating from ${currentExpert} to ${escalateTo}`,
    };
  }

  /**
   * 強制エスカレーションを実行
   */
  forceEscalation(
    currentExpert: ExpertType,
    result: DelegationResult
  ): DelegationResult {
    const escalation = this.getEscalationTarget(currentExpert);

    return {
      ...result,
      success: false,
      metadata: {
        ...result.metadata,
        escalated: escalation.shouldEscalate,
        escalationTarget: escalation.targetExpert,
        escalationReason: escalation.reason,
      },
    };
  }

  /**
   * 失敗カウントをリセット
   */
  resetFailureCount(taskId: string): void {
    this.failureCounts.delete(taskId);
  }

  /**
   * 現在の失敗カウントを取得
   */
  getFailureCount(taskId: string): number {
    return this.failureCounts.get(taskId) ?? 0;
  }

  /**
   * すべての失敗カウントをクリア
   */
  clearAllFailureCounts(): void {
    this.failureCounts.clear();
  }

  private isRetryable(error: unknown): boolean {
    if (error instanceof DelegationError) {
      return error.isRetryable();
    }

    // ネットワークエラーなどはリトライ可能とみなす
    if (error instanceof Error) {
      const message = error.message.toLowerCase();
      return (
        message.includes('timeout') ||
        message.includes('network') ||
        message.includes('unavailable') ||
        message.includes('rate limit')
      );
    }

    return false;
  }

  private calculateDelay(attempt: number): number {
    const delay =
      this.retryConfig.initialDelayMs *
      Math.pow(this.retryConfig.backoffMultiplier, attempt - 1);

    // ジッターを追加（±20%）
    const jitter = delay * 0.2 * (Math.random() * 2 - 1);

    return Math.min(delay + jitter, this.retryConfig.maxDelayMs);
  }

  private incrementFailureCount(taskId: string): void {
    const current = this.failureCounts.get(taskId) ?? 0;
    this.failureCounts.set(taskId, current + 1);
  }

  private sleep(ms: number): Promise<void> {
    return new Promise((resolve) => setTimeout(resolve, ms));
  }
}

/**
 * RetryHandlerのファクトリ関数
 */
export function createRetryHandler(
  retryConfig?: Partial<RetryConfig>,
  escalationConfig?: Partial<EscalationConfig>
): RetryHandler {
  return new RetryHandler(retryConfig, escalationConfig);
}
