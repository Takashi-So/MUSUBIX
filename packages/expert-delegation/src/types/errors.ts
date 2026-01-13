/**
 * @nahisaho/musubix-expert-delegation
 * Error Types
 *
 * DES-ERR-001
 * Traces to: REQ-NFR-001
 */

import type { ExpertType } from './index.js';

/**
 * 委任エラーの種類
 */
export type DelegationErrorCode =
  | 'EXPERT_NOT_FOUND' // エキスパートが見つからない
  | 'PROVIDER_UNAVAILABLE' // プロバイダーが利用不可
  | 'MODEL_NOT_AVAILABLE' // モデルが利用不可
  | 'TRIGGER_AMBIGUOUS' // トリガーが曖昧
  | 'PROMPT_TOO_LONG' // プロンプトが長すぎる
  | 'TIMEOUT' // タイムアウト
  | 'RATE_LIMITED' // レート制限
  | 'AUTHENTICATION_FAILED' // 認証失敗
  | 'RETRY_EXHAUSTED' // リトライ回数超過
  | 'INVALID_MODE' // 無効なモード
  | 'CONSTITUTION_VIOLATION'; // 憲法違反

/**
 * エラーコードごとのメッセージ
 */
const ERROR_MESSAGES: Record<DelegationErrorCode, string> = {
  EXPERT_NOT_FOUND: '指定されたエキスパートが見つかりません',
  PROVIDER_UNAVAILABLE: 'LLMプロバイダーが利用できません',
  MODEL_NOT_AVAILABLE: '指定されたモデルが利用できません',
  TRIGGER_AMBIGUOUS: 'トリガーが曖昧です。エキスパートを明示的に指定してください',
  PROMPT_TOO_LONG: 'プロンプトがモデルの制限を超えています',
  TIMEOUT: 'リクエストがタイムアウトしました',
  RATE_LIMITED: 'レート制限に達しました。しばらく待ってからリトライしてください',
  AUTHENTICATION_FAILED: 'GitHub Copilotの認証に失敗しました',
  RETRY_EXHAUSTED: 'リトライ回数の上限に達しました',
  INVALID_MODE: '無効な実行モードです',
  CONSTITUTION_VIOLATION: '憲法条項に違反する操作です',
};

/**
 * リトライ可能なエラーコード
 */
const RETRYABLE_CODES: DelegationErrorCode[] = [
  'PROVIDER_UNAVAILABLE',
  'MODEL_NOT_AVAILABLE',
  'TIMEOUT',
  'RATE_LIMITED',
];

/**
 * 委任エラー
 */
export class DelegationError extends Error {
  public readonly name = 'DelegationError';

  constructor(
    public readonly code: DelegationErrorCode,
    message: string,
    public readonly expert?: ExpertType,
    public readonly retryable: boolean = false,
    public readonly context?: Record<string, unknown>
  ) {
    super(message);

    // ES5互換のためのプロトタイプチェーン修正
    Object.setPrototypeOf(this, DelegationError.prototype);
  }

  /**
   * このエラーがリトライ可能か判定
   */
  isRetryable(): boolean {
    return this.retryable;
  }

  /**
   * リトライ可能なエラーか判定（静的メソッド）
   */
  static isRetryable(error: unknown): boolean {
    if (error instanceof DelegationError) {
      return error.retryable;
    }
    return false;
  }

  /**
   * エラーコードからエラーを生成
   */
  static fromCode(
    code: DelegationErrorCode,
    context?: Record<string, unknown>,
    expert?: ExpertType
  ): DelegationError {
    return new DelegationError(
      code,
      ERROR_MESSAGES[code],
      expert,
      RETRYABLE_CODES.includes(code),
      context
    );
  }

  /**
   * エラーをJSON形式で出力
   */
  toJSON(): Record<string, unknown> {
    return {
      name: this.name,
      code: this.code,
      message: this.message,
      expert: this.expert,
      retryable: this.retryable,
      context: this.context,
    };
  }
}

/**
 * エスカレーション結果
 */
export interface EscalationResult {
  shouldEscalate: boolean;
  targetExpert?: ExpertType;
  reason?: string;
}

/**
 * エラーコードの一覧を取得
 */
export function getAllErrorCodes(): DelegationErrorCode[] {
  return Object.keys(ERROR_MESSAGES) as DelegationErrorCode[];
}

/**
 * エラーメッセージを取得
 */
export function getErrorMessage(code: DelegationErrorCode): string {
  return ERROR_MESSAGES[code];
}
