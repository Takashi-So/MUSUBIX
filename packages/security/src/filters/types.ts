/**
 * Sensitive Data Filter Types
 *
 * REQ-INT-004: SensitiveDataFilter - 機密情報のフィルタリング
 *
 * @packageDocumentation
 */

/**
 * 機密データの種類
 */
export type SensitiveDataType =
  | 'api_key'
  | 'password'
  | 'secret'
  | 'aws_key'
  | 'private_key'
  | 'oauth_token'
  | 'bearer_token'
  | 'jwt'
  | 'connection_string'
  | 'ssh_key'
  | 'pgp_key'
  | 'certificate'
  | 'credit_card'
  | 'ssn'
  | 'email'
  | 'phone'
  | 'ip_address'
  | 'custom';

/**
 * 機密データパターン定義
 */
export interface SensitiveDataPattern {
  /** パターン種別 */
  readonly type: SensitiveDataType;
  /** 検出用正規表現 */
  readonly pattern: RegExp;
  /** 説明 */
  readonly description: string;
  /** 重要度（high: 即座にマスク, medium: 警告付きマスク, low: オプションでマスク） */
  readonly severity: 'high' | 'medium' | 'low';
  /** マスク時の置換文字列 */
  readonly replacement: string;
}

/**
 * フィルタリング結果
 */
export interface FilterResult {
  /** フィルタリング後のテキスト */
  readonly filtered: string;
  /** 検出された機密データ */
  readonly detections: SensitiveDataDetection[];
  /** 元のテキストが変更されたか */
  readonly wasModified: boolean;
  /** フィルタリング統計 */
  readonly stats: FilterStats;
}

/**
 * 機密データ検出結果
 */
export interface SensitiveDataDetection {
  /** 検出された種類 */
  readonly type: SensitiveDataType;
  /** 検出位置（開始） */
  readonly startIndex: number;
  /** 検出位置（終了） */
  readonly endIndex: number;
  /** マスク後の文字列 */
  readonly masked: string;
  /** 重要度 */
  readonly severity: 'high' | 'medium' | 'low';
  /** パターン説明 */
  readonly description: string;
}

/**
 * フィルタリング統計
 */
export interface FilterStats {
  /** 検出された機密データの総数 */
  readonly totalDetections: number;
  /** 種類別の検出数 */
  readonly byType: Record<SensitiveDataType, number>;
  /** 重要度別の検出数 */
  readonly bySeverity: Record<'high' | 'medium' | 'low', number>;
  /** 処理時間（ミリ秒） */
  readonly processingTimeMs: number;
}

/**
 * フィルター設定
 */
export interface FilterConfig {
  /** 有効なパターン種別 */
  readonly enabledTypes: readonly SensitiveDataType[];
  /** 最小重要度（これ以上のみフィルタリング） */
  readonly minSeverity: 'high' | 'medium' | 'low';
  /** カスタムパターン */
  readonly customPatterns: readonly SensitiveDataPattern[];
  /** マスク文字 */
  readonly maskChar: string;
  /** マスク長（固定長の場合） */
  readonly maskLength?: number;
  /** 元の長さを保持するか */
  readonly preserveLength: boolean;
}

/**
 * デフォルト機密データパターン
 */
export const DEFAULT_SENSITIVE_PATTERNS: readonly SensitiveDataPattern[] = [
  // API Keys
  {
    type: 'api_key',
    pattern: /(?:api[_-]?key|apikey)[=:\s]+["']?([a-zA-Z0-9_\-]{20,})["']?/gi,
    description: 'API Key',
    severity: 'high',
    replacement: '[API_KEY_REDACTED]',
  },
  {
    type: 'api_key',
    pattern: /(?:x-api-key|authorization)[=:\s]+["']?([a-zA-Z0-9_\-]{20,})["']?/gi,
    description: 'API Key Header',
    severity: 'high',
    replacement: '[API_KEY_REDACTED]',
  },

  // Passwords
  {
    type: 'password',
    pattern: /(?:password|passwd|pwd)[=:\s]+["']?([^\s"']{4,})["']?/gi,
    description: 'Password',
    severity: 'high',
    replacement: '[PASSWORD_REDACTED]',
  },

  // Secrets
  {
    type: 'secret',
    pattern: /(?:secret|client[_-]?secret)[=:\s]+["']?([a-zA-Z0-9_\-]{16,})["']?/gi,
    description: 'Secret Key',
    severity: 'high',
    replacement: '[SECRET_REDACTED]',
  },

  // AWS Keys
  {
    type: 'aws_key',
    pattern: /(?:AKIA|ABIA|ACCA|ASIA)[A-Z0-9]{16}/g,
    description: 'AWS Access Key ID',
    severity: 'high',
    replacement: '[AWS_KEY_REDACTED]',
  },
  {
    type: 'aws_key',
    pattern: /(?:aws[_-]?secret[_-]?access[_-]?key)[=:\s]+["']?([a-zA-Z0-9/+=]{40})["']?/gi,
    description: 'AWS Secret Access Key',
    severity: 'high',
    replacement: '[AWS_SECRET_REDACTED]',
  },

  // Private Keys
  {
    type: 'private_key',
    pattern: /-----BEGIN (?:RSA |EC |DSA |OPENSSH )?PRIVATE KEY-----[\s\S]*?-----END (?:RSA |EC |DSA |OPENSSH )?PRIVATE KEY-----/g,
    description: 'Private Key',
    severity: 'high',
    replacement: '[PRIVATE_KEY_REDACTED]',
  },

  // OAuth/Bearer Tokens
  {
    type: 'oauth_token',
    pattern: /(?:oauth[_-]?token|access[_-]?token)[=:\s]+["']?([a-zA-Z0-9_\-.]{20,})["']?/gi,
    description: 'OAuth Token',
    severity: 'high',
    replacement: '[OAUTH_TOKEN_REDACTED]',
  },
  {
    type: 'bearer_token',
    pattern: /Bearer\s+([a-zA-Z0-9_\-.]{20,})/gi,
    description: 'Bearer Token',
    severity: 'high',
    replacement: 'Bearer [TOKEN_REDACTED]',
  },

  // JWT
  {
    type: 'jwt',
    pattern: /eyJ[a-zA-Z0-9_-]*\.eyJ[a-zA-Z0-9_-]*\.[a-zA-Z0-9_-]*/g,
    description: 'JSON Web Token',
    severity: 'high',
    replacement: '[JWT_REDACTED]',
  },

  // Connection Strings
  {
    type: 'connection_string',
    pattern: /(?:mongodb|mysql|postgres|redis|amqp):\/\/[^\s"']+:[^\s"']+@[^\s"']+/gi,
    description: 'Database Connection String',
    severity: 'high',
    replacement: '[CONNECTION_STRING_REDACTED]',
  },

  // SSH Keys
  {
    type: 'ssh_key',
    pattern: /ssh-(?:rsa|dss|ed25519|ecdsa)\s+[A-Za-z0-9+/=]{100,}/g,
    description: 'SSH Public Key',
    severity: 'medium',
    replacement: '[SSH_KEY_REDACTED]',
  },

  // Credit Card Numbers
  {
    type: 'credit_card',
    pattern: /\b(?:4[0-9]{12}(?:[0-9]{3})?|5[1-5][0-9]{14}|3[47][0-9]{13}|6(?:011|5[0-9]{2})[0-9]{12})\b/g,
    description: 'Credit Card Number',
    severity: 'high',
    replacement: '[CREDIT_CARD_REDACTED]',
  },

  // Email (medium severity - context dependent)
  {
    type: 'email',
    pattern: /\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b/g,
    description: 'Email Address',
    severity: 'medium',
    replacement: '[EMAIL_REDACTED]',
  },

  // IP Addresses (low severity)
  {
    type: 'ip_address',
    pattern: /\b(?:(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.){3}(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\b/g,
    description: 'IPv4 Address',
    severity: 'low',
    replacement: '[IP_REDACTED]',
  },
] as const;

/**
 * デフォルトフィルター設定
 */
export const DEFAULT_FILTER_CONFIG: FilterConfig = {
  enabledTypes: [
    'api_key',
    'password',
    'secret',
    'aws_key',
    'private_key',
    'oauth_token',
    'bearer_token',
    'jwt',
    'connection_string',
    'ssh_key',
    'credit_card',
  ],
  minSeverity: 'medium',
  customPatterns: [],
  maskChar: '*',
  preserveLength: false,
};

/**
 * SensitiveDataFilter インターフェース
 */
export interface SensitiveDataFilter {
  /**
   * テキストから機密データをフィルタリング
   * @param text フィルタリング対象のテキスト
   * @returns フィルタリング結果
   */
  filter(text: string): FilterResult;

  /**
   * テキストに機密データが含まれるかチェック
   * @param text チェック対象のテキスト
   * @returns 機密データが含まれる場合 true
   */
  containsSensitiveData(text: string): boolean;

  /**
   * 機密データを検出（マスクせず）
   * @param text 検出対象のテキスト
   * @returns 検出結果の配列
   */
  detect(text: string): SensitiveDataDetection[];

  /**
   * 設定を取得
   */
  getConfig(): FilterConfig;

  /**
   * カスタムパターンを追加
   * @param pattern 追加するパターン
   */
  addPattern(pattern: SensitiveDataPattern): void;

  /**
   * 全パターンを取得
   */
  getPatterns(): readonly SensitiveDataPattern[];
}
