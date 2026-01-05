/**
 * Pattern Sharing Types
 *
 * @module learning/sharing/types
 * @description Phase 2: Pattern Sharing 型定義
 * @requirements REQ-SHARE-001, REQ-SHARE-002, REQ-SHARE-003, REQ-SHARE-004, REQ-SHARE-005
 */

/**
 * エクスポートオプション
 * REQ-SHARE-001: パターンエクスポート
 */
export interface ExportOptions {
  /** 機密データを除去するか (REQ-SHARE-004) */
  sanitize: boolean;
  /** 出力フォーマット */
  format: 'json' | 'n3';
  /** 圧縮するか */
  compress?: boolean;
  /** バージョン情報を含めるか */
  includeVersion?: boolean;
  /** メタデータを含めるか */
  includeMetadata?: boolean;
}

/**
 * インポートオプション
 */
export interface ImportOptions {
  /** 検証をスキップするか */
  skipValidation?: boolean;
  /** 競合解決戦略 */
  conflictStrategy?: ConflictStrategy;
  /** マージ時に既存を上書きするか */
  overwrite?: boolean;
}

/**
 * エクスポート結果
 */
export interface ExportResult {
  /** エクスポートされたデータ */
  data: string;
  /** パターン数 */
  patternCount: number;
  /** データサイズ（バイト） */
  size: number;
  /** フォーマット */
  format: 'json' | 'n3';
  /** エクスポート日時 */
  exportedAt: string;
  /** バージョン */
  version: string;
  /** チェックサム */
  checksum: string;
}

/**
 * インポート結果
 * REQ-SHARE-002: パターンインポート
 */
export interface ImportResult {
  /** 成功したか */
  success: boolean;
  /** インポートされたパターン数 */
  importedCount: number;
  /** スキップされたパターン数 */
  skippedCount: number;
  /** 競合があったパターン数 */
  conflictCount: number;
  /** インポートされたパターン */
  patterns: SharedPattern[];
  /** エラーメッセージ */
  errors: string[];
  /** 警告メッセージ */
  warnings: string[];
}

/**
 * 検証結果
 * REQ-SHARE-003: オントロジー制約検証
 */
export interface ValidationResult {
  /** 有効か */
  valid: boolean;
  /** エラー一覧 */
  errors: ValidationError[];
  /** 警告一覧 */
  warnings: ValidationWarning[];
  /** 検証対象パターン数 */
  patternCount: number;
  /** 検証にかかった時間（ms） */
  validationTime: number;
}

/**
 * 検証エラー
 */
export interface ValidationError {
  /** エラーコード */
  code: string;
  /** エラーメッセージ */
  message: string;
  /** 関連するパターンID */
  patternId?: string;
  /** エラーの位置 */
  location?: string;
}

/**
 * 検証警告
 */
export interface ValidationWarning {
  /** 警告コード */
  code: string;
  /** 警告メッセージ */
  message: string;
  /** 関連するパターンID */
  patternId?: string;
  /** 推奨アクション */
  suggestion?: string;
}

/**
 * 共有パターン（シリアライズ形式）
 */
export interface SharedPattern {
  /** パターンID */
  id: string;
  /** パターン名 */
  name: string;
  /** カテゴリ */
  category: 'code' | 'design' | 'test' | 'architecture';
  /** 説明 */
  description: string;
  /** 信頼度 (0-1) */
  confidence: number;
  /** 使用回数 */
  usageCount: number;
  /** テンプレート */
  template?: string;
  /** コンテキスト */
  context?: PatternContext;
  /** メタデータ */
  metadata: PatternMetadata;
  /** 作成日時 */
  createdAt: string;
  /** 更新日時 */
  updatedAt: string;
  /** バージョン */
  version: number;
}

/**
 * パターンコンテキスト
 */
export interface PatternContext {
  /** 言語 */
  language?: string;
  /** フレームワーク */
  framework?: string;
  /** ドメイン */
  domain?: string;
  /** 適用条件 */
  applicableWhen?: string[];
  /** 前提条件 */
  prerequisites?: string[];
}

/**
 * パターンメタデータ
 */
export interface PatternMetadata {
  /** ソース（どこから学習したか） */
  source: 'local' | 'imported' | 'manual';
  /** インポート元 */
  importedFrom?: string;
  /** オリジナルID */
  originalId?: string;
  /** タグ */
  tags?: string[];
  /** 作者 */
  author?: string;
  /** ライセンス */
  license?: string;
}

/**
 * 競合情報
 * REQ-SHARE-005: 競合解決
 */
export interface Conflict {
  /** 競合タイプ */
  type: 'id' | 'name' | 'content' | 'version';
  /** ローカルパターン */
  localPattern: SharedPattern;
  /** リモートパターン */
  remotePattern: SharedPattern;
  /** 競合の詳細 */
  details: string;
}

/**
 * 競合解決戦略
 */
export type ConflictStrategy = 'keep-local' | 'keep-remote' | 'merge' | 'prompt' | 'skip';

/**
 * 競合解決結果
 */
export interface Resolution {
  /** 解決済み競合数 */
  resolvedCount: number;
  /** 解決されたパターン */
  resolvedPatterns: SharedPattern[];
  /** 手動解決が必要な競合 */
  pendingConflicts: Conflict[];
  /** 使用された戦略 */
  strategy: ConflictStrategy;
}

/**
 * サニタイズ設定
 * REQ-SHARE-004: 機密データ除去
 */
export interface SanitizeConfig {
  /** パスを除去するか */
  removePaths: boolean;
  /** 作者情報を除去するか */
  removeAuthor: boolean;
  /** カスタム正規表現パターン */
  customPatterns?: RegExp[];
  /** 除去するフィールド */
  removeFields?: string[];
}

/**
 * パターンリポジトリ情報
 */
export interface PatternRepository {
  /** リポジトリURL */
  url: string;
  /** リポジトリ名 */
  name: string;
  /** 認証が必要か */
  requiresAuth: boolean;
  /** 最終同期日時 */
  lastSyncedAt?: string;
  /** パターン数 */
  patternCount?: number;
}

/**
 * サーバー設定
 */
export interface ServerConfig {
  /** ポート */
  port: number;
  /** ホスト */
  host: string;
  /** 認証を有効にするか */
  enableAuth: boolean;
  /** CORS設定 */
  cors?: CorsConfig;
  /** レート制限 */
  rateLimit?: RateLimitConfig;
}

/**
 * CORS設定
 */
export interface CorsConfig {
  /** 許可するオリジン */
  allowedOrigins: string[];
  /** 許可するメソッド */
  allowedMethods: string[];
  /** 許可するヘッダー */
  allowedHeaders: string[];
}

/**
 * レート制限設定
 */
export interface RateLimitConfig {
  /** ウィンドウ時間（ms） */
  windowMs: number;
  /** 最大リクエスト数 */
  maxRequests: number;
}

/**
 * 認証トークン
 */
export interface AuthToken {
  /** トークン */
  token: string;
  /** 有効期限 */
  expiresAt: string;
  /** スコープ */
  scopes: AuthScope[];
  /** ユーザーID */
  userId?: string;
}

/**
 * 認証スコープ
 */
export type AuthScope = 'read' | 'write' | 'admin';

/**
 * 認証リクエスト
 */
export interface AuthRequest {
  /** ユーザー名またはAPIキー */
  credentials: string;
  /** シークレット */
  secret?: string;
  /** リクエストされたスコープ */
  scopes?: AuthScope[];
}

/**
 * 認証結果
 */
export interface AuthResult {
  /** 成功したか */
  success: boolean;
  /** トークン */
  token?: AuthToken;
  /** エラーメッセージ */
  error?: string;
}
