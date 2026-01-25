/**
 * Learning Hooks Types
 *
 * REQ-LH-001: Continuous Learning Evaluation
 * REQ-LH-002: Learned Skills Storage
 * REQ-LH-003: Pattern Ignore List
 *
 * @packageDocumentation
 */

/**
 * パターンタイプ
 * REQ-LH-001: 抽出対象パターンの分類
 */
export type PatternType =
  | 'error_resolution'
  | 'user_corrections'
  | 'workarounds'
  | 'debugging_techniques'
  | 'project_specific';

/**
 * 抽出されたパターン
 */
export interface ExtractedPattern {
  /** パターンID（自動生成） */
  readonly id: string;
  /** パターン名 */
  readonly name: string;
  /** 説明 */
  readonly description: string;
  /** パターンタイプ */
  readonly type: PatternType;
  /** 信頼度（0.0-1.0） */
  readonly confidence: number;
  /** 問題の説明 */
  readonly problem: string;
  /** 解決策 */
  readonly solution: string;
  /** コード例（任意） */
  readonly codeExample?: string;
  /** 適用条件 */
  readonly whenToUse: string[];
  /** 関連パターン */
  readonly relatedPatterns: string[];
  /** 抽出元セッションID */
  readonly sourceSessionId: string;
  /** 抽出日時 */
  readonly extractedAt: Date;
}

/**
 * パターン候補（抽出中の一時状態）
 */
export interface PatternCandidate {
  /** パターンタイプ */
  type: PatternType;
  /** 問題の説明 */
  problem: string;
  /** 解決策 */
  solution: string;
  /** 関連メッセージのインデックス */
  messageIndices: number[];
  /** 暫定信頼度 */
  tentativeConfidence: number;
  /** コード例 */
  codeExample?: string;
}

/**
 * 会話メッセージ（分析用）
 */
export interface ConversationMessage {
  /** メッセージインデックス */
  index: number;
  /** 送信者（user/assistant） */
  role: 'user' | 'assistant';
  /** メッセージ内容 */
  content: string;
  /** タイムスタンプ */
  timestamp: Date;
  /** エラーが含まれるか */
  containsError?: boolean;
  /** 修正指示が含まれるか */
  containsCorrection?: boolean;
  /** コードが含まれるか */
  containsCode?: boolean;
}

/**
 * 抽出設定
 */
export interface ExtractionConfig {
  /** パターン抽出の最小メッセージ数 */
  readonly minMessages: number;
  /** パターン抽出の最小セッション時間（分） */
  readonly minSessionMinutes: number;
  /** パターン保存の信頼度閾値 */
  readonly confidenceThreshold: number;
  /** セッション当たりの最大パターン数 */
  readonly maxPatternsPerSession: number;
  /** 自動抽出の有効/無効 */
  readonly enableAutoExtraction: boolean;
}

/**
 * デフォルト抽出設定
 * REQ-LH-001: 抽出条件の閾値
 */
export const DEFAULT_EXTRACTION_CONFIG: ExtractionConfig = {
  minMessages: 10,
  minSessionMinutes: 15,
  confidenceThreshold: 0.7,
  maxPatternsPerSession: 5,
  enableAutoExtraction: true,
};

/**
 * 除外パターン定義
 * REQ-LH-003: Pattern Ignore List
 */
export interface IgnorePattern {
  /** 除外カテゴリ */
  readonly category:
    | 'typo'
    | 'temporary'
    | 'external_api'
    | 'environment_specific'
    | 'security';
  /** 検出用正規表現 */
  readonly pattern: RegExp;
  /** 説明 */
  readonly reason: string;
}

/**
 * デフォルト除外パターン
 * REQ-LH-003: 除外対象のパターン定義
 */
export const DEFAULT_IGNORE_PATTERNS: readonly IgnorePattern[] = [
  // タイポ修正
  {
    category: 'typo',
    pattern: /typo|spelling|misspell/i,
    reason: '単純なタイポ修正は汎用性がない',
  },
  {
    category: 'typo',
    pattern: /\b(funtion|fucntion|funciton)\b/i,
    reason: 'function のタイポ',
  },

  // 一時的な問題
  {
    category: 'temporary',
    pattern: /timeout|ETIMEDOUT|ECONNRESET|connection refused/i,
    reason: '一時的なネットワークエラー',
  },
  {
    category: 'temporary',
    pattern: /socket hang up|ECONNREFUSED/i,
    reason: '一時的な接続エラー',
  },

  // 外部API障害
  {
    category: 'external_api',
    pattern: /rate limit|429|too many requests/i,
    reason: 'レートリミット（一時的）',
  },
  {
    category: 'external_api',
    pattern: /service unavailable|503|502 bad gateway/i,
    reason: '外部サービス障害',
  },

  // 環境固有の問題
  {
    category: 'environment_specific',
    pattern: /ENOENT.*\/home\/|ENOENT.*C:\\Users\\/i,
    reason: '環境固有のパス問題',
  },
  {
    category: 'environment_specific',
    pattern: /permission denied.*\/usr\/local/i,
    reason: '環境固有の権限問題',
  },

  // セキュリティ関連
  {
    category: 'security',
    pattern: /api[_-]?key|password|secret|token|credential/i,
    reason: '機密情報漏洩リスク',
  },
  {
    category: 'security',
    pattern: /private[_-]?key|oauth|bearer/i,
    reason: '認証情報漏洩リスク',
  },
] as const;

/**
 * 抽出結果
 */
export interface ExtractionResult {
  /** セッションID */
  readonly sessionId: string;
  /** 抽出されたパターン */
  readonly extractedPatterns: ExtractedPattern[];
  /** スキップされたパターン（除外理由付き） */
  readonly skippedPatterns: Array<{
    candidate: PatternCandidate;
    reason: string;
  }>;
  /** メッセージ数 */
  readonly messageCount: number;
  /** セッション時間（分） */
  readonly sessionMinutes: number;
  /** 抽出日時 */
  readonly extractedAt: Date;
}

/**
 * 学習レポート
 */
export interface LearningReport {
  /** セッションID */
  readonly sessionId: string;
  /** メッセージ数 */
  readonly messageCount: number;
  /** セッション時間（人間可読形式） */
  readonly sessionDuration: string;
  /** 抽出されたパターン（サマリー） */
  readonly extractedPatterns: Array<{
    name: string;
    type: PatternType;
    confidence: number;
    summary: string;
  }>;
  /** スキップされたパターン数（カテゴリ別） */
  readonly skippedCounts: Record<string, number>;
  /** 生成日時 */
  readonly generatedAt: Date;
}

/**
 * Learning Hooks Manager インターフェース
 */
export interface LearningHooksManager {
  /**
   * パターン抽出条件をチェック
   * @param messageCount メッセージ数
   * @param sessionMinutes セッション時間（分）
   * @returns 抽出を実行すべきか
   */
  shouldExtract(messageCount: number, sessionMinutes: number): boolean;

  /**
   * 会話からパターンを抽出
   * @param messages 会話メッセージ
   * @param sessionId セッションID
   * @returns 抽出結果
   */
  extractPatterns(
    messages: ConversationMessage[],
    sessionId: string
  ): ExtractionResult;

  /**
   * パターン候補が除外対象かチェック
   * @param candidate パターン候補
   * @returns 除外すべきか、除外理由
   */
  shouldIgnore(candidate: PatternCandidate): { ignore: boolean; reason?: string };

  /**
   * パターンをスキルファイルとして保存
   * @param pattern 保存するパターン
   * @returns 保存先パス
   */
  saveAsSkill(pattern: ExtractedPattern): string;

  /**
   * 学習レポートを生成
   * @param result 抽出結果
   * @returns 学習レポート
   */
  generateReport(result: ExtractionResult): LearningReport;

  /**
   * 学習レポートをMarkdown形式でフォーマット
   * @param report 学習レポート
   * @returns Markdown文字列
   */
  formatReportAsMarkdown(report: LearningReport): string;

  /**
   * 設定を取得
   */
  getConfig(): ExtractionConfig;

  /**
   * 除外パターンを取得
   */
  getIgnorePatterns(): readonly IgnorePattern[];

  /**
   * カスタム除外パターンを追加
   * @param pattern 追加する除外パターン
   */
  addIgnorePattern(pattern: IgnorePattern): void;
}

/**
 * エラー解決フローの検出結果
 */
export interface ErrorResolutionFlow {
  /** エラーメッセージのインデックス */
  errorMessageIndex: number;
  /** 修正アクションのインデックス */
  fixActionIndex: number;
  /** 解消確認のインデックス（任意） */
  resolutionIndex?: number;
  /** エラー内容 */
  errorContent: string;
  /** 修正内容 */
  fixContent: string;
}

/**
 * ユーザー修正の検出結果
 */
export interface UserCorrectionFlow {
  /** AI提案のインデックス */
  aiProposalIndex: number;
  /** ユーザー修正指示のインデックス */
  userCorrectionIndex: number;
  /** 承認のインデックス（任意） */
  approvalIndex?: number;
  /** 元の提案 */
  originalProposal: string;
  /** 修正内容 */
  correctionContent: string;
}

/**
 * パターン分析結果
 */
export interface PatternAnalysisResult {
  /** 検出されたエラー解決フロー */
  errorResolutionFlows: ErrorResolutionFlow[];
  /** 検出されたユーザー修正フロー */
  userCorrectionFlows: UserCorrectionFlow[];
  /** 検出されたデバッグ技法 */
  debuggingTechniques: string[];
  /** プロジェクト固有パターン候補 */
  projectSpecificCandidates: string[];
}
