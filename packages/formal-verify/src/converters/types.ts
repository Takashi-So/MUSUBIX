/**
 * Converter Types
 * 
 * EARS→SMT変換の型定義
 */

/**
 * EARSパターンタイプ
 */
export type EarsPatternType = 
  | 'ubiquitous'    // THE [system] SHALL [requirement]
  | 'event-driven'  // WHEN [event], THE [system] SHALL [response]
  | 'state-driven'  // WHILE [state], THE [system] SHALL [response]
  | 'unwanted'      // THE [system] SHALL NOT [behavior]
  | 'optional';     // IF [condition], THEN THE [system] SHALL [response]

/**
 * EARSパターン解析結果
 */
export interface EarsPattern {
  /** パターンタイプ */
  type: EarsPatternType;
  /** 原文 */
  original: string;
  /** システム名 */
  system: string;
  /** 要件/応答 */
  requirement: string;
  /** イベント（event-drivenの場合） */
  event?: string;
  /** 状態（state-drivenの場合） */
  state?: string;
  /** 条件（optionalの場合） */
  condition?: string;
  /** 否定フラグ（unwantedの場合） */
  negated?: boolean;
}

/**
 * SMT論理式
 */
export interface SmtFormula {
  /** SMT-LIB2形式の文字列 */
  smtLib2: string;
  /** 変数宣言 */
  declarations: SmtDeclaration[];
  /** アサーション */
  assertions: string[];
  /** メタデータ */
  metadata: {
    /** 元のEARSパターン */
    earsPattern: EarsPattern;
    /** 変換に使用したルール */
    transformationRules: string[];
    /** 警告 */
    warnings: string[];
  };
}

/**
 * SMT変数宣言
 */
export interface SmtDeclaration {
  /** 変数名 */
  name: string;
  /** SMT型 */
  type: string;
  /** 説明 */
  description?: string;
}

/**
 * 変換結果
 */
export interface ConversionResult {
  /** 成功フラグ */
  success: boolean;
  /** SMT論理式（成功時） */
  formula?: SmtFormula;
  /** エラーメッセージ（失敗時） */
  error?: string;
  /** 警告メッセージ */
  warnings: string[];
  /** 変換時間（ミリ秒） */
  duration: number;
}

/**
 * 変換オプション
 */
export interface ConversionOptions {
  /** 厳密モード（警告をエラーとして扱う） */
  strict?: boolean;
  /** 変数の型推論を有効にする */
  inferTypes?: boolean;
  /** カスタム変数型マッピング */
  typeMapping?: Record<string, string>;
  /** デバッグ出力 */
  debug?: boolean;
}

/**
 * 変換ルール
 */
export interface TransformationRule {
  /** ルール名 */
  name: string;
  /** 適用対象のパターンタイプ */
  patternTypes: EarsPatternType[];
  /** 変換関数 */
  transform: (pattern: EarsPattern) => string;
  /** 優先度（高いほど先に適用） */
  priority: number;
}
