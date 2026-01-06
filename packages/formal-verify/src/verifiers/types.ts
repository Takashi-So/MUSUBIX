/**
 * Verifier Types
 * 
 * 事前条件/事後条件検証の型定義
 */

/**
 * 変数の型宣言
 */
export type VariableType = 'Int' | 'Real' | 'Bool' | 'String' | 'Array' | 'BitVec';

/**
 * 変数宣言
 */
export interface VariableDeclaration {
  /** 変数名 */
  name: string;
  /** 変数の型 */
  type: VariableType;
  /** 配列の場合の要素型 */
  elementType?: VariableType;
  /** BitVecの場合のビット幅 */
  bitWidth?: number;
}

/**
 * 条件式
 */
export interface Condition {
  /** 条件式（自然言語またはSMT-LIB2） */
  expression: string;
  /** 条件式の形式 */
  format: 'natural' | 'smt' | 'javascript';
  /** 条件の説明（オプション） */
  description?: string;
}

/**
 * 検証オプション
 */
export interface VerificationOptions {
  /** タイムアウト（ミリ秒） */
  timeout?: number;
  /** 反例を生成するか */
  generateCounterexample?: boolean;
  /** 証明を生成するか */
  generateProof?: boolean;
  /** 詳細ログを出力するか */
  verbose?: boolean;
}

/**
 * 検証結果のステータス
 */
export type VerificationStatus = 'valid' | 'invalid' | 'unknown' | 'error';

/**
 * 反例
 */
export interface Counterexample {
  /** 変数の値の割り当て */
  assignments: Record<string, unknown>;
  /** 説明 */
  explanation?: string;
}

/**
 * 検証結果
 */
export interface VerificationResult {
  /** 検証ステータス */
  status: VerificationStatus;
  /** 検証対象の条件 */
  condition: Condition;
  /** 検証にかかった時間（ミリ秒） */
  duration: number;
  /** 反例（invalidの場合） */
  counterexample?: Counterexample;
  /** 証明（validの場合） */
  proof?: string;
  /** エラーメッセージ（errorの場合） */
  errorMessage?: string;
  /** 詳細情報 */
  details?: Record<string, unknown>;
}

/**
 * 事前条件検証入力
 */
export interface PreconditionInput {
  /** 検証対象の事前条件 */
  condition: Condition;
  /** 変数宣言 */
  variables: VariableDeclaration[];
  /** 追加のコンテキスト条件 */
  context?: Condition[];
  /** 検証オプション */
  options?: VerificationOptions;
}

/**
 * 事後条件検証入力
 */
export interface PostconditionInput {
  /** 事前条件 */
  precondition: Condition;
  /** 検証対象の事後条件 */
  postcondition: Condition;
  /** 変数宣言（事前状態） */
  preVariables: VariableDeclaration[];
  /** 変数宣言（事後状態） */
  postVariables: VariableDeclaration[];
  /** 遷移関係（事前→事後の変換） */
  transition?: string;
  /** 検証オプション */
  options?: VerificationOptions;
}
