/**
 * Z3 Client Interface and Types
 * 
 * Z3ソルバーとの通信インターフェース定義
 */

/**
 * Z3ソルバーの結果
 */
export type Z3Result = 'sat' | 'unsat' | 'unknown' | 'error';

/**
 * Z3クライアントオプション
 */
export interface Z3Options {
  /** タイムアウト（ミリ秒） */
  timeout?: number;
  /** ログレベル */
  logLevel?: 'debug' | 'info' | 'warn' | 'error' | 'silent';
  /** メモリ制限（MB） */
  memoryLimit?: number;
}

/**
 * Z3クライアントインターフェース
 * 
 * Z3WasmClientとZ3ProcessFallbackが実装
 */
export interface Z3Client {
  /**
   * Z3ソルバーを初期化
   */
  initialize(): Promise<void>;

  /**
   * SMT-LIB2形式のアサーションの充足可能性をチェック
   * @param smtLib2 - SMT-LIB2形式の文字列
   * @returns 充足可能性の結果
   */
  checkSat(smtLib2: string): Promise<Z3Result>;

  /**
   * モデルを取得（sat の場合のみ有効）
   * @param smtLib2 - SMT-LIB2形式の文字列
   * @returns モデルの文字列表現、またはnull
   */
  getModel(smtLib2: string): Promise<string | null>;

  /**
   * 証明を取得（unsat の場合のみ有効）
   * @param smtLib2 - SMT-LIB2形式の文字列
   * @returns 証明の文字列表現、またはnull
   */
  getProof(smtLib2: string): Promise<string | null>;

  /**
   * リソースを解放
   */
  dispose(): Promise<void>;

  /**
   * クライアントが利用可能かどうか
   */
  isAvailable(): boolean;
}

/**
 * Z3検証コンテキスト
 */
export interface Z3Context {
  /** 宣言された変数 */
  declarations: Map<string, string>;
  /** アサーション */
  assertions: string[];
  /** オプション */
  options: Z3Options;
}

/**
 * Z3エラー情報
 */
export interface Z3Error {
  /** エラーコード */
  code: string;
  /** エラーメッセージ */
  message: string;
  /** 発生位置（行番号） */
  line?: number;
  /** 発生位置（列番号） */
  column?: number;
}
