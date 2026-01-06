/**
 * Z3 Adapter
 * 
 * Z3WasmClient と Z3ProcessFallback を統合するアダプタークラス
 * 自動フォールバック機能を提供
 */

import type { Z3Client, Z3Result, Z3Options } from './types.js';
import { Z3WasmClient } from './Z3WasmClient.js';
import { Z3ProcessFallback } from './Z3ProcessFallback.js';

/**
 * Z3Adapterオプション
 */
export interface Z3AdapterOptions extends Z3Options {
  /** WebAssemblyを優先するかどうか（デフォルト: true） */
  preferWasm?: boolean;
  /** フォールバックを有効にするか（デフォルト: true） */
  enableFallback?: boolean;
}

/**
 * Z3アダプター
 * 
 * Z3WasmClientとZ3ProcessFallbackを統合し、
 * 環境に応じて最適なクライアントを自動選択します。
 * 
 * @example
 * ```typescript
 * // ファクトリーメソッドで作成（推奨）
 * const z3 = await Z3Adapter.create();
 * const result = await z3.checkSat('(declare-const x Int) (assert (> x 0))');
 * 
 * // オプション指定
 * const z3 = await Z3Adapter.create({
 *   timeout: 10000,
 *   preferWasm: true,
 *   enableFallback: true,
 * });
 * ```
 */
export class Z3Adapter implements Z3Client {
  private primaryClient: Z3Client | null = null;
  private fallbackClient: Z3Client | null = null;
  private activeClient: Z3Client | null = null;
  private initialized = false;
  private readonly options: Z3AdapterOptions;

  constructor(options: Z3AdapterOptions = {}) {
    this.options = {
      timeout: options.timeout ?? 30000,
      logLevel: options.logLevel ?? 'silent',
      memoryLimit: options.memoryLimit ?? 512,
      preferWasm: options.preferWasm ?? true,
      enableFallback: options.enableFallback ?? true,
    };
  }

  /**
   * Z3Adapterのファクトリーメソッド
   * 
   * @param options - アダプターオプション
   * @returns 初期化済みのZ3Adapter
   * @throws {Error} Z3が利用できない場合
   */
  static async create(options: Z3AdapterOptions = {}): Promise<Z3Adapter> {
    const adapter = new Z3Adapter(options);
    await adapter.initialize();
    return adapter;
  }

  /**
   * Z3クライアントを初期化
   * 
   * preferWasm=trueの場合はWasmを優先し、失敗時にProcessFallbackを使用
   * preferWasm=falseの場合はProcessFallbackを優先
   */
  async initialize(): Promise<void> {
    if (this.initialized) {
      return;
    }

    const { preferWasm, enableFallback, logLevel } = this.options;

    if (preferWasm) {
      // Wasmを優先
      this.primaryClient = new Z3WasmClient(this.options);
      if (enableFallback) {
        this.fallbackClient = new Z3ProcessFallback(this.options);
      }
    } else {
      // Processを優先
      this.primaryClient = new Z3ProcessFallback(this.options);
      if (enableFallback) {
        this.fallbackClient = new Z3WasmClient(this.options);
      }
    }

    // プライマリクライアントの初期化を試行
    try {
      await this.primaryClient.initialize();
      if (this.primaryClient.isAvailable()) {
        this.activeClient = this.primaryClient;
        if (logLevel !== 'silent') {
          console.log(`[Z3Adapter] Using primary client: ${preferWasm ? 'Wasm' : 'Process'}`);
        }
      }
    } catch (error) {
      if (logLevel !== 'silent') {
        console.warn('[Z3Adapter] Primary client initialization failed:', error);
      }
    }

    // フォールバックを試行
    if (!this.activeClient && this.fallbackClient && enableFallback) {
      try {
        await this.fallbackClient.initialize();
        if (this.fallbackClient.isAvailable()) {
          this.activeClient = this.fallbackClient;
          if (logLevel !== 'silent') {
            console.log(`[Z3Adapter] Using fallback client: ${preferWasm ? 'Process' : 'Wasm'}`);
          }
        }
      } catch (error) {
        if (logLevel !== 'silent') {
          console.warn('[Z3Adapter] Fallback client initialization failed:', error);
        }
      }
    }

    this.initialized = true;

    if (!this.activeClient) {
      throw new Error(
        'Z3 is not available. Install z3-solver package (npm install z3-solver) ' +
        'or ensure Z3 is installed on your system and available in PATH.'
      );
    }
  }

  /**
   * SMT-LIB2形式のアサーションの充足可能性をチェック
   */
  async checkSat(smtLib2: string): Promise<Z3Result> {
    this.ensureInitialized();
    return this.activeClient!.checkSat(smtLib2);
  }

  /**
   * モデルを取得（sat の場合のみ有効）
   */
  async getModel(smtLib2: string): Promise<string | null> {
    this.ensureInitialized();
    return this.activeClient!.getModel(smtLib2);
  }

  /**
   * 証明を取得（unsat の場合のみ有効）
   */
  async getProof(smtLib2: string): Promise<string | null> {
    this.ensureInitialized();
    return this.activeClient!.getProof(smtLib2);
  }

  /**
   * リソースを解放
   */
  async dispose(): Promise<void> {
    if (this.primaryClient) {
      await this.primaryClient.dispose();
      this.primaryClient = null;
    }
    if (this.fallbackClient) {
      await this.fallbackClient.dispose();
      this.fallbackClient = null;
    }
    this.activeClient = null;
    this.initialized = false;
  }

  /**
   * クライアントが利用可能かどうか
   */
  isAvailable(): boolean {
    return this.activeClient?.isAvailable() ?? false;
  }

  /**
   * 現在使用中のクライアントタイプを取得
   */
  getActiveClientType(): 'wasm' | 'process' | null {
    if (!this.activeClient) return null;
    if (this.activeClient instanceof Z3WasmClient) return 'wasm';
    if (this.activeClient instanceof Z3ProcessFallback) return 'process';
    return null;
  }

  /**
   * バックエンドタイプを取得（getActiveClientTypeのエイリアス）
   */
  getBackendType(): 'wasm' | 'process' | 'none' {
    const type = this.getActiveClientType();
    return type ?? 'none';
  }

  /**
   * 初期化状態を確認
   */
  private ensureInitialized(): void {
    if (!this.initialized || !this.activeClient) {
      throw new Error('Z3Adapter not initialized. Use Z3Adapter.create() to create an instance.');
    }
  }
}
