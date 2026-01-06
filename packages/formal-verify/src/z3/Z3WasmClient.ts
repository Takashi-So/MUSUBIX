/**
 * Z3 WebAssembly Client
 * 
 * z3-wasmを使用したブラウザ/Node.js両対応のZ3クライアント
 * 
 * @implements {Z3Client}
 */

import type { Z3Client, Z3Result, Z3Options } from './types.js';

/**
 * Z3 WebAssemblyクライアント
 * 
 * z3-wasmパッケージを使用してZ3ソルバーをWebAssemblyで実行します。
 * ネイティブZ3が利用できない環境でのフォールバックとして機能します。
 * 
 * @example
 * ```typescript
 * const client = new Z3WasmClient({ timeout: 5000 });
 * await client.initialize();
 * const result = await client.checkSat('(declare-const x Int) (assert (> x 0))');
 * console.log(result); // 'sat'
 * ```
 */
export class Z3WasmClient implements Z3Client {
  private z3Instance: unknown = null;
  private initialized = false;
  private readonly options: Z3Options;

  constructor(options: Z3Options = {}) {
    this.options = {
      timeout: options.timeout ?? 30000,
      logLevel: options.logLevel ?? 'silent',
      memoryLimit: options.memoryLimit ?? 512,
    };
  }

  /**
   * Z3 WebAssemblyモジュールを初期化
   * 
   * @throws {Error} z3-wasmモジュールのロードに失敗した場合
   */
  async initialize(): Promise<void> {
    if (this.initialized) {
      return;
    }

    try {
      // z3-wasmの動的インポート
      // Note: z3-wasmがインストールされていない場合はエラーになる
      // その場合はZ3ProcessFallbackにフォールバック
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      const z3Module: any = await import('z3-solver').catch(() => null);
      
      if (!z3Module) {
        throw new Error('z3-solver module not found. Install with: npm install z3-solver');
      }

      const { init } = z3Module;
      this.z3Instance = await init();
      this.initialized = true;

      if (this.options.logLevel !== 'silent') {
        console.log('[Z3WasmClient] Initialized successfully');
      }
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      throw new Error(`Failed to initialize Z3 WebAssembly: ${message}`);
    }
  }

  /**
   * SMT-LIB2形式のアサーションの充足可能性をチェック
   */
  async checkSat(smtLib2: string): Promise<Z3Result> {
    if (!this.initialized || !this.z3Instance) {
      throw new Error('Z3WasmClient not initialized. Call initialize() first.');
    }

    try {
      const z3 = this.z3Instance as {
        Context: new (name: string) => {
          eval: (expr: string) => Promise<{ toString: () => string }>;
        };
      };

      const ctx = new z3.Context('main');
      
      // SMT-LIB2をパースして評価
      // タイムアウト付きで実行
      const timeoutPromise = new Promise<Z3Result>((_, reject) => {
        setTimeout(() => reject(new Error('Z3 timeout')), this.options.timeout);
      });

      const evalPromise = (async (): Promise<Z3Result> => {
        try {
          // SMT-LIB2形式を評価
          const fullScript = `${smtLib2}\n(check-sat)`;
          const result = await ctx.eval(fullScript);
          const resultStr = result.toString().toLowerCase();
          
          if (resultStr.includes('sat') && !resultStr.includes('unsat')) {
            return 'sat';
          } else if (resultStr.includes('unsat')) {
            return 'unsat';
          } else if (resultStr.includes('unknown')) {
            return 'unknown';
          }
          return 'unknown';
        } catch {
          return 'error';
        }
      })();

      return await Promise.race([evalPromise, timeoutPromise]);
    } catch (error) {
      if (this.options.logLevel !== 'silent') {
        console.error('[Z3WasmClient] checkSat error:', error);
      }
      return 'error';
    }
  }

  /**
   * モデルを取得（sat の場合のみ有効）
   */
  async getModel(smtLib2: string): Promise<string | null> {
    if (!this.initialized || !this.z3Instance) {
      throw new Error('Z3WasmClient not initialized. Call initialize() first.');
    }

    try {
      const result = await this.checkSat(smtLib2);
      if (result !== 'sat') {
        return null;
      }

      const z3 = this.z3Instance as {
        Context: new (name: string) => {
          eval: (expr: string) => Promise<{ toString: () => string }>;
        };
      };

      const ctx = new z3.Context('main');
      const fullScript = `${smtLib2}\n(check-sat)\n(get-model)`;
      const modelResult = await ctx.eval(fullScript);
      return modelResult.toString();
    } catch (error) {
      if (this.options.logLevel !== 'silent') {
        console.error('[Z3WasmClient] getModel error:', error);
      }
      return null;
    }
  }

  /**
   * 証明を取得（unsat の場合のみ有効）
   */
  async getProof(smtLib2: string): Promise<string | null> {
    if (!this.initialized || !this.z3Instance) {
      throw new Error('Z3WasmClient not initialized. Call initialize() first.');
    }

    try {
      const result = await this.checkSat(smtLib2);
      if (result !== 'unsat') {
        return null;
      }

      const z3 = this.z3Instance as {
        Context: new (name: string) => {
          eval: (expr: string) => Promise<{ toString: () => string }>;
        };
      };

      const ctx = new z3.Context('main');
      const fullScript = `(set-option :produce-proofs true)\n${smtLib2}\n(check-sat)\n(get-proof)`;
      const proofResult = await ctx.eval(fullScript);
      return proofResult.toString();
    } catch (error) {
      if (this.options.logLevel !== 'silent') {
        console.error('[Z3WasmClient] getProof error:', error);
      }
      return null;
    }
  }

  /**
   * リソースを解放
   */
  async dispose(): Promise<void> {
    this.z3Instance = null;
    this.initialized = false;
  }

  /**
   * クライアントが利用可能かどうか
   */
  isAvailable(): boolean {
    return this.initialized && this.z3Instance !== null;
  }
}
