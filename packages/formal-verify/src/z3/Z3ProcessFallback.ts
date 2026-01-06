/**
 * Z3 Process Fallback Client
 * 
 * ネイティブZ3コマンドラインツールを使用するフォールバッククライアント
 * 
 * @implements {Z3Client}
 */

import { spawn } from 'child_process';
import { writeFile, unlink, mkdtemp } from 'fs/promises';
import { tmpdir } from 'os';
import { join } from 'path';
import type { Z3Client, Z3Result, Z3Options } from './types.js';

/**
 * Z3プロセスフォールバッククライアント
 * 
 * z3-wasmが利用できない場合のフォールバックとして、
 * システムにインストールされたZ3コマンドラインツールを使用します。
 * 
 * @example
 * ```typescript
 * const client = new Z3ProcessFallback({ timeout: 10000 });
 * await client.initialize();
 * if (client.isAvailable()) {
 *   const result = await client.checkSat('(declare-const x Int) (assert (> x 0))');
 * }
 * ```
 */
export class Z3ProcessFallback implements Z3Client {
  private z3Path: string | null = null;
  private initialized = false;
  private available = false;
  private readonly options: Z3Options;

  constructor(options: Z3Options = {}) {
    this.options = {
      timeout: options.timeout ?? 30000,
      logLevel: options.logLevel ?? 'silent',
      memoryLimit: options.memoryLimit ?? 512,
    };
  }

  /**
   * Z3コマンドラインツールの存在を確認
   */
  async initialize(): Promise<void> {
    if (this.initialized) {
      return;
    }

    try {
      // z3コマンドの存在確認
      const z3Path = await this.findZ3Executable();
      
      if (z3Path) {
        this.z3Path = z3Path;
        this.available = true;
        
        if (this.options.logLevel !== 'silent') {
          console.log(`[Z3ProcessFallback] Found Z3 at: ${z3Path}`);
        }
      } else {
        this.available = false;
        
        if (this.options.logLevel !== 'silent') {
          console.warn('[Z3ProcessFallback] Z3 executable not found in PATH');
        }
      }

      this.initialized = true;
    } catch (error) {
      this.available = false;
      this.initialized = true;
      
      if (this.options.logLevel !== 'silent') {
        console.error('[Z3ProcessFallback] Initialization error:', error);
      }
    }
  }

  /**
   * Z3実行ファイルを検索
   */
  private async findZ3Executable(): Promise<string | null> {
    const candidates = ['z3', 'z3.exe'];
    
    for (const candidate of candidates) {
      try {
        const result = await this.runCommand('which', [candidate]);
        if (result.exitCode === 0 && result.stdout.trim()) {
          return result.stdout.trim();
        }
      } catch {
        // Windows では where を使用
        try {
          const result = await this.runCommand('where', [candidate]);
          if (result.exitCode === 0 && result.stdout.trim()) {
            return result.stdout.trim().split('\n')[0].trim();
          }
        } catch {
          // continue
        }
      }
    }

    return null;
  }

  /**
   * コマンドを実行
   */
  private runCommand(
    command: string,
    args: string[]
  ): Promise<{ stdout: string; stderr: string; exitCode: number }> {
    return new Promise((resolve, reject) => {
      const proc = spawn(command, args, {
        timeout: 5000,
        shell: true,
      });

      let stdout = '';
      let stderr = '';

      proc.stdout?.on('data', (data) => {
        stdout += data.toString();
      });

      proc.stderr?.on('data', (data) => {
        stderr += data.toString();
      });

      proc.on('close', (code) => {
        resolve({ stdout, stderr, exitCode: code ?? 1 });
      });

      proc.on('error', (error) => {
        reject(error);
      });
    });
  }

  /**
   * SMT-LIB2形式のアサーションの充足可能性をチェック
   */
  async checkSat(smtLib2: string): Promise<Z3Result> {
    if (!this.initialized) {
      throw new Error('Z3ProcessFallback not initialized. Call initialize() first.');
    }

    if (!this.available || !this.z3Path) {
      return 'error';
    }

    let tempDir: string | null = null;
    let tempFile: string | null = null;

    try {
      // 一時ファイルにSMT-LIB2スクリプトを書き込む
      tempDir = await mkdtemp(join(tmpdir(), 'z3-'));
      tempFile = join(tempDir, 'input.smt2');
      
      const fullScript = `${smtLib2}\n(check-sat)\n(exit)`;
      await writeFile(tempFile, fullScript, 'utf-8');

      // Z3を実行
      const result = await this.runZ3(tempFile);
      
      const output = result.stdout.toLowerCase();
      if (output.includes('unsat')) {
        return 'unsat';
      } else if (output.includes('sat')) {
        return 'sat';
      } else if (output.includes('unknown')) {
        return 'unknown';
      }

      return 'unknown';
    } catch (error) {
      if (this.options.logLevel !== 'silent') {
        console.error('[Z3ProcessFallback] checkSat error:', error);
      }
      return 'error';
    } finally {
      // 一時ファイルを削除
      if (tempFile) {
        await unlink(tempFile).catch(() => {});
      }
      if (tempDir) {
        await unlink(tempDir).catch(() => {});
      }
    }
  }

  /**
   * Z3プロセスを実行
   */
  private runZ3(inputFile: string): Promise<{ stdout: string; stderr: string; exitCode: number }> {
    return new Promise((resolve, reject) => {
      if (!this.z3Path) {
        reject(new Error('Z3 path not set'));
        return;
      }

      const args = [
        `-T:${Math.floor(this.options.timeout! / 1000)}`,
        `-memory:${this.options.memoryLimit}`,
        inputFile,
      ];

      const proc = spawn(this.z3Path, args, {
        timeout: this.options.timeout,
      });

      let stdout = '';
      let stderr = '';

      proc.stdout?.on('data', (data) => {
        stdout += data.toString();
      });

      proc.stderr?.on('data', (data) => {
        stderr += data.toString();
      });

      proc.on('close', (code) => {
        resolve({ stdout, stderr, exitCode: code ?? 1 });
      });

      proc.on('error', (error) => {
        reject(error);
      });
    });
  }

  /**
   * モデルを取得（sat の場合のみ有効）
   */
  async getModel(smtLib2: string): Promise<string | null> {
    if (!this.available || !this.z3Path) {
      return null;
    }

    let tempDir: string | null = null;
    let tempFile: string | null = null;

    try {
      tempDir = await mkdtemp(join(tmpdir(), 'z3-'));
      tempFile = join(tempDir, 'input.smt2');
      
      const fullScript = `${smtLib2}\n(check-sat)\n(get-model)\n(exit)`;
      await writeFile(tempFile, fullScript, 'utf-8');

      const result = await this.runZ3(tempFile);
      
      if (!result.stdout.toLowerCase().includes('sat')) {
        return null;
      }

      // モデル部分を抽出
      const modelMatch = result.stdout.match(/\(model[\s\S]*\)/);
      return modelMatch ? modelMatch[0] : result.stdout;
    } catch (error) {
      if (this.options.logLevel !== 'silent') {
        console.error('[Z3ProcessFallback] getModel error:', error);
      }
      return null;
    } finally {
      if (tempFile) await unlink(tempFile).catch(() => {});
      if (tempDir) await unlink(tempDir).catch(() => {});
    }
  }

  /**
   * 証明を取得（unsat の場合のみ有効）
   */
  async getProof(smtLib2: string): Promise<string | null> {
    if (!this.available || !this.z3Path) {
      return null;
    }

    let tempDir: string | null = null;
    let tempFile: string | null = null;

    try {
      tempDir = await mkdtemp(join(tmpdir(), 'z3-'));
      tempFile = join(tempDir, 'input.smt2');
      
      const fullScript = `(set-option :produce-proofs true)\n${smtLib2}\n(check-sat)\n(get-proof)\n(exit)`;
      await writeFile(tempFile, fullScript, 'utf-8');

      const result = await this.runZ3(tempFile);
      
      if (!result.stdout.toLowerCase().includes('unsat')) {
        return null;
      }

      return result.stdout;
    } catch (error) {
      if (this.options.logLevel !== 'silent') {
        console.error('[Z3ProcessFallback] getProof error:', error);
      }
      return null;
    } finally {
      if (tempFile) await unlink(tempFile).catch(() => {});
      if (tempDir) await unlink(tempDir).catch(() => {});
    }
  }

  /**
   * リソースを解放
   */
  async dispose(): Promise<void> {
    this.z3Path = null;
    this.available = false;
  }

  /**
   * クライアントが利用可能かどうか
   */
  isAvailable(): boolean {
    return this.available && this.z3Path !== null;
  }
}
