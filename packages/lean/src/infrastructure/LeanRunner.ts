/**
 * @fileoverview Lean execution runner
 * @module @nahisaho/musubix-lean/infrastructure
 * @traceability REQ-LEAN-CORE-004
 */

import { spawn, type ChildProcess } from 'child_process';
import * as fs from 'fs/promises';
import * as path from 'path';
import type { LeanConfig, LeanVersion } from '../types.js';
import { LeanExecutionError, LeanNotFoundError } from '../errors.js';

/**
 * Lean execution result
 */
export interface LeanExecutionResult {
  success: boolean;
  stdout: string;
  stderr: string;
  exitCode: number;
  duration: number;
}

/**
 * Lean goal information
 */
export interface LeanGoalInfo {
  goals: string[];
  hypotheses: string[];
}

/**
 * Runs Lean commands and validates proofs
 * @traceability REQ-LEAN-CORE-004
 */
export class LeanRunner {
  private leanPath: string;
  private projectPath: string;
  private timeout: number;
  private lakeEnabled: boolean;
  private verbose: boolean;
  private leanVersion: LeanVersion | null = null;

  constructor(config: Partial<LeanConfig> = {}) {
    this.leanPath = config.leanPath ?? 'lean';
    this.projectPath = config.projectPath ?? process.cwd();
    this.lakeEnabled = config.lakeEnabled ?? true;
    this.timeout = config.timeout ?? 30000;
    this.verbose = config.verbose ?? false;
  }

  /**
   * Execute Lean code file
   * @traceability REQ-LEAN-CORE-004
   */
  async execute(filePath: string, options?: { timeout?: number }): Promise<LeanExecutionResult> {
    const timeout = options?.timeout ?? this.timeout;
    const startTime = Date.now();

    return new Promise((resolve, reject) => {
      const args = this.buildLeanArgs(filePath);

      if (this.verbose) {
        console.log(`[LeanRunner] Executing: ${this.leanPath} ${args.join(' ')}`);
      }

      const proc: ChildProcess = spawn(this.leanPath, args, {
        cwd: this.projectPath,
        env: {
          ...process.env,
          LEAN_PATH: process.env.LEAN_PATH || '',
        },
      });

      let stdout = '';
      let stderr = '';
      let killed = false;

      const timeoutId = setTimeout(() => {
        killed = true;
        proc.kill('SIGTERM');
      }, timeout);

      proc.stdout?.on('data', (data: Buffer) => {
        stdout += data.toString();
      });

      proc.stderr?.on('data', (data: Buffer) => {
        stderr += data.toString();
      });

      proc.on('error', (error: Error) => {
        clearTimeout(timeoutId);
        if (error.message.includes('ENOENT')) {
          reject(new LeanNotFoundError(this.leanPath));
        } else {
          reject(new LeanExecutionError('Execution failed', error.message, stderr));
        }
      });

      proc.on('close', (exitCode: number | null) => {
        clearTimeout(timeoutId);
        const duration = Date.now() - startTime;
        
        if (killed) {
          resolve({
            success: false,
            stdout,
            stderr: 'Execution timed out',
            exitCode: -1,
            duration,
          });
        } else {
          resolve({
            success: exitCode === 0,
            stdout,
            stderr,
            exitCode: exitCode ?? 1,
            duration,
          });
        }
      });
    });
  }

  /**
   * Execute Lean code string (creates temp file)
   */
  async executeCode(code: string, options?: { timeout?: number }): Promise<LeanExecutionResult> {
    const tempDir = path.join(this.projectPath, '.musubix-temp');
    const tempFile = path.join(tempDir, `temp_${Date.now()}.lean`);

    try {
      await fs.mkdir(tempDir, { recursive: true });
      await fs.writeFile(tempFile, code, 'utf-8');

      const result = await this.execute(tempFile, options);

      // Clean up
      await fs.unlink(tempFile).catch(() => {});

      return result;
    } catch (error) {
      // Clean up on error
      await fs.unlink(tempFile).catch(() => {});
      throw error;
    }
  }

  /**
   * Check if Lean can type-check a file
   */
  async typeCheck(filePath: string): Promise<{ valid: boolean; errors: string[] }> {
    const result = await this.execute(filePath);

    if (result.success) {
      return { valid: true, errors: [] };
    }

    // Parse errors from stderr
    const errors = this.parseErrors(result.stderr);
    return { valid: false, errors };
  }

  /**
   * Get current proof state (goals and hypotheses)
   */
  async getGoalState(_filePath: string, _line: number, _column: number): Promise<LeanGoalInfo> {
    // In a real implementation, this would use the Lean server protocol
    // For now, return a placeholder
    return {
      goals: [],
      hypotheses: [],
    };
  }

  /**
   * Run Lake build
   */
  async lakeBuild(projectPath?: string): Promise<LeanExecutionResult> {
    const cwd = projectPath ?? this.projectPath;
    const startTime = Date.now();

    return new Promise((resolve, reject) => {
      const proc: ChildProcess = spawn('lake', ['build'], {
        cwd,
      });

      let stdout = '';
      let stderr = '';

      const timeoutId = setTimeout(() => {
        proc.kill('SIGTERM');
      }, this.timeout * 2);

      proc.stdout?.on('data', (data: Buffer) => {
        stdout += data.toString();
      });

      proc.stderr?.on('data', (data: Buffer) => {
        stderr += data.toString();
      });

      proc.on('error', (error: Error) => {
        clearTimeout(timeoutId);
        reject(new LeanExecutionError('Lake build failed', error.message, stderr));
      });

      proc.on('close', (exitCode: number | null) => {
        clearTimeout(timeoutId);
        const duration = Date.now() - startTime;
        resolve({
          success: exitCode === 0,
          stdout,
          stderr,
          exitCode: exitCode ?? 1,
          duration,
        });
      });
    });
  }

  /**
   * Get Lean version information
   */
  async getVersion(): Promise<LeanVersion> {
    if (this.leanVersion) {
      return this.leanVersion;
    }

    return new Promise((resolve, reject) => {
      const proc: ChildProcess = spawn(this.leanPath, ['--version']);

      let stdout = '';

      const timeoutId = setTimeout(() => {
        proc.kill('SIGTERM');
        reject(new LeanExecutionError('Version check timed out', '', ''));
      }, 5000);

      proc.stdout?.on('data', (data: Buffer) => {
        stdout += data.toString();
      });

      proc.on('error', (_error: Error) => {
        clearTimeout(timeoutId);
        reject(new LeanNotFoundError(this.leanPath));
      });

      proc.on('close', (exitCode: number | null) => {
        clearTimeout(timeoutId);
        if (exitCode !== 0) {
          reject(new LeanExecutionError('Failed to get Lean version', '', ''));
          return;
        }

        const version = this.parseVersion(stdout);
        this.leanVersion = version;
        resolve(version);
      });
    });
  }

  /**
   * Parse version from Lean output
   */
  private parseVersion(output: string): LeanVersion {
    // Parse "Lean (version 4.x.x, ...)"
    const match = output.match(/version (\d+)\.(\d+)\.(\d+)/);

    if (match) {
      return {
        major: parseInt(match[1], 10),
        minor: parseInt(match[2], 10),
        patch: parseInt(match[3], 10),
        full: `${match[1]}.${match[2]}.${match[3]}`,
      };
    }

    // Fallback
    return {
      major: 4,
      minor: 0,
      patch: 0,
      full: 'unknown',
    };
  }

  /**
   * Build Lean command arguments
   */
  private buildLeanArgs(filePath: string): string[] {
    if (this.lakeEnabled) {
      // When using Lake, we run the file through Lake
      return ['env', this.leanPath, filePath];
    }

    // Direct Lean execution
    return [filePath];
  }

  /**
   * Parse Lean error messages
   */
  private parseErrors(stderr: string): string[] {
    const errors: string[] = [];
    const lines = stderr.split('\n');

    for (const line of lines) {
      // Lean error format: "file:line:col: error: message"
      if (line.includes('error:')) {
        errors.push(line.trim());
      }
    }

    return errors.length > 0 ? errors : [stderr.trim()];
  }

  /**
   * Check if Lean is available
   */
  async isAvailable(): Promise<boolean> {
    try {
      await this.getVersion();
      return true;
    } catch {
      return false;
    }
  }

  /**
   * Get configuration
   */
  getConfig(): LeanConfig {
    return {
      leanPath: this.leanPath,
      projectPath: this.projectPath,
      timeout: this.timeout,
      lakeEnabled: this.lakeEnabled,
      verbose: this.verbose,
    };
  }

  /**
   * Update configuration
   */
  updateConfig(config: Partial<LeanConfig>): void {
    if (config.leanPath) {
      this.leanPath = config.leanPath;
      this.leanVersion = null;
    }
    if (config.projectPath) this.projectPath = config.projectPath;
    if (config.timeout) this.timeout = config.timeout;
    if (config.lakeEnabled !== undefined) this.lakeEnabled = config.lakeEnabled;
    if (config.verbose !== undefined) this.verbose = config.verbose;
  }
}
