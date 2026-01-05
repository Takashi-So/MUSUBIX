/**
 * CLI Runner Facade
 *
 * @fileoverview Executes CLI commands for E2E testing
 * @module @musubix/core/testing/cli-runner
 * @requirement REQ-E2E-001
 */

import { exec, spawn } from 'child_process';
import { promisify } from 'util';
import * as path from 'path';
import { fileURLToPath } from 'url';
import type { ICliRunner, CliResult, CliRunnerOptions } from './types.js';

const execAsync = promisify(exec);

// Get the CLI path relative to this module
const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const DEFAULT_CLI_PATH = path.resolve(__dirname, '../../../../bin/musubix.js');

/**
 * CLI Runner implementation
 */
class CliRunner implements ICliRunner {
  private readonly cliPath: string;
  private readonly defaultOptions: CliRunnerOptions;

  constructor(cliPath?: string, defaultOptions: CliRunnerOptions = {}) {
    this.cliPath = cliPath || DEFAULT_CLI_PATH;
    this.defaultOptions = defaultOptions;
  }

  /**
   * Run CLI command
   */
  async run(args: string[], options: CliRunnerOptions = {}): Promise<CliResult> {
    const mergedOptions = { ...this.defaultOptions, ...options };
    const timeout = mergedOptions.timeout || 30000;
    const cwd = mergedOptions.cwd || process.cwd();
    const env = { ...process.env, ...mergedOptions.env };

    const command = `node ${this.cliPath} ${args.join(' ')}`;
    const startTime = Date.now();

    try {
      const { stdout, stderr } = await execAsync(command, {
        cwd,
        env,
        timeout,
        maxBuffer: 10 * 1024 * 1024, // 10MB
      });

      return {
        stdout: stdout.trim(),
        stderr: stderr.trim(),
        exitCode: 0,
        duration: Date.now() - startTime,
      };
    } catch (error: unknown) {
      const execError = error as {
        stdout?: string;
        stderr?: string;
        code?: number;
        killed?: boolean;
      };

      return {
        stdout: execError.stdout?.trim() || '',
        stderr: execError.stderr?.trim() || '',
        exitCode: execError.code ?? (execError.killed ? 137 : 1),
        duration: Date.now() - startTime,
      };
    }
  }

  /**
   * Run CLI with stdin input
   */
  async runWithInput(args: string[], input: string): Promise<CliResult> {
    const startTime = Date.now();

    return new Promise((resolve) => {
      const child = spawn('node', [this.cliPath, ...args], {
        cwd: this.defaultOptions.cwd || process.cwd(),
        env: { ...process.env, ...this.defaultOptions.env },
        stdio: ['pipe', 'pipe', 'pipe'],
      });

      let stdout = '';
      let stderr = '';

      child.stdout.on('data', (data) => {
        stdout += data.toString();
      });

      child.stderr.on('data', (data) => {
        stderr += data.toString();
      });

      child.on('close', (code) => {
        resolve({
          stdout: stdout.trim(),
          stderr: stderr.trim(),
          exitCode: code ?? 0,
          duration: Date.now() - startTime,
        });
      });

      child.on('error', () => {
        resolve({
          stdout: stdout.trim(),
          stderr: stderr.trim(),
          exitCode: 1,
          duration: Date.now() - startTime,
        });
      });

      // Write input and close stdin
      child.stdin.write(input);
      child.stdin.end();
    });
  }

  /**
   * Run requirements subcommand
   */
  async requirements(subcommand: string, ...args: string[]): Promise<CliResult> {
    return this.run(['requirements', subcommand, ...args]);
  }

  /**
   * Run design subcommand
   */
  async design(subcommand: string, ...args: string[]): Promise<CliResult> {
    return this.run(['design', subcommand, ...args]);
  }

  /**
   * Run learn subcommand
   */
  async learn(subcommand: string, ...args: string[]): Promise<CliResult> {
    return this.run(['learn', subcommand, ...args]);
  }

  /**
   * Run ontology subcommand
   */
  async ontology(subcommand: string, ...args: string[]): Promise<CliResult> {
    return this.run(['ontology', subcommand, ...args]);
  }

  /**
   * Run perf subcommand
   */
  async perf(subcommand: string, ...args: string[]): Promise<CliResult> {
    return this.run(['perf', subcommand, ...args]);
  }

  /**
   * Run codegen subcommand
   */
  async codegen(subcommand: string, ...args: string[]): Promise<CliResult> {
    return this.run(['codegen', subcommand, ...args]);
  }

  /**
   * Run trace subcommand
   */
  async trace(subcommand: string, ...args: string[]): Promise<CliResult> {
    return this.run(['trace', subcommand, ...args]);
  }
}

/**
 * Create a CLI runner instance
 *
 * @param cliPath - Path to CLI executable (default: bin/musubix.js)
 * @param options - Default options for all commands
 * @returns CLI runner instance
 *
 * @example
 * ```typescript
 * const cli = createCliRunner();
 * const result = await cli.run(['--version']);
 * expect(result.exitCode).toBe(0);
 * ```
 */
export function createCliRunner(
  cliPath?: string,
  options?: CliRunnerOptions
): ICliRunner {
  return new CliRunner(cliPath, options);
}

/**
 * Create a CLI runner with working directory
 *
 * @param cwd - Working directory
 * @returns CLI runner instance
 */
export function createCliRunnerInDir(cwd: string): ICliRunner {
  return createCliRunner(undefined, { cwd });
}
