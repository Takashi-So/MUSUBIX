/**
 * LintRunner - ESLint integration for watch mode
 * 
 * Implements: TSK-WATCH-004, DES-WATCH-002, REQ-WATCH-002
 */

import { spawn } from 'node:child_process';
import { extname } from 'node:path';
import type { TaskRunner, Issue } from '../types.js';

/**
 * ESLint output format
 */
interface ESLintResult {
  filePath: string;
  messages: Array<{
    ruleId: string | null;
    severity: 1 | 2;
    message: string;
    line: number;
    column: number;
  }>;
  errorCount: number;
  warningCount: number;
}

/**
 * LintRunner class
 */
export class LintRunner implements TaskRunner {
  readonly name = 'lint';
  
  private supportedExtensions = ['.ts', '.tsx', '.js', '.jsx', '.mjs', '.cjs'];

  /**
   * Check if runner supports the file
   */
  supports(file: string): boolean {
    const ext = extname(file);
    return this.supportedExtensions.includes(ext);
  }

  /**
   * Run ESLint on files
   */
  async run(files: string[]): Promise<Issue[]> {
    if (files.length === 0) return [];

    try {
      const output = await this.runESLint(files);
      return this.parseOutput(output);
    } catch (error) {
      // ESLint not found or failed to run
      return [{
        severity: 'error',
        message: `Lint runner failed: ${error instanceof Error ? error.message : String(error)}`,
        file: files[0],
      }];
    }
  }

  /**
   * Run ESLint process
   */
  private runESLint(files: string[]): Promise<string> {
    return new Promise((resolve, reject) => {
      const args = [
        'eslint',
        '--format', 'json',
        '--no-error-on-unmatched-pattern',
        ...files,
      ];

      const child = spawn('npx', args, {
        stdio: ['pipe', 'pipe', 'pipe'],
        shell: true,
      });

      let stdout = '';
      let stderr = '';

      child.stdout?.on('data', (data) => {
        stdout += data.toString();
      });

      child.stderr?.on('data', (data) => {
        stderr += data.toString();
      });

      child.on('error', (error) => {
        reject(error);
      });

      child.on('close', (code) => {
        // ESLint exits with 1 if there are errors, but still outputs JSON
        if (stdout) {
          resolve(stdout);
        } else if (code !== 0 && stderr) {
          reject(new Error(stderr));
        } else {
          resolve('[]');
        }
      });
    });
  }

  /**
   * Parse ESLint JSON output
   */
  private parseOutput(output: string): Issue[] {
    const issues: Issue[] = [];

    try {
      const results: ESLintResult[] = JSON.parse(output);

      for (const result of results) {
        for (const message of result.messages) {
          issues.push({
            severity: message.severity === 2 ? 'error' : 'warning',
            message: message.message,
            file: result.filePath,
            line: message.line,
            column: message.column,
            ruleId: message.ruleId ?? undefined,
          });
        }
      }
    } catch {
      // Failed to parse output
      if (output.trim()) {
        issues.push({
          severity: 'error',
          message: `Failed to parse ESLint output: ${output.slice(0, 200)}`,
          file: '',
        });
      }
    }

    return issues;
  }
}

/**
 * Create a LintRunner instance
 */
export function createLintRunner(): LintRunner {
  return new LintRunner();
}
