/**
 * TestRunner - Vitest integration for watch mode
 * 
 * Implements: TSK-WATCH-005, DES-WATCH-003, REQ-WATCH-003
 */

import { spawn } from 'node:child_process';
import { extname, basename, dirname, join } from 'node:path';
import { stat } from 'node:fs/promises';
import type { TaskRunner, Issue } from '../types.js';

/**
 * Vitest JSON output format
 */
interface VitestResult {
  numTotalTests: number;
  numPassedTests: number;
  numFailedTests: number;
  numPendingTests: number;
  testResults: Array<{
    name: string;
    status: 'passed' | 'failed' | 'pending';
    assertionResults: Array<{
      status: 'passed' | 'failed' | 'pending';
      title: string;
      failureMessages: string[];
    }>;
  }>;
}

/**
 * TestRunner class
 */
export class TestRunner implements TaskRunner {
  readonly name = 'test';
  
  private supportedExtensions = ['.ts', '.tsx', '.js', '.jsx'];
  private testPatterns = ['.test.', '.spec.', '__tests__'];

  /**
   * Check if runner supports the file
   */
  supports(file: string): boolean {
    const ext = extname(file);
    return this.supportedExtensions.includes(ext);
  }

  /**
   * Run tests for changed files
   */
  async run(files: string[]): Promise<Issue[]> {
    if (files.length === 0) return [];

    // Find related test files
    const testFiles = await this.findRelatedTests(files);
    
    if (testFiles.length === 0) {
      return [];
    }

    try {
      const output = await this.runVitest(testFiles);
      return this.parseOutput(output);
    } catch (error) {
      return [{
        severity: 'error',
        message: `Test runner failed: ${error instanceof Error ? error.message : String(error)}`,
        file: files[0],
      }];
    }
  }

  /**
   * Find related test files for source files
   */
  private async findRelatedTests(files: string[]): Promise<string[]> {
    const testFiles: string[] = [];

    for (const file of files) {
      // If file is already a test file, add it
      if (this.isTestFile(file)) {
        testFiles.push(file);
        continue;
      }

      // Try to find corresponding test file
      const relatedTests = await this.findTestFilesFor(file);
      testFiles.push(...relatedTests);
    }

    return [...new Set(testFiles)];
  }

  /**
   * Check if file is a test file
   */
  private isTestFile(file: string): boolean {
    return this.testPatterns.some(pattern => file.includes(pattern));
  }

  /**
   * Find test files for a source file
   */
  private async findTestFilesFor(sourceFile: string): Promise<string[]> {
    const candidates: string[] = [];
    const ext = extname(sourceFile);
    const base = basename(sourceFile, ext);
    const dir = dirname(sourceFile);

    // Check common test file patterns
    const patterns = [
      join(dir, `${base}.test${ext}`),
      join(dir, `${base}.spec${ext}`),
      join(dir, '__tests__', `${base}.test${ext}`),
      join(dir, '__tests__', `${base}.spec${ext}`),
    ];

    for (const pattern of patterns) {
      try {
        await stat(pattern);
        candidates.push(pattern);
      } catch {
        // File doesn't exist
      }
    }

    return candidates;
  }

  /**
   * Run Vitest process
   */
  private runVitest(files: string[]): Promise<string> {
    return new Promise((resolve, reject) => {
      const args = [
        'vitest',
        'run',
        '--reporter=json',
        '--no-watch',
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
        // Try to extract JSON from output
        const jsonMatch = stdout.match(/\{[\s\S]*"testResults"[\s\S]*\}/);
        if (jsonMatch) {
          resolve(jsonMatch[0]);
        } else if (code === 0) {
          resolve('{"numTotalTests":0,"numPassedTests":0,"numFailedTests":0,"testResults":[]}');
        } else {
          // No tests found or failed
          resolve('{"numTotalTests":0,"numPassedTests":0,"numFailedTests":0,"testResults":[]}');
        }
      });
    });
  }

  /**
   * Parse Vitest JSON output
   */
  private parseOutput(output: string): Issue[] {
    const issues: Issue[] = [];

    try {
      const result: VitestResult = JSON.parse(output);

      for (const testResult of result.testResults) {
        for (const assertion of testResult.assertionResults) {
          if (assertion.status === 'failed') {
            issues.push({
              severity: 'error',
              message: `Test failed: ${assertion.title}\n${assertion.failureMessages.join('\n')}`,
              file: testResult.name,
              ruleId: 'test-failure',
            });
          }
        }
      }

      // Add summary if there are failures
      if (result.numFailedTests > 0) {
        issues.push({
          severity: 'info',
          message: `Tests: ${result.numPassedTests} passed, ${result.numFailedTests} failed, ${result.numTotalTests} total`,
          file: '',
        });
      }
    } catch {
      // Failed to parse output
      if (output.trim() && !output.includes('"numTotalTests":0')) {
        issues.push({
          severity: 'warning',
          message: `Failed to parse test output`,
          file: '',
        });
      }
    }

    return issues;
  }
}

/**
 * Create a TestRunner instance
 */
export function createTestRunner(): TestRunner {
  return new TestRunner();
}
