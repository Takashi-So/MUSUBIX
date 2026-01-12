/**
 * ResultReporter - Report watch results to terminal and JSON
 * 
 * Implements: TSK-WATCH-003, DES-WATCH-006, REQ-WATCH-006
 */

import { writeFile, mkdir } from 'node:fs/promises';
import { join, dirname } from 'node:path';
import type { TaskResult } from './task-scheduler.js';
import type { Issue } from './types.js';

/**
 * Report configuration
 */
export interface ReportConfig {
  /** Output directory for JSON reports */
  outputDir: string;
  /** Output format */
  format: 'json' | 'terminal' | 'both';
  /** Verbose output */
  verbose: boolean;
  /** Enable colors in terminal output */
  colors: boolean;
}

/**
 * Watch report
 */
export interface WatchReport {
  /** Report timestamp */
  timestamp: Date;
  /** Task results */
  tasks: TaskResult[];
  /** Summary */
  summary: {
    total: number;
    passed: number;
    failed: number;
    issues: number;
    errors: number;
    warnings: number;
  };
}

/**
 * ANSI color codes
 */
const Colors = {
  reset: '\x1b[0m',
  red: '\x1b[31m',
  green: '\x1b[32m',
  yellow: '\x1b[33m',
  blue: '\x1b[34m',
  magenta: '\x1b[35m',
  cyan: '\x1b[36m',
  gray: '\x1b[90m',
  bold: '\x1b[1m',
};

/**
 * Default configuration
 */
const DEFAULT_CONFIG: ReportConfig = {
  outputDir: '.musubix/watch',
  format: 'both',
  verbose: false,
  colors: true,
};

/**
 * ResultReporter class
 */
export class ResultReporter {
  private config: ReportConfig;
  private results: TaskResult[] = [];
  private maxResults = 100;

  constructor(config: Partial<ReportConfig> = {}) {
    this.config = { ...DEFAULT_CONFIG, ...config };
  }

  /**
   * Color a string (if colors enabled)
   */
  private color(str: string, colorCode: string): string {
    if (!this.config.colors) return str;
    return `${colorCode}${str}${Colors.reset}`;
  }

  /**
   * Report a task result
   */
  report(result: TaskResult): void {
    this.results.push(result);
    
    // Trim old results
    if (this.results.length > this.maxResults) {
      this.results = this.results.slice(-this.maxResults);
    }

    if (this.config.format === 'terminal' || this.config.format === 'both') {
      this.printToTerminal(result);
    }

    if (this.config.format === 'json' || this.config.format === 'both') {
      this.writeJSON(result).catch(console.error);
    }
  }

  /**
   * Print result to terminal
   */
  private printToTerminal(result: TaskResult): void {
    const timestamp = result.timestamp.toISOString().slice(11, 19);
    const typeLabel = this.getTypeLabel(result.type);
    const status = result.success
      ? this.color('✓', Colors.green)
      : this.color('✗', Colors.red);
    const duration = `${result.duration}ms`;

    console.log(
      `${this.color(timestamp, Colors.gray)} ${status} ${typeLabel} ${this.color(duration, Colors.gray)}`
    );

    if (result.error) {
      console.log(`  ${this.color('Error:', Colors.red)} ${result.error}`);
    }

    if (result.issues.length > 0) {
      const errors = result.issues.filter(i => i.severity === 'error').length;
      const warnings = result.issues.filter(i => i.severity === 'warning').length;
      
      console.log(
        `  ${this.color(`${errors} error(s)`, Colors.red)}, ` +
        `${this.color(`${warnings} warning(s)`, Colors.yellow)}`
      );

      if (this.config.verbose) {
        this.printIssues(result.issues);
      }
    }
  }

  /**
   * Get colored label for task type
   */
  private getTypeLabel(type: string): string {
    const labels: Record<string, [string, string]> = {
      lint: ['LINT', Colors.cyan],
      test: ['TEST', Colors.blue],
      security: ['SECURITY', Colors.magenta],
      ears: ['EARS', Colors.yellow],
    };

    const [label, color] = labels[type] ?? [type.toUpperCase(), Colors.gray];
    return this.color(`[${label}]`, color);
  }

  /**
   * Print issues to terminal
   */
  private printIssues(issues: Issue[]): void {
    const grouped = this.groupIssuesByFile(issues);

    for (const [file, fileIssues] of grouped) {
      console.log(`  ${this.color(file, Colors.bold)}`);
      
      for (const issue of fileIssues) {
        const location = issue.line ? `:${issue.line}${issue.column ? `:${issue.column}` : ''}` : '';
        const severityColor = issue.severity === 'error' ? Colors.red : Colors.yellow;
        const severityLabel = this.color(issue.severity, severityColor);
        const ruleLabel = issue.ruleId ? this.color(`(${issue.ruleId})`, Colors.gray) : '';
        
        console.log(`    ${location} ${severityLabel} ${issue.message} ${ruleLabel}`);
      }
    }
  }

  /**
   * Group issues by file
   */
  private groupIssuesByFile(issues: Issue[]): Map<string, Issue[]> {
    const grouped = new Map<string, Issue[]>();
    
    for (const issue of issues) {
      const existing = grouped.get(issue.file) ?? [];
      existing.push(issue);
      grouped.set(issue.file, existing);
    }

    return grouped;
  }

  /**
   * Write result to JSON file
   */
  private async writeJSON(result: TaskResult): Promise<void> {
    const outputPath = join(
      this.config.outputDir,
      `${result.type}-${Date.now()}.json`
    );

    await mkdir(dirname(outputPath), { recursive: true });
    await writeFile(outputPath, JSON.stringify(result, null, 2));
  }

  /**
   * Get latest report
   */
  getLatestReport(): WatchReport {
    const summary = {
      total: this.results.length,
      passed: this.results.filter(r => r.success).length,
      failed: this.results.filter(r => !r.success).length,
      issues: this.results.reduce((sum, r) => sum + r.issues.length, 0),
      errors: this.results.reduce(
        (sum, r) => sum + r.issues.filter(i => i.severity === 'error').length,
        0
      ),
      warnings: this.results.reduce(
        (sum, r) => sum + r.issues.filter(i => i.severity === 'warning').length,
        0
      ),
    };

    return {
      timestamp: new Date(),
      tasks: [...this.results],
      summary,
    };
  }

  /**
   * Export report to JSON file
   */
  async exportJSON(path: string): Promise<void> {
    const report = this.getLatestReport();
    await mkdir(dirname(path), { recursive: true });
    await writeFile(path, JSON.stringify(report, null, 2));
  }

  /**
   * Print summary to terminal
   */
  printSummary(): void {
    const report = this.getLatestReport();
    const { summary } = report;

    console.log('');
    console.log(this.color('═══ Watch Summary ═══', Colors.bold));
    console.log(`  Total tasks: ${summary.total}`);
    console.log(`  ${this.color('Passed:', Colors.green)} ${summary.passed}`);
    console.log(`  ${this.color('Failed:', Colors.red)} ${summary.failed}`);
    console.log(`  ${this.color('Errors:', Colors.red)} ${summary.errors}`);
    console.log(`  ${this.color('Warnings:', Colors.yellow)} ${summary.warnings}`);
    console.log('');
  }

  /**
   * Clear results
   */
  clear(): void {
    this.results = [];
  }

  /**
   * Update configuration
   */
  updateConfig(config: Partial<ReportConfig>): void {
    this.config = { ...this.config, ...config };
  }
}

/**
 * Create a ResultReporter instance
 */
export function createResultReporter(config?: Partial<ReportConfig>): ResultReporter {
  return new ResultReporter(config);
}
