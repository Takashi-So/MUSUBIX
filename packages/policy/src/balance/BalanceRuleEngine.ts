/**
 * BalanceRuleEngine Entity
 *
 * Implements the 90/10 rule for change balance validation.
 * Ensures that counted changes (real functionality) maintain a high ratio.
 *
 * @see TSK-FR-028〜032 - BalanceRuleEngine
 * @see REQ-FR-001〜003 - BalanceRuleEngine
 * @trace DES-MUSUBIX-FR-001 DES-POLICY-001
 */

import {
  type BalanceChange,
  type BalanceChangeType,
  type BalanceMetrics,
  type BalanceEvaluationResult,
  type BalanceConfig,
  getTotalLines,
  isCounted,
  DEFAULT_BALANCE_CONFIG,
} from './types.js';

/**
 * BalanceRuleEngine Interface
 */
export interface IBalanceRuleEngine {
  /** Evaluate the current balance of changes */
  evaluateBalance(): Promise<BalanceEvaluationResult>;

  /** Get current statistics */
  getStats(): Promise<BalanceMetrics>;

  /** Generate a detailed balance report */
  getBalanceReport(): Promise<string>;

  /** Add a change record */
  addChange(change: BalanceChange): void;

  /** Remove a change record */
  removeChange(changeId: string): void;

  /** Get all changes */
  getChanges(): readonly BalanceChange[];

  /** Clear all changes */
  clear(): void;

  /** Infer change type from file path */
  inferChangeType(filePath: string): BalanceChangeType;
}

/**
 * BalanceRuleEngine Implementation
 *
 * Tracks and evaluates the balance between counted and non-counted changes
 * to ensure productivity metrics stay healthy.
 *
 * @example
 * ```typescript
 * const engine = createBalanceRuleEngine();
 *
 * // Add changes
 * engine.addChange(createBalanceChange({ type: 'feature', file: 'src/app.ts', linesAdded: 100, linesRemoved: 0 }));
 * engine.addChange(createBalanceChange({ type: 'config', file: 'tsconfig.json', linesAdded: 5, linesRemoved: 0 }));
 *
 * // Evaluate balance
 * const result = await engine.evaluateBalance();
 * if (!result.passed) {
 *   console.log('Balance warning:', result.message);
 * }
 * ```
 */
export class BalanceRuleEngine implements IBalanceRuleEngine {
  private readonly config: BalanceConfig;
  private changes: Map<string, BalanceChange> = new Map();

  constructor(config?: BalanceConfig) {
    this.config = config ?? DEFAULT_BALANCE_CONFIG;
  }

  /**
   * Evaluate the current balance of changes
   */
  async evaluateBalance(): Promise<BalanceEvaluationResult> {
    const metrics = await this.getStats();

    if (metrics.totalChanges === 0) {
      return {
        passed: true,
        message: 'No changes to evaluate',
        severity: 'info',
        metrics,
      };
    }

    const recommendations = this.generateRecommendations(metrics);

    if (metrics.exceedsThreshold) {
      return {
        passed: false,
        message: `Balance warning: ${(metrics.ratio * 100).toFixed(1)}% non-counted changes exceeds ${(this.config.maxNonCountedRatio * 100).toFixed(0)}% threshold`,
        severity: this.config.exceedSeverity,
        metrics,
        recommendations,
      };
    }

    return {
      passed: true,
      message: `Balance OK: ${(metrics.ratio * 100).toFixed(1)}% non-counted changes (threshold: ${(this.config.maxNonCountedRatio * 100).toFixed(0)}%)`,
      severity: 'info',
      metrics,
    };
  }

  /**
   * Get current statistics
   */
  async getStats(): Promise<BalanceMetrics> {
    let countedChanges = 0;
    let nonCountedChanges = 0;
    let countedLines = 0;
    let nonCountedLines = 0;

    for (const change of this.changes.values()) {
      const lines = getTotalLines(change);

      if (isCounted(change.type)) {
        countedChanges++;
        // Apply type weight from config
        const weight = this.config.typeWeights[change.type];
        countedLines += lines * weight;
      } else {
        nonCountedChanges++;
        nonCountedLines += lines;
      }
    }

    const totalChanges = countedChanges + nonCountedChanges;
    const totalLines = countedLines + nonCountedLines;
    const ratio = totalLines > 0 ? nonCountedLines / totalLines : 0;

    return {
      countedChanges,
      nonCountedChanges,
      totalChanges,
      countedLines: Math.round(countedLines),
      nonCountedLines,
      totalLines: Math.round(totalLines),
      ratio,
      exceedsThreshold: ratio > this.config.maxNonCountedRatio,
      threshold: this.config.maxNonCountedRatio,
    };
  }

  /**
   * Generate a detailed balance report
   */
  async getBalanceReport(): Promise<string> {
    const metrics = await this.getStats();
    const lines: string[] = [];

    lines.push('# Balance Report');
    lines.push('');
    lines.push('## Summary');
    lines.push(`- **Total Changes**: ${metrics.totalChanges}`);
    lines.push(`- **Counted Changes**: ${metrics.countedChanges} (${metrics.countedLines} lines)`);
    lines.push(`- **Non-counted Changes**: ${metrics.nonCountedChanges} (${metrics.nonCountedLines} lines)`);
    lines.push(`- **Balance Ratio**: ${(metrics.ratio * 100).toFixed(1)}% non-counted`);
    lines.push(`- **Threshold**: ${(metrics.threshold * 100).toFixed(0)}%`);
    lines.push(`- **Status**: ${metrics.exceedsThreshold ? '⚠️ Exceeds Threshold' : '✅ Within Threshold'}`);
    lines.push('');

    if (this.changes.size > 0) {
      lines.push('## Changes by Type');
      const byType = this.groupChangesByType();
      for (const [type, changes] of byType.entries()) {
        const totalLines = changes.reduce((sum, c) => sum + getTotalLines(c), 0);
        const category = isCounted(type) ? 'counted' : 'non-counted';
        lines.push(`- **${type}** (${category}): ${changes.length} changes, ${totalLines} lines`);
      }
    }

    return lines.join('\n');
  }

  /**
   * Add a change record
   */
  addChange(change: BalanceChange): void {
    this.changes.set(change.id, change);
  }

  /**
   * Remove a change record
   */
  removeChange(changeId: string): void {
    this.changes.delete(changeId);
  }

  /**
   * Get all changes
   */
  getChanges(): readonly BalanceChange[] {
    return Object.freeze([...this.changes.values()]);
  }

  /**
   * Clear all changes
   */
  clear(): void {
    this.changes.clear();
  }

  /**
   * Infer change type from file path
   */
  inferChangeType(filePath: string): BalanceChangeType {
    const lower = filePath.toLowerCase();

    // Test files
    if (
      lower.includes('.test.') ||
      lower.includes('.spec.') ||
      lower.includes('__tests__') ||
      lower.includes('__mocks__')
    ) {
      return 'test';
    }

    // CI/CD
    if (
      lower.includes('.github/') ||
      lower.includes('.gitlab-ci') ||
      lower.includes('azure-pipelines') ||
      lower.includes('jenkinsfile')
    ) {
      return 'ci';
    }

    // Documentation
    if (
      lower.endsWith('.md') ||
      lower.includes('/docs/') ||
      lower.endsWith('.rst') ||
      lower.endsWith('.txt')
    ) {
      return 'docs';
    }

    // Configuration
    if (
      lower.endsWith('.json') ||
      lower.endsWith('.yml') ||
      lower.endsWith('.yaml') ||
      lower.endsWith('.toml') ||
      lower.includes('config') ||
      lower.startsWith('.') ||
      lower.includes('rc.') ||
      lower.includes('.config.')
    ) {
      return 'config';
    }

    // Build/Packaging
    if (
      lower.includes('dockerfile') ||
      lower.includes('makefile') ||
      lower.includes('package.json') ||
      lower.includes('package-lock.json') ||
      lower.includes('pnpm-lock.yaml') ||
      lower.includes('yarn.lock') ||
      lower.includes('tsconfig') ||
      lower.includes('webpack') ||
      lower.includes('rollup') ||
      lower.includes('vite.config')
    ) {
      return 'build';
    }

    // Default to feature for source files
    return 'feature';
  }

  // Private helpers

  private groupChangesByType(): Map<BalanceChangeType, BalanceChange[]> {
    const byType = new Map<BalanceChangeType, BalanceChange[]>();

    for (const change of this.changes.values()) {
      const existing = byType.get(change.type) ?? [];
      existing.push(change);
      byType.set(change.type, existing);
    }

    return byType;
  }

  private generateRecommendations(metrics: BalanceMetrics): readonly string[] {
    const recommendations: string[] = [];

    if (metrics.exceedsThreshold) {
      if (metrics.nonCountedLines > metrics.countedLines * 0.2) {
        recommendations.push('Consider batching configuration changes separately from feature work');
      }
      if (metrics.countedChanges === 0) {
        recommendations.push('No counted changes detected. Ensure feature/bugfix work is included');
      }
    }

    return Object.freeze(recommendations);
  }
}

/**
 * Create a BalanceRuleEngine instance
 *
 * @param config - Optional configuration
 * @returns IBalanceRuleEngine instance
 */
export function createBalanceRuleEngine(config?: BalanceConfig): IBalanceRuleEngine {
  return new BalanceRuleEngine(config);
}
