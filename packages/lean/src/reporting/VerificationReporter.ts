/**
 * @fileoverview Verification report generator
 * @module @nahisaho/musubix-lean/reporting
 * @traceability REQ-LEAN-FEEDBACK-001 to REQ-LEAN-FEEDBACK-003
 */

import type {
  VerificationReport,
  VerificationResult,
  LeanTheorem,
  LeanProof,
  ReportFormat,
  ReportStatistics,
  ProofFeedback,
  ProofState,
} from '../types.js';

/**
 * Verification result status
 */
export type VerificationStatus = 'proved' | 'disproved' | 'timeout' | 'error' | 'incomplete';

/**
 * Detailed verification result entry
 */
export interface VerificationResultEntry {
  theorem: LeanTheorem;
  status: VerificationStatus;
  proof?: LeanProof;
  error?: string;
  duration: number;
  feedback?: ProofFeedback;
}

/**
 * Generates comprehensive verification reports
 * @traceability REQ-LEAN-FEEDBACK-001
 */
export class VerificationReporter {
  private results: VerificationResultEntry[] = [];
  private startTime: number = Date.now();

  /**
   * Add a verification result
   */
  addResult(entry: VerificationResultEntry): void {
    this.results.push(entry);
  }

  /**
   * Generate verification report
   * @traceability REQ-LEAN-FEEDBACK-002
   */
  generate(): VerificationReport {
    const totalDuration = Date.now() - this.startTime;
    const statistics = this.calculateStatistics();

    return {
      id: this.generateReportId(),
      timestamp: new Date().toISOString(),
      results: this.results.map((entry) => this.convertToVerificationResult(entry)),
      statistics,
      executionDetails: {
        totalDuration,
        leanVersion: '', // Would be populated by LeanRunner
        systemInfo: this.getSystemInfo(),
      },
    };
  }

  /**
   * Export report in specified format
   * @traceability REQ-LEAN-FEEDBACK-003
   */
  export(format: ReportFormat): string {
    const report = this.generate();

    switch (format) {
      case 'json':
        return JSON.stringify(report, null, 2);
      case 'markdown':
        return this.toMarkdown(report);
      case 'html':
        return this.toHtml(report);
      case 'csv':
        return this.toCsv(report);
      default:
        return JSON.stringify(report, null, 2);
    }
  }

  /**
   * Convert entry to VerificationResult
   */
  private convertToVerificationResult(entry: VerificationResultEntry): VerificationResult {
    return {
      theoremId: entry.theorem.id,
      status: entry.status === 'proved' ? 'proved' : entry.status === 'error' ? 'error' : 'incomplete',
      proof: entry.proof,
      errors: entry.error ? [entry.error] : [],
      warnings: [],
      duration: entry.duration,
      feedback: entry.feedback,
    };
  }

  /**
   * Calculate statistics from results
   */
  private calculateStatistics(): ReportStatistics {
    const proved = this.results.filter((r) => r.status === 'proved').length;
    const failed = this.results.filter(
      (r) => r.status === 'disproved' || r.status === 'error'
    ).length;
    const incomplete = this.results.filter(
      (r) => r.status === 'incomplete' || r.status === 'timeout'
    ).length;

    const totalTime = this.results.reduce((sum, r) => sum + r.duration, 0);
    const avgTime = this.results.length > 0 ? totalTime / this.results.length : 0;

    return {
      totalTheorems: this.results.length,
      provedCount: proved,
      failedCount: failed,
      incompleteCount: incomplete,
      averageProofTime: avgTime,
      totalTime,
    };
  }

  /**
   * Generate unique report ID
   */
  private generateReportId(): string {
    const timestamp = Date.now().toString(36);
    const random = Math.random().toString(36).substring(2, 8);
    return `RPT-${timestamp}-${random}`;
  }

  /**
   * Get system information
   */
  private getSystemInfo(): Record<string, string> {
    return {
      platform: typeof process !== 'undefined' ? process.platform : 'unknown',
      nodeVersion: typeof process !== 'undefined' ? process.version : 'unknown',
      musubixVersion: '2.0.0-alpha.1',
    };
  }

  /**
   * Convert report to Markdown format
   */
  private toMarkdown(report: VerificationReport): string {
    const lines: string[] = [];

    lines.push('# Verification Report');
    lines.push('');
    lines.push(`**Report ID**: ${report.id}`);
    lines.push(`**Generated**: ${report.timestamp}`);
    lines.push('');

    // Statistics
    lines.push('## Summary');
    lines.push('');
    lines.push('| Metric | Value |');
    lines.push('|--------|-------|');
    lines.push(`| Total Theorems | ${report.statistics.totalTheorems} |`);
    lines.push(`| Proved | ${report.statistics.provedCount} |`);
    lines.push(`| Failed | ${report.statistics.failedCount} |`);
    lines.push(`| Incomplete | ${report.statistics.incompleteCount} |`);
    lines.push(`| Avg Proof Time | ${report.statistics.averageProofTime.toFixed(2)}ms |`);
    lines.push(`| Total Time | ${report.statistics.totalTime.toFixed(2)}ms |`);
    lines.push('');

    // Pass rate
    const passRate = report.statistics.totalTheorems > 0
      ? ((report.statistics.provedCount / report.statistics.totalTheorems) * 100).toFixed(1)
      : '0.0';
    lines.push(`**Pass Rate**: ${passRate}%`);
    lines.push('');

    // Results
    lines.push('## Results');
    lines.push('');

    for (const result of report.results) {
      const statusIcon = result.status === 'proved' ? '✅' : result.status === 'error' ? '❌' : '⚠️';
      lines.push(`### ${statusIcon} ${result.theoremId}`);
      lines.push('');
      lines.push(`- **Status**: ${result.status}`);
      lines.push(`- **Duration**: ${result.duration}ms`);

      if (result.proof) {
        lines.push('');
        lines.push('**Proof**:');
        lines.push('```lean');
        lines.push(result.proof.leanCode);
        lines.push('```');
      }

      if (result.errors.length > 0) {
        lines.push('');
        lines.push('**Errors**:');
        for (const error of result.errors) {
          lines.push(`- ${error}`);
        }
      }

      if (result.feedback) {
        lines.push('');
        lines.push('**Feedback**:');
        for (const guidance of result.feedback.guidance) {
          lines.push(`- ${guidance}`);
        }
      }

      lines.push('');
    }

    return lines.join('\n');
  }

  /**
   * Convert report to HTML format
   */
  private toHtml(report: VerificationReport): string {
    const passRate = report.statistics.totalTheorems > 0
      ? ((report.statistics.provedCount / report.statistics.totalTheorems) * 100).toFixed(1)
      : '0.0';

    return `<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <title>Verification Report ${report.id}</title>
  <style>
    body { font-family: system-ui, sans-serif; max-width: 900px; margin: 2rem auto; padding: 0 1rem; }
    h1, h2, h3 { color: #1a1a1a; }
    .summary { background: #f5f5f5; padding: 1rem; border-radius: 8px; margin: 1rem 0; }
    .stat { display: inline-block; margin: 0.5rem 1rem; }
    .stat-value { font-size: 1.5rem; font-weight: bold; }
    .stat-label { color: #666; font-size: 0.9rem; }
    .result { border: 1px solid #ddd; border-radius: 8px; padding: 1rem; margin: 1rem 0; }
    .result.proved { border-color: #22c55e; }
    .result.error { border-color: #ef4444; }
    .result.incomplete { border-color: #f59e0b; }
    pre { background: #1a1a1a; color: #e5e5e5; padding: 1rem; border-radius: 4px; overflow-x: auto; }
    .pass-rate { font-size: 2rem; font-weight: bold; color: ${parseFloat(passRate) >= 80 ? '#22c55e' : parseFloat(passRate) >= 50 ? '#f59e0b' : '#ef4444'}; }
  </style>
</head>
<body>
  <h1>Verification Report</h1>
  <p><strong>ID:</strong> ${report.id}</p>
  <p><strong>Generated:</strong> ${report.timestamp}</p>

  <div class="summary">
    <h2>Summary</h2>
    <div class="stat"><div class="stat-value">${report.statistics.totalTheorems}</div><div class="stat-label">Total</div></div>
    <div class="stat"><div class="stat-value">${report.statistics.provedCount}</div><div class="stat-label">Proved</div></div>
    <div class="stat"><div class="stat-value">${report.statistics.failedCount}</div><div class="stat-label">Failed</div></div>
    <div class="stat"><div class="stat-value">${report.statistics.incompleteCount}</div><div class="stat-label">Incomplete</div></div>
    <div class="stat"><div class="pass-rate">${passRate}%</div><div class="stat-label">Pass Rate</div></div>
  </div>

  <h2>Results</h2>
  ${report.results.map((r) => `
  <div class="result ${r.status}">
    <h3>${r.status === 'proved' ? '✅' : r.status === 'error' ? '❌' : '⚠️'} ${r.theoremId}</h3>
    <p><strong>Status:</strong> ${r.status} | <strong>Duration:</strong> ${r.duration}ms</p>
    ${r.proof ? `<pre>${this.escapeHtml(r.proof.leanCode)}</pre>` : ''}
    ${r.errors.length > 0 ? `<p><strong>Errors:</strong> ${r.errors.join(', ')}</p>` : ''}
    ${r.feedback ? `<p><strong>Feedback:</strong> ${r.feedback.guidance.join('; ')}</p>` : ''}
  </div>
  `).join('\n')}
</body>
</html>`;
  }

  /**
   * Escape HTML special characters
   */
  private escapeHtml(text: string): string {
    return text
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&#039;');
  }

  /**
   * Convert report to CSV format
   */
  private toCsv(report: VerificationReport): string {
    const lines: string[] = [];

    // Header
    lines.push('Theorem ID,Status,Duration (ms),Errors');

    // Data rows
    for (const result of report.results) {
      const errors = result.errors.join('; ').replace(/"/g, '""');
      lines.push(
        `"${result.theoremId}","${result.status}",${result.duration},"${errors}"`
      );
    }

    return lines.join('\n');
  }

  /**
   * Clear all results
   */
  clear(): void {
    this.results = [];
    this.startTime = Date.now();
  }

  /**
   * Get current result count
   */
  getResultCount(): number {
    return this.results.length;
  }

  /**
   * Provide user-friendly feedback for proof failures
   * @traceability REQ-LEAN-FEEDBACK-002
   */
  static generateUserFeedback(state: ProofState, attemptedTactics: string[]): string[] {
    const feedback: string[] = [];

    if (state.goals.length === 0) {
      feedback.push('All goals have been proved!');
      return feedback;
    }

    const currentGoal = state.goals[state.currentGoal];
    if (currentGoal) {
      feedback.push(`Current goal: ${currentGoal.type}`);
      feedback.push('');

      if (attemptedTactics.length > 0) {
        feedback.push(`Attempted tactics: ${attemptedTactics.join(', ')}`);
      }

      // Goal-specific suggestions
      if (currentGoal.leanCode.includes('=')) {
        feedback.push('Hint: This is an equality. Try "rfl" for reflexivity or "simp" to simplify.');
      }

      if (currentGoal.leanCode.includes('True')) {
        feedback.push('Hint: Goal is "True". Use "trivial" tactic.');
      }

      if (state.hypotheses.length > 0) {
        feedback.push('');
        feedback.push('Available hypotheses:');
        for (const hyp of state.hypotheses) {
          feedback.push(`  ${hyp.name} : ${hyp.type}`);
        }
      }
    }

    return feedback;
  }
}
