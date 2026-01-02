/**
 * Coverage Reporter
 * 
 * Generates and reports test coverage metrics
 * 
 * @packageDocumentation
 * @module codegen/coverage-reporter
 * 
 * @see REQ-QUA-002 - Coverage Reporting
 * @see Article VII - Quality Assurance Standards
 */

/**
 * Coverage metric type
 */
export type CoverageMetricType = 'statements' | 'branches' | 'functions' | 'lines';

/**
 * Coverage threshold status
 */
export type ThresholdStatus = 'pass' | 'warn' | 'fail';

/**
 * Coverage data for a file
 */
export interface FileCoverage {
  /** File path */
  path: string;
  /** Statement coverage */
  statements: CoverageMetric;
  /** Branch coverage */
  branches: CoverageMetric;
  /** Function coverage */
  functions: CoverageMetric;
  /** Line coverage */
  lines: CoverageMetric;
  /** Uncovered lines */
  uncoveredLines: number[];
  /** Uncovered branches */
  uncoveredBranches: BranchInfo[];
  /** Uncovered functions */
  uncoveredFunctions: string[];
}

/**
 * Coverage metric
 */
export interface CoverageMetric {
  /** Total count */
  total: number;
  /** Covered count */
  covered: number;
  /** Skipped count */
  skipped: number;
  /** Percentage (0-100) */
  percentage: number;
}

/**
 * Branch info
 */
export interface BranchInfo {
  /** Line number */
  line: number;
  /** Branch type */
  type: 'if' | 'switch' | 'ternary' | 'logical';
  /** Branch index */
  index: number;
  /** Is covered */
  covered: boolean;
}

/**
 * Coverage summary
 */
export interface CoverageSummary {
  /** Total files */
  totalFiles: number;
  /** Covered files */
  coveredFiles: number;
  /** Statement coverage */
  statements: CoverageMetric;
  /** Branch coverage */
  branches: CoverageMetric;
  /** Function coverage */
  functions: CoverageMetric;
  /** Line coverage */
  lines: CoverageMetric;
  /** Overall percentage */
  overallPercentage: number;
}

/**
 * Coverage threshold
 */
export interface CoverageThreshold {
  /** Metric type */
  metric: CoverageMetricType;
  /** Minimum percentage to pass */
  pass: number;
  /** Minimum percentage to warn */
  warn: number;
}

/**
 * Coverage report
 */
export interface CoverageReport {
  /** Report timestamp */
  timestamp: Date;
  /** Project name */
  projectName: string;
  /** Summary */
  summary: CoverageSummary;
  /** File coverages */
  files: FileCoverage[];
  /** Threshold results */
  thresholdResults: ThresholdResult[];
  /** Trends */
  trends?: CoverageTrend[];
  /** Recommendations */
  recommendations: string[];
}

/**
 * Threshold result
 */
export interface ThresholdResult {
  /** Metric type */
  metric: CoverageMetricType;
  /** Current percentage */
  current: number;
  /** Threshold */
  threshold: CoverageThreshold;
  /** Status */
  status: ThresholdStatus;
  /** Gap (if failing) */
  gap?: number;
}

/**
 * Coverage trend
 */
export interface CoverageTrend {
  /** Date */
  date: Date;
  /** Metric type */
  metric: CoverageMetricType;
  /** Percentage */
  percentage: number;
  /** Change from previous */
  change: number;
}

/**
 * Coverage report format
 */
export type ReportFormat = 'text' | 'json' | 'html' | 'lcov' | 'cobertura' | 'markdown';

/**
 * Coverage reporter config
 */
export interface CoverageReporterConfig {
  /** Project name */
  projectName: string;
  /** Thresholds */
  thresholds: CoverageThreshold[];
  /** Report formats */
  formats: ReportFormat[];
  /** Output directory */
  outputDir: string;
  /** Include file details */
  includeFileDetails: boolean;
  /** Show uncovered lines */
  showUncoveredLines: boolean;
  /** Track trends */
  trackTrends: boolean;
  /** Previous coverage (for trends) */
  previousCoverage?: CoverageSummary;
}

/**
 * Default configuration
 */
export const DEFAULT_REPORTER_CONFIG: CoverageReporterConfig = {
  projectName: 'Project',
  thresholds: [
    { metric: 'statements', pass: 80, warn: 60 },
    { metric: 'branches', pass: 80, warn: 60 },
    { metric: 'functions', pass: 80, warn: 60 },
    { metric: 'lines', pass: 80, warn: 60 },
  ],
  formats: ['text', 'json'],
  outputDir: 'coverage',
  includeFileDetails: true,
  showUncoveredLines: true,
  trackTrends: false,
};

/**
 * Coverage Reporter
 */
export class CoverageReporter {
  private config: CoverageReporterConfig;

  constructor(config?: Partial<CoverageReporterConfig>) {
    this.config = { ...DEFAULT_REPORTER_CONFIG, ...config };
  }

  /**
   * Generate coverage report from raw data
   */
  generateReport(coverageData: FileCoverage[]): CoverageReport {
    const summary = this.calculateSummary(coverageData);
    const thresholdResults = this.checkThresholds(summary);
    const recommendations = this.generateRecommendations(coverageData, summary, thresholdResults);
    const trends = this.config.trackTrends
      ? this.calculateTrends(summary)
      : undefined;

    return {
      timestamp: new Date(),
      projectName: this.config.projectName,
      summary,
      files: coverageData,
      thresholdResults,
      trends,
      recommendations,
    };
  }

  /**
   * Format report
   */
  formatReport(report: CoverageReport, format: ReportFormat): string {
    switch (format) {
      case 'text':
        return this.formatText(report);
      case 'json':
        return this.formatJson(report);
      case 'html':
        return this.formatHtml(report);
      case 'lcov':
        return this.formatLcov(report);
      case 'cobertura':
        return this.formatCobertura(report);
      case 'markdown':
        return this.formatMarkdown(report);
      default:
        return this.formatText(report);
    }
  }

  /**
   * Get all formatted reports
   */
  getAllFormattedReports(report: CoverageReport): Map<ReportFormat, string> {
    const reports = new Map<ReportFormat, string>();
    
    for (const format of this.config.formats) {
      reports.set(format, this.formatReport(report, format));
    }

    return reports;
  }

  /**
   * Parse coverage from various formats
   */
  parseCoverage(data: string, format: 'istanbul' | 'lcov' | 'cobertura'): FileCoverage[] {
    switch (format) {
      case 'istanbul':
        return this.parseIstanbul(data);
      case 'lcov':
        return this.parseLcov(data);
      case 'cobertura':
        return this.parseCobertura(data);
      default:
        throw new Error(`Unknown format: ${format}`);
    }
  }

  /**
   * Calculate summary
   */
  private calculateSummary(files: FileCoverage[]): CoverageSummary {
    const totals = {
      statements: { total: 0, covered: 0, skipped: 0 },
      branches: { total: 0, covered: 0, skipped: 0 },
      functions: { total: 0, covered: 0, skipped: 0 },
      lines: { total: 0, covered: 0, skipped: 0 },
    };

    let coveredFiles = 0;

    for (const file of files) {
      // Aggregate metrics
      totals.statements.total += file.statements.total;
      totals.statements.covered += file.statements.covered;
      totals.statements.skipped += file.statements.skipped;

      totals.branches.total += file.branches.total;
      totals.branches.covered += file.branches.covered;
      totals.branches.skipped += file.branches.skipped;

      totals.functions.total += file.functions.total;
      totals.functions.covered += file.functions.covered;
      totals.functions.skipped += file.functions.skipped;

      totals.lines.total += file.lines.total;
      totals.lines.covered += file.lines.covered;
      totals.lines.skipped += file.lines.skipped;

      // Check if file is covered
      if (file.statements.percentage > 0) {
        coveredFiles++;
      }
    }

    const statements = this.createMetric(totals.statements);
    const branches = this.createMetric(totals.branches);
    const functions = this.createMetric(totals.functions);
    const lines = this.createMetric(totals.lines);

    const overallPercentage = (
      statements.percentage +
      branches.percentage +
      functions.percentage +
      lines.percentage
    ) / 4;

    return {
      totalFiles: files.length,
      coveredFiles,
      statements,
      branches,
      functions,
      lines,
      overallPercentage: Math.round(overallPercentage * 100) / 100,
    };
  }

  /**
   * Create metric from totals
   */
  private createMetric(totals: { total: number; covered: number; skipped: number }): CoverageMetric {
    const percentage = totals.total > 0
      ? (totals.covered / totals.total) * 100
      : 0;

    return {
      total: totals.total,
      covered: totals.covered,
      skipped: totals.skipped,
      percentage: Math.round(percentage * 100) / 100,
    };
  }

  /**
   * Check thresholds
   */
  private checkThresholds(summary: CoverageSummary): ThresholdResult[] {
    const results: ThresholdResult[] = [];

    for (const threshold of this.config.thresholds) {
      const current = summary[threshold.metric].percentage;
      let status: ThresholdStatus;
      let gap: number | undefined;

      if (current >= threshold.pass) {
        status = 'pass';
      } else if (current >= threshold.warn) {
        status = 'warn';
        gap = threshold.pass - current;
      } else {
        status = 'fail';
        gap = threshold.pass - current;
      }

      results.push({
        metric: threshold.metric,
        current,
        threshold,
        status,
        gap,
      });
    }

    return results;
  }

  /**
   * Calculate trends
   */
  private calculateTrends(current: CoverageSummary): CoverageTrend[] {
    const trends: CoverageTrend[] = [];
    const previous = this.config.previousCoverage;

    const metrics: CoverageMetricType[] = ['statements', 'branches', 'functions', 'lines'];

    for (const metric of metrics) {
      const currentValue = current[metric].percentage;
      const previousValue = previous ? previous[metric].percentage : currentValue;
      const change = currentValue - previousValue;

      trends.push({
        date: new Date(),
        metric,
        percentage: currentValue,
        change: Math.round(change * 100) / 100,
      });
    }

    return trends;
  }

  /**
   * Generate recommendations
   */
  private generateRecommendations(
    files: FileCoverage[],
    summary: CoverageSummary,
    thresholds: ThresholdResult[]
  ): string[] {
    const recommendations: string[] = [];

    // Threshold-based recommendations
    const failingMetrics = thresholds.filter((t) => t.status === 'fail');
    if (failingMetrics.length > 0) {
      for (const metric of failingMetrics) {
        recommendations.push(
          `Increase ${metric.metric} coverage by ${metric.gap?.toFixed(1)}% to meet threshold`
        );
      }
    }

    // File-based recommendations
    const lowCoverageFiles = files
      .filter((f) => f.statements.percentage < 50)
      .sort((a, b) => a.statements.percentage - b.statements.percentage)
      .slice(0, 5);

    if (lowCoverageFiles.length > 0) {
      recommendations.push(
        `Focus on improving coverage in: ${lowCoverageFiles.map((f) => f.path).join(', ')}`
      );
    }

    // Branch-based recommendations
    if (summary.branches.percentage < summary.statements.percentage - 20) {
      recommendations.push(
        'Branch coverage is significantly lower than statement coverage - add more conditional tests'
      );
    }

    // Function-based recommendations
    const filesWithUncoveredFunctions = files.filter(
      (f) => f.uncoveredFunctions.length > 0
    );
    if (filesWithUncoveredFunctions.length > 0) {
      recommendations.push(
        `${filesWithUncoveredFunctions.length} files have uncovered functions - add tests for them`
      );
    }

    // Overall recommendations
    if (summary.overallPercentage >= 80) {
      recommendations.push('Coverage is good! Consider adding edge case tests');
    } else if (summary.overallPercentage >= 60) {
      recommendations.push('Coverage is moderate. Prioritize critical paths');
    } else {
      recommendations.push('Coverage is low. Start with unit tests for core functionality');
    }

    return recommendations;
  }

  /**
   * Format as text
   */
  private formatText(report: CoverageReport): string {
    const lines: string[] = [];
    const width = 80;

    lines.push('='.repeat(width));
    lines.push(`COVERAGE REPORT - ${report.projectName}`);
    lines.push(`Generated: ${report.timestamp.toISOString()}`);
    lines.push('='.repeat(width));
    lines.push('');

    // Summary
    lines.push('SUMMARY');
    lines.push('-'.repeat(width));
    lines.push(`Files:      ${report.summary.coveredFiles}/${report.summary.totalFiles}`);
    lines.push(`Statements: ${this.formatMetricBar(report.summary.statements)}`);
    lines.push(`Branches:   ${this.formatMetricBar(report.summary.branches)}`);
    lines.push(`Functions:  ${this.formatMetricBar(report.summary.functions)}`);
    lines.push(`Lines:      ${this.formatMetricBar(report.summary.lines)}`);
    lines.push('');
    lines.push(`Overall:    ${report.summary.overallPercentage}%`);
    lines.push('');

    // Threshold results
    lines.push('THRESHOLD STATUS');
    lines.push('-'.repeat(width));
    for (const result of report.thresholdResults) {
      const icon = result.status === 'pass' ? '✓' :
                   result.status === 'warn' ? '⚠' : '✗';
      const status = result.status.toUpperCase().padEnd(4);
      lines.push(`${icon} ${result.metric.padEnd(12)} ${result.current.toFixed(1)}% ${status}`);
    }
    lines.push('');

    // Trends
    if (report.trends) {
      lines.push('TRENDS');
      lines.push('-'.repeat(width));
      for (const trend of report.trends) {
        const arrow = trend.change > 0 ? '↑' : trend.change < 0 ? '↓' : '→';
        const change = trend.change !== 0 ? `${trend.change > 0 ? '+' : ''}${trend.change.toFixed(1)}%` : '';
        lines.push(`${trend.metric.padEnd(12)} ${trend.percentage.toFixed(1)}% ${arrow} ${change}`);
      }
      lines.push('');
    }

    // File details
    if (this.config.includeFileDetails) {
      lines.push('FILE COVERAGE');
      lines.push('-'.repeat(width));
      for (const file of report.files.slice(0, 20)) {
        const pct = file.statements.percentage.toFixed(1).padStart(5);
        lines.push(`${pct}% ${file.path}`);
        
        if (this.config.showUncoveredLines && file.uncoveredLines.length > 0) {
          const uncovered = file.uncoveredLines.slice(0, 10).join(', ');
          const more = file.uncoveredLines.length > 10
            ? ` (+${file.uncoveredLines.length - 10} more)`
            : '';
          lines.push(`       Uncovered lines: ${uncovered}${more}`);
        }
      }
      if (report.files.length > 20) {
        lines.push(`... and ${report.files.length - 20} more files`);
      }
      lines.push('');
    }

    // Recommendations
    lines.push('RECOMMENDATIONS');
    lines.push('-'.repeat(width));
    for (const rec of report.recommendations) {
      lines.push(`• ${rec}`);
    }
    lines.push('');

    lines.push('='.repeat(width));

    return lines.join('\n');
  }

  /**
   * Format metric as bar
   */
  private formatMetricBar(metric: CoverageMetric): string {
    const barWidth = 30;
    const filled = Math.round((metric.percentage / 100) * barWidth);
    const bar = '█'.repeat(filled) + '░'.repeat(barWidth - filled);
    return `${bar} ${metric.covered}/${metric.total} (${metric.percentage}%)`;
  }

  /**
   * Format as JSON
   */
  private formatJson(report: CoverageReport): string {
    return JSON.stringify(report, null, 2);
  }

  /**
   * Format as HTML
   */
  private formatHtml(report: CoverageReport): string {
    const statusColor = (status: ThresholdStatus): string => {
      switch (status) {
        case 'pass': return '#4caf50';
        case 'warn': return '#ff9800';
        case 'fail': return '#f44336';
      }
    };

    return `<!DOCTYPE html>
<html>
<head>
  <title>Coverage Report - ${report.projectName}</title>
  <style>
    body { font-family: -apple-system, BlinkMacSystemFont, sans-serif; margin: 20px; }
    h1 { color: #333; }
    .summary { display: grid; grid-template-columns: repeat(4, 1fr); gap: 20px; margin: 20px 0; }
    .metric { background: #f5f5f5; padding: 20px; border-radius: 8px; }
    .metric h3 { margin: 0 0 10px 0; }
    .metric .value { font-size: 2em; font-weight: bold; }
    .progress { background: #e0e0e0; height: 8px; border-radius: 4px; margin-top: 10px; }
    .progress-bar { height: 100%; border-radius: 4px; }
    .threshold { display: flex; align-items: center; padding: 10px; border-radius: 4px; margin: 5px 0; }
    .threshold.pass { background: #e8f5e9; }
    .threshold.warn { background: #fff3e0; }
    .threshold.fail { background: #ffebee; }
    table { width: 100%; border-collapse: collapse; margin: 20px 0; }
    th, td { text-align: left; padding: 10px; border-bottom: 1px solid #ddd; }
    th { background: #f5f5f5; }
    .recommendation { padding: 10px; background: #e3f2fd; margin: 5px 0; border-radius: 4px; }
  </style>
</head>
<body>
  <h1>Coverage Report - ${report.projectName}</h1>
  <p>Generated: ${report.timestamp.toISOString()}</p>
  
  <div class="summary">
    <div class="metric">
      <h3>Statements</h3>
      <div class="value">${report.summary.statements.percentage}%</div>
      <div class="progress"><div class="progress-bar" style="width: ${report.summary.statements.percentage}%; background: #2196f3;"></div></div>
    </div>
    <div class="metric">
      <h3>Branches</h3>
      <div class="value">${report.summary.branches.percentage}%</div>
      <div class="progress"><div class="progress-bar" style="width: ${report.summary.branches.percentage}%; background: #9c27b0;"></div></div>
    </div>
    <div class="metric">
      <h3>Functions</h3>
      <div class="value">${report.summary.functions.percentage}%</div>
      <div class="progress"><div class="progress-bar" style="width: ${report.summary.functions.percentage}%; background: #ff9800;"></div></div>
    </div>
    <div class="metric">
      <h3>Lines</h3>
      <div class="value">${report.summary.lines.percentage}%</div>
      <div class="progress"><div class="progress-bar" style="width: ${report.summary.lines.percentage}%; background: #4caf50;"></div></div>
    </div>
  </div>

  <h2>Threshold Status</h2>
  ${report.thresholdResults.map((r) => `
    <div class="threshold ${r.status}">
      <strong>${r.metric}</strong>: ${r.current}% 
      (threshold: ${r.threshold.pass}%) - 
      <span style="color: ${statusColor(r.status)}">${r.status.toUpperCase()}</span>
      ${r.gap ? ` (${r.gap.toFixed(1)}% to pass)` : ''}
    </div>
  `).join('')}

  <h2>File Coverage</h2>
  <table>
    <thead>
      <tr>
        <th>File</th>
        <th>Statements</th>
        <th>Branches</th>
        <th>Functions</th>
        <th>Lines</th>
      </tr>
    </thead>
    <tbody>
      ${report.files.map((f) => `
        <tr>
          <td>${f.path}</td>
          <td>${f.statements.percentage}%</td>
          <td>${f.branches.percentage}%</td>
          <td>${f.functions.percentage}%</td>
          <td>${f.lines.percentage}%</td>
        </tr>
      `).join('')}
    </tbody>
  </table>

  <h2>Recommendations</h2>
  ${report.recommendations.map((r) => `
    <div class="recommendation">${r}</div>
  `).join('')}
</body>
</html>`;
  }

  /**
   * Format as LCOV
   */
  private formatLcov(report: CoverageReport): string {
    const lines: string[] = [];

    for (const file of report.files) {
      lines.push(`TN:`);
      lines.push(`SF:${file.path}`);
      
      // Function coverage
      lines.push(`FNF:${file.functions.total}`);
      lines.push(`FNH:${file.functions.covered}`);
      
      // Line coverage
      lines.push(`LF:${file.lines.total}`);
      lines.push(`LH:${file.lines.covered}`);
      
      // Branch coverage
      lines.push(`BRF:${file.branches.total}`);
      lines.push(`BRH:${file.branches.covered}`);
      
      lines.push('end_of_record');
    }

    return lines.join('\n');
  }

  /**
   * Format as Cobertura XML
   */
  private formatCobertura(report: CoverageReport): string {
    const lineRate = report.summary.lines.percentage / 100;
    const branchRate = report.summary.branches.percentage / 100;

    return `<?xml version="1.0" ?>
<!DOCTYPE coverage SYSTEM "http://cobertura.sourceforge.net/xml/coverage-04.dtd">
<coverage version="1.0" timestamp="${report.timestamp.getTime()}" lines-valid="${report.summary.lines.total}" lines-covered="${report.summary.lines.covered}" line-rate="${lineRate.toFixed(4)}" branches-valid="${report.summary.branches.total}" branches-covered="${report.summary.branches.covered}" branch-rate="${branchRate.toFixed(4)}">
  <packages>
    <package name="${report.projectName}" line-rate="${lineRate.toFixed(4)}" branch-rate="${branchRate.toFixed(4)}">
      <classes>
${report.files.map((f) => `        <class name="${f.path}" filename="${f.path}" line-rate="${(f.lines.percentage / 100).toFixed(4)}" branch-rate="${(f.branches.percentage / 100).toFixed(4)}">
          <lines>
${Array.from({ length: f.lines.total }, (_, i) => `            <line number="${i + 1}" hits="${f.uncoveredLines.includes(i + 1) ? 0 : 1}"/>`).join('\n')}
          </lines>
        </class>`).join('\n')}
      </classes>
    </package>
  </packages>
</coverage>`;
  }

  /**
   * Format as Markdown
   */
  private formatMarkdown(report: CoverageReport): string {
    const lines: string[] = [];

    lines.push(`# Coverage Report - ${report.projectName}`);
    lines.push('');
    lines.push(`> Generated: ${report.timestamp.toISOString()}`);
    lines.push('');

    // Summary
    lines.push('## Summary');
    lines.push('');
    lines.push('| Metric | Covered | Total | Percentage |');
    lines.push('|--------|---------|-------|------------|');
    lines.push(`| Statements | ${report.summary.statements.covered} | ${report.summary.statements.total} | ${report.summary.statements.percentage}% |`);
    lines.push(`| Branches | ${report.summary.branches.covered} | ${report.summary.branches.total} | ${report.summary.branches.percentage}% |`);
    lines.push(`| Functions | ${report.summary.functions.covered} | ${report.summary.functions.total} | ${report.summary.functions.percentage}% |`);
    lines.push(`| Lines | ${report.summary.lines.covered} | ${report.summary.lines.total} | ${report.summary.lines.percentage}% |`);
    lines.push('');
    lines.push(`**Overall Coverage: ${report.summary.overallPercentage}%**`);
    lines.push('');

    // Thresholds
    lines.push('## Threshold Status');
    lines.push('');
    for (const result of report.thresholdResults) {
      const icon = result.status === 'pass' ? '✅' :
                   result.status === 'warn' ? '⚠️' : '❌';
      lines.push(`- ${icon} **${result.metric}**: ${result.current}% (threshold: ${result.threshold.pass}%)`);
    }
    lines.push('');

    // Trends
    if (report.trends) {
      lines.push('## Trends');
      lines.push('');
      lines.push('| Metric | Current | Change |');
      lines.push('|--------|---------|--------|');
      for (const trend of report.trends) {
        const arrow = trend.change > 0 ? '📈' : trend.change < 0 ? '📉' : '➡️';
        const change = trend.change !== 0 
          ? `${trend.change > 0 ? '+' : ''}${trend.change.toFixed(1)}%`
          : 'No change';
        lines.push(`| ${trend.metric} | ${trend.percentage}% | ${arrow} ${change} |`);
      }
      lines.push('');
    }

    // File Coverage
    if (this.config.includeFileDetails) {
      lines.push('## File Coverage');
      lines.push('');
      lines.push('| File | Statements | Branches | Functions | Lines |');
      lines.push('|------|------------|----------|-----------|-------|');
      for (const file of report.files) {
        lines.push(`| ${file.path} | ${file.statements.percentage}% | ${file.branches.percentage}% | ${file.functions.percentage}% | ${file.lines.percentage}% |`);
      }
      lines.push('');
    }

    // Recommendations
    lines.push('## Recommendations');
    lines.push('');
    for (const rec of report.recommendations) {
      lines.push(`- ${rec}`);
    }

    return lines.join('\n');
  }

  /**
   * Parse Istanbul JSON coverage
   */
  private parseIstanbul(data: string): FileCoverage[] {
    const json = JSON.parse(data);
    const files: FileCoverage[] = [];

    for (const [path, coverage] of Object.entries(json)) {
      const cov = coverage as Record<string, unknown>;
      files.push(this.parseIstanbulFile(path, cov));
    }

    return files;
  }

  /**
   * Parse Istanbul file coverage
   */
  private parseIstanbulFile(path: string, coverage: Record<string, unknown>): FileCoverage {
    const s = coverage.s as Record<string, number>;
    const b = coverage.b as Record<string, number[]>;
    const f = coverage.f as Record<string, number>;

    const stmtTotal = Object.keys(s).length;
    const stmtCovered = Object.values(s).filter((v) => v > 0).length;

    const branchTotal = Object.values(b).flat().length;
    const branchCovered = Object.values(b).flat().filter((v) => v > 0).length;

    const fnTotal = Object.keys(f).length;
    const fnCovered = Object.values(f).filter((v) => v > 0).length;

    // Calculate line coverage from statement map
    const statementMap = coverage.statementMap as Record<string, { start: { line: number } }>;
    const lines = new Set<number>();
    const coveredLines = new Set<number>();
    
    for (const [key, value] of Object.entries(statementMap)) {
      const line = value.start.line;
      lines.add(line);
      if (s[key] > 0) {
        coveredLines.add(line);
      }
    }

    return {
      path,
      statements: {
        total: stmtTotal,
        covered: stmtCovered,
        skipped: 0,
        percentage: stmtTotal > 0 ? Math.round((stmtCovered / stmtTotal) * 10000) / 100 : 0,
      },
      branches: {
        total: branchTotal,
        covered: branchCovered,
        skipped: 0,
        percentage: branchTotal > 0 ? Math.round((branchCovered / branchTotal) * 10000) / 100 : 0,
      },
      functions: {
        total: fnTotal,
        covered: fnCovered,
        skipped: 0,
        percentage: fnTotal > 0 ? Math.round((fnCovered / fnTotal) * 10000) / 100 : 0,
      },
      lines: {
        total: lines.size,
        covered: coveredLines.size,
        skipped: 0,
        percentage: lines.size > 0 ? Math.round((coveredLines.size / lines.size) * 10000) / 100 : 0,
      },
      uncoveredLines: [...lines].filter((l) => !coveredLines.has(l)),
      uncoveredBranches: [],
      uncoveredFunctions: [],
    };
  }

  /**
   * Parse LCOV format
   */
  private parseLcov(data: string): FileCoverage[] {
    const files: FileCoverage[] = [];
    const records = data.split('end_of_record');

    for (const record of records) {
      if (!record.trim()) continue;

      const lines = record.trim().split('\n');
      let path = '';
      let linesTotal = 0, linesCovered = 0;
      let fnTotal = 0, fnCovered = 0;
      let branchTotal = 0, branchCovered = 0;

      for (const line of lines) {
        if (line.startsWith('SF:')) path = line.substring(3);
        else if (line.startsWith('LF:')) linesTotal = parseInt(line.substring(3));
        else if (line.startsWith('LH:')) linesCovered = parseInt(line.substring(3));
        else if (line.startsWith('FNF:')) fnTotal = parseInt(line.substring(4));
        else if (line.startsWith('FNH:')) fnCovered = parseInt(line.substring(4));
        else if (line.startsWith('BRF:')) branchTotal = parseInt(line.substring(4));
        else if (line.startsWith('BRH:')) branchCovered = parseInt(line.substring(4));
      }

      if (path) {
        files.push({
          path,
          statements: { total: linesTotal, covered: linesCovered, skipped: 0, percentage: linesTotal > 0 ? Math.round((linesCovered / linesTotal) * 10000) / 100 : 0 },
          branches: { total: branchTotal, covered: branchCovered, skipped: 0, percentage: branchTotal > 0 ? Math.round((branchCovered / branchTotal) * 10000) / 100 : 0 },
          functions: { total: fnTotal, covered: fnCovered, skipped: 0, percentage: fnTotal > 0 ? Math.round((fnCovered / fnTotal) * 10000) / 100 : 0 },
          lines: { total: linesTotal, covered: linesCovered, skipped: 0, percentage: linesTotal > 0 ? Math.round((linesCovered / linesTotal) * 10000) / 100 : 0 },
          uncoveredLines: [],
          uncoveredBranches: [],
          uncoveredFunctions: [],
        });
      }
    }

    return files;
  }

  /**
   * Parse Cobertura XML
   */
  private parseCobertura(data: string): FileCoverage[] {
    // Simple XML parsing for Cobertura format
    const files: FileCoverage[] = [];
    const classRegex = /<class name="([^"]+)" filename="([^"]+)" line-rate="([^"]+)" branch-rate="([^"]+)"/g;
    
    let match;
    while ((match = classRegex.exec(data)) !== null) {
      const path = match[2];
      const lineRate = parseFloat(match[3]) * 100;
      const branchRate = parseFloat(match[4]) * 100;

      files.push({
        path,
        statements: { total: 100, covered: Math.round(lineRate), skipped: 0, percentage: lineRate },
        branches: { total: 100, covered: Math.round(branchRate), skipped: 0, percentage: branchRate },
        functions: { total: 100, covered: Math.round(lineRate), skipped: 0, percentage: lineRate },
        lines: { total: 100, covered: Math.round(lineRate), skipped: 0, percentage: lineRate },
        uncoveredLines: [],
        uncoveredBranches: [],
        uncoveredFunctions: [],
      });
    }

    return files;
  }
}

/**
 * Create coverage reporter instance
 */
export function createCoverageReporter(
  config?: Partial<CoverageReporterConfig>
): CoverageReporter {
  return new CoverageReporter(config);
}
