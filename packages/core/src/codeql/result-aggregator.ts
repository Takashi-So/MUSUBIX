/**
 * Result Aggregator - Aggregate CodeQL findings for reporting
 *
 * Implements: TSK-CODEQL-003, REQ-CODEQL-004〜005, DES-CODEQL-003
 */

import type { CodeQLFinding, CodeQLScanResult } from './types.js';

/**
 * Aggregated report format
 */
export interface AggregatedReport {
  /** Report metadata */
  meta: {
    generatedAt: Date;
    tool: string;
    toolVersion?: string;
    projectPath?: string;
  };

  /** Summary statistics */
  summary: {
    totalFindings: number;
    uniqueRules: number;
    filesAffected: number;
    bySeverity: Record<string, number>;
    byCategory: Record<string, number>;
  };

  /** Findings grouped by file */
  byFile: Map<string, CodeQLFinding[]>;

  /** Findings grouped by rule */
  byRule: Map<string, CodeQLFinding[]>;

  /** Top issues (most frequent rules) */
  topIssues: Array<{
    ruleId: string;
    ruleName?: string;
    count: number;
    severity: string;
  }>;

  /** Critical findings requiring immediate attention */
  critical: CodeQLFinding[];

  /** Raw findings */
  findings: CodeQLFinding[];
}

/**
 * Aggregator configuration
 */
export interface AggregatorConfig {
  /** Group findings by file */
  groupByFile?: boolean;

  /** Group findings by rule */
  groupByRule?: boolean;

  /** Sort order */
  sortBy?: 'severity' | 'file' | 'rule';

  /** Limit top issues count */
  topIssuesLimit?: number;

  /** Include CWE category grouping */
  groupByCWE?: boolean;
}

/**
 * Result Aggregator class
 */
export class ResultAggregator {
  private config: AggregatorConfig;

  constructor(config: AggregatorConfig = {}) {
    this.config = {
      groupByFile: true,
      groupByRule: true,
      sortBy: 'severity',
      topIssuesLimit: 10,
      groupByCWE: true,
      ...config,
    };
  }

  /**
   * Aggregate a single scan result
   */
  aggregate(result: CodeQLScanResult): AggregatedReport {
    const findings = this.sortFindings(result.findings);

    // Group by file
    const byFile = new Map<string, CodeQLFinding[]>();
    if (this.config.groupByFile) {
      for (const finding of findings) {
        const file = finding.file || 'unknown';
        const existing = byFile.get(file) ?? [];
        existing.push(finding);
        byFile.set(file, existing);
      }
    }

    // Group by rule
    const byRule = new Map<string, CodeQLFinding[]>();
    if (this.config.groupByRule) {
      for (const finding of findings) {
        const existing = byRule.get(finding.ruleId) ?? [];
        existing.push(finding);
        byRule.set(finding.ruleId, existing);
      }
    }

    // Calculate top issues
    const topIssues = this.calculateTopIssues(byRule);

    // Get critical findings
    const critical = findings.filter(
      (f) => f.severity === 'critical' || f.severity === 'high'
    );

    // Calculate category stats
    const byCategory = this.calculateCategoryStats(findings);

    return {
      meta: {
        generatedAt: new Date(),
        tool: result.tool.name,
        toolVersion: result.tool.version,
      },
      summary: {
        totalFindings: findings.length,
        uniqueRules: byRule.size,
        filesAffected: byFile.size,
        bySeverity: result.stats.bySeverity,
        byCategory,
      },
      byFile,
      byRule,
      topIssues,
      critical,
      findings,
    };
  }

  /**
   * Merge multiple scan results
   */
  mergeResults(results: CodeQLScanResult[]): CodeQLScanResult {
    const allFindings: CodeQLFinding[] = [];
    let toolName = 'multiple';
    let toolVersion: string | undefined;

    for (const result of results) {
      allFindings.push(...result.findings);
      if (results.length === 1) {
        toolName = result.tool.name;
        toolVersion = result.tool.version;
      }
    }

    // Deduplicate findings by ID
    const uniqueFindings = this.deduplicateFindings(allFindings);

    // Recalculate stats
    const stats = this.calculateStats(uniqueFindings);

    return {
      timestamp: new Date(),
      tool: { name: toolName, version: toolVersion },
      findings: uniqueFindings,
      stats,
    };
  }

  /**
   * Sort findings by configured order
   */
  private sortFindings(findings: CodeQLFinding[]): CodeQLFinding[] {
    const severityOrder = ['critical', 'high', 'medium', 'low', 'info'];

    return [...findings].sort((a, b) => {
      switch (this.config.sortBy) {
        case 'severity':
          return (
            severityOrder.indexOf(a.severity) -
            severityOrder.indexOf(b.severity)
          );
        case 'file':
          return (a.file || '').localeCompare(b.file || '');
        case 'rule':
          return a.ruleId.localeCompare(b.ruleId);
        default:
          return 0;
      }
    });
  }

  /**
   * Calculate top issues from rule grouping
   */
  private calculateTopIssues(
    byRule: Map<string, CodeQLFinding[]>
  ): AggregatedReport['topIssues'] {
    const issues: AggregatedReport['topIssues'] = [];

    for (const [ruleId, findings] of byRule) {
      issues.push({
        ruleId,
        ruleName: findings[0]?.ruleName,
        count: findings.length,
        severity: findings[0]?.severity ?? 'medium',
      });
    }

    // Sort by count descending
    issues.sort((a, b) => b.count - a.count);

    return issues.slice(0, this.config.topIssuesLimit);
  }

  /**
   * Calculate CWE category statistics
   */
  private calculateCategoryStats(findings: CodeQLFinding[]): Record<string, number> {
    const byCategory: Record<string, number> = {};

    for (const finding of findings) {
      if (finding.cweIds && finding.cweIds.length > 0) {
        for (const cweId of finding.cweIds) {
          const category = this.getCWECategory(cweId);
          byCategory[category] = (byCategory[category] ?? 0) + 1;
        }
      } else {
        byCategory['uncategorized'] = (byCategory['uncategorized'] ?? 0) + 1;
      }
    }

    return byCategory;
  }

  /**
   * Get CWE category from ID (simplified)
   */
  private getCWECategory(cweId: string): string {
    const id = parseInt(cweId.replace('CWE-', ''), 10);

    // Simplified category mapping based on CWE ranges
    if ([79, 89, 78, 94, 77, 502].includes(id)) return 'injection';
    if ([287, 306, 862, 352, 269].includes(id)) return 'auth';
    if ([311, 327].includes(id)) return 'crypto';
    if ([22, 434].includes(id)) return 'file';
    if ([798].includes(id)) return 'secrets';
    if ([119, 416, 476, 190].includes(id)) return 'memory';
    if ([200].includes(id)) return 'info-disclosure';

    return 'other';
  }

  /**
   * Deduplicate findings
   */
  private deduplicateFindings(findings: CodeQLFinding[]): CodeQLFinding[] {
    const seen = new Set<string>();
    const unique: CodeQLFinding[] = [];

    for (const finding of findings) {
      if (!seen.has(finding.id)) {
        seen.add(finding.id);
        unique.push(finding);
      }
    }

    return unique;
  }

  /**
   * Calculate statistics
   */
  private calculateStats(findings: CodeQLFinding[]): CodeQLScanResult['stats'] {
    const bySeverity: Record<string, number> = {
      critical: 0,
      high: 0,
      medium: 0,
      low: 0,
      info: 0,
    };

    const byRule: Record<string, number> = {};
    const files = new Set<string>();

    for (const finding of findings) {
      bySeverity[finding.severity] = (bySeverity[finding.severity] ?? 0) + 1;
      byRule[finding.ruleId] = (byRule[finding.ruleId] ?? 0) + 1;
      if (finding.file) {
        files.add(finding.file);
      }
    }

    return {
      total: findings.length,
      bySeverity,
      byRule,
      filesAffected: files.size,
    };
  }

  /**
   * Generate markdown report
   */
  toMarkdown(report: AggregatedReport): string {
    const lines: string[] = [];

    lines.push('# CodeQL Security Report\n');
    lines.push(`**Generated**: ${report.meta.generatedAt.toISOString()}`);
    lines.push(`**Tool**: ${report.meta.tool}${report.meta.toolVersion ? ` v${report.meta.toolVersion}` : ''}\n`);

    lines.push('## Summary\n');
    lines.push(`| Metric | Value |`);
    lines.push(`|--------|-------|`);
    lines.push(`| Total Findings | ${report.summary.totalFindings} |`);
    lines.push(`| Unique Rules | ${report.summary.uniqueRules} |`);
    lines.push(`| Files Affected | ${report.summary.filesAffected} |`);
    lines.push('');

    lines.push('### By Severity\n');
    lines.push('| Severity | Count |');
    lines.push('|----------|-------|');
    for (const [severity, count] of Object.entries(report.summary.bySeverity)) {
      if (count > 0) {
        const icon = severity === 'critical' ? '🔴' : severity === 'high' ? '🟠' : severity === 'medium' ? '🟡' : '🟢';
        lines.push(`| ${icon} ${severity} | ${count} |`);
      }
    }
    lines.push('');

    if (report.critical.length > 0) {
      lines.push('## ⚠️ Critical Findings\n');
      for (const finding of report.critical.slice(0, 10)) {
        lines.push(`### ${finding.ruleId}`);
        lines.push(`- **File**: \`${finding.file}:${finding.startLine ?? ''}\``);
        lines.push(`- **Message**: ${finding.message}`);
        if (finding.cweIds && finding.cweIds.length > 0) {
          lines.push(`- **CWE**: ${finding.cweIds.join(', ')}`);
        }
        if (finding.explanation) {
          lines.push(`- **説明**: ${finding.explanation.slice(0, 200)}...`);
        }
        lines.push('');
      }
    }

    lines.push('## Top Issues\n');
    lines.push('| Rule | Count | Severity |');
    lines.push('|------|-------|----------|');
    for (const issue of report.topIssues) {
      lines.push(`| ${issue.ruleName ?? issue.ruleId} | ${issue.count} | ${issue.severity} |`);
    }

    return lines.join('\n');
  }

  /**
   * Generate JSON report
   */
  toJSON(report: AggregatedReport): string {
    return JSON.stringify(
      {
        meta: report.meta,
        summary: report.summary,
        topIssues: report.topIssues,
        critical: report.critical,
        findings: report.findings,
      },
      null,
      2
    );
  }
}

/**
 * Create a result aggregator
 */
export function createResultAggregator(config?: AggregatorConfig): ResultAggregator {
  return new ResultAggregator(config);
}
