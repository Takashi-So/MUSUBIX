/**
 * @fileoverview Report Aggregator for Multiple Scan Results
 * @module @nahisaho/musubix-security/integrations/report-aggregator
 * 
 * Aggregates multiple security scan results into unified reports
 * with trend analysis and comparison capabilities.
 */

import type { ScanResult, Severity, Vulnerability } from '../types/index.js';

// ============================================================================
// Types
// ============================================================================

/**
 * Aggregated scan entry
 */
export interface AggregatedScanEntry {
  /** Scan identifier */
  id: string;
  /** Scan timestamp */
  timestamp: Date;
  /** Scan target/source */
  source: string;
  /** Scan type */
  type: ScanType;
  /** Original scan result */
  result: ScanResult;
  /** Metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Scan type classification
 */
export type ScanType = 
  | 'vulnerability'
  | 'secret'
  | 'dependency'
  | 'compliance'
  | 'container'
  | 'iac'
  | 'api'
  | 'full';

/**
 * Report aggregator options
 */
export interface ReportAggregatorOptions {
  /** Deduplicate similar findings */
  deduplicate?: boolean;
  /** Similarity threshold for deduplication (0-1) */
  similarityThreshold?: number;
  /** Group by file/rule/severity */
  groupBy?: 'file' | 'rule' | 'severity' | 'category';
  /** Include historical comparison */
  includeHistory?: boolean;
  /** Maximum history entries to keep */
  maxHistoryEntries?: number;
}

/**
 * Aggregated report
 */
export interface AggregatedReport {
  /** Report generation timestamp */
  generatedAt: Date;
  /** Report ID */
  reportId: string;
  /** Summary statistics */
  summary: AggregatedSummary;
  /** All findings (deduplicated if enabled) */
  findings: AggregatedFinding[];
  /** Grouped findings */
  groupedFindings: GroupedFindings;
  /** Scan sources */
  sources: ScanSource[];
  /** Trend data */
  trends: TrendData;
  /** Comparison with previous */
  comparison?: ReportComparison;
}

/**
 * Aggregated summary
 */
export interface AggregatedSummary {
  /** Total scans aggregated */
  totalScans: number;
  /** Total unique findings */
  totalFindings: number;
  /** Findings by severity */
  bySeverity: Record<Severity, number>;
  /** Findings by type */
  byType: Record<ScanType, number>;
  /** Files affected */
  filesAffected: number;
  /** Rules triggered */
  rulesTriggered: number;
  /** Overall security score */
  securityScore: number;
  /** Risk level */
  riskLevel: 'critical' | 'high' | 'medium' | 'low' | 'minimal';
}

/**
 * Aggregated finding
 */
export interface AggregatedFinding {
  /** Finding ID */
  id: string;
  /** Original vulnerability */
  vulnerability: Vulnerability;
  /** Sources where this finding was detected */
  sources: string[];
  /** Occurrence count */
  occurrences: number;
  /** First seen timestamp */
  firstSeen: Date;
  /** Last seen timestamp */
  lastSeen: Date;
  /** Is new (not in previous report) */
  isNew: boolean;
  /** Is fixed (was in previous, not in current) */
  isFixed: boolean;
  /** Fingerprint for deduplication */
  fingerprint: string;
}

/**
 * Grouped findings by category
 */
export interface GroupedFindings {
  /** Findings grouped by file */
  byFile: Map<string, AggregatedFinding[]>;
  /** Findings grouped by rule */
  byRule: Map<string, AggregatedFinding[]>;
  /** Findings grouped by severity */
  bySeverity: Map<Severity, AggregatedFinding[]>;
  /** Findings grouped by OWASP category */
  byCategory: Map<string, AggregatedFinding[]>;
}

/**
 * Scan source metadata
 */
export interface ScanSource {
  /** Source identifier */
  id: string;
  /** Scan type */
  type: ScanType;
  /** Timestamp */
  timestamp: Date;
  /** Target scanned */
  target: string;
  /** Finding count from this source */
  findingCount: number;
}

/**
 * Trend data over time
 */
export interface TrendData {
  /** Data points */
  dataPoints: TrendDataPoint[];
  /** Trend direction */
  direction: 'improving' | 'stable' | 'degrading';
  /** Change percentage */
  changePercent: number;
  /** Projected risk (if trend continues) */
  projectedRisk: string;
}

/**
 * Single trend data point
 */
export interface TrendDataPoint {
  /** Timestamp */
  timestamp: Date;
  /** Total findings */
  totalFindings: number;
  /** Critical findings */
  criticalFindings: number;
  /** Security score */
  securityScore: number;
}

/**
 * Comparison with previous report
 */
export interface ReportComparison {
  /** New findings */
  newFindings: AggregatedFinding[];
  /** Fixed findings */
  fixedFindings: AggregatedFinding[];
  /** Unchanged findings */
  unchangedFindings: AggregatedFinding[];
  /** Finding count change */
  findingDelta: number;
  /** Security score change */
  scoreDelta: number;
  /** Summary text */
  summaryText: string;
}

// ============================================================================
// Report Aggregator Class
// ============================================================================

/**
 * Aggregates multiple security scan results
 * 
 * @example
 * ```typescript
 * const aggregator = createReportAggregator({
 *   deduplicate: true,
 *   groupBy: 'severity',
 * });
 * 
 * aggregator.addScan('vuln-scan', scanResult1, 'vulnerability');
 * aggregator.addScan('secret-scan', scanResult2, 'secret');
 * 
 * const report = aggregator.generateReport();
 * ```
 */
export class ReportAggregator {
  private options: Required<ReportAggregatorOptions>;
  private scans: AggregatedScanEntry[] = [];
  private history: AggregatedReport[] = [];
  private scanCounter = 0;

  constructor(options: ReportAggregatorOptions = {}) {
    this.options = {
      deduplicate: options.deduplicate ?? true,
      similarityThreshold: options.similarityThreshold ?? 0.8,
      groupBy: options.groupBy ?? 'severity',
      includeHistory: options.includeHistory ?? true,
      maxHistoryEntries: options.maxHistoryEntries ?? 10,
    };
  }

  /**
   * Add a scan result to the aggregator
   */
  addScan(
    source: string,
    result: ScanResult,
    type: ScanType = 'full',
    metadata?: Record<string, unknown>
  ): string {
    const id = `scan-${++this.scanCounter}-${Date.now()}`;
    
    this.scans.push({
      id,
      timestamp: new Date(),
      source,
      type,
      result,
      metadata,
    });

    return id;
  }

  /**
   * Remove a scan by ID
   */
  removeScan(id: string): boolean {
    const index = this.scans.findIndex(s => s.id === id);
    if (index >= 0) {
      this.scans.splice(index, 1);
      return true;
    }
    return false;
  }

  /**
   * Clear all scans
   */
  clear(): void {
    this.scans = [];
  }

  /**
   * Generate aggregated report
   */
  generateReport(): AggregatedReport {
    const reportId = `report-${Date.now()}`;
    const generatedAt = new Date();
    
    // Aggregate all findings
    const allFindings = this.aggregateFindings();
    
    // Deduplicate if enabled
    const findings = this.options.deduplicate 
      ? this.deduplicateFindings(allFindings)
      : allFindings;

    // Generate grouped findings
    const groupedFindings = this.groupFindings(findings);

    // Generate summary
    const summary = this.generateSummary(findings);

    // Generate scan sources
    const sources = this.generateSources();

    // Generate trends
    const trends = this.generateTrends(findings);

    // Compare with previous report
    const comparison = this.options.includeHistory && this.history.length > 0
      ? this.compareWithPrevious(findings)
      : undefined;

    const report: AggregatedReport = {
      reportId,
      generatedAt,
      summary,
      findings,
      groupedFindings,
      sources,
      trends,
      comparison,
    };

    // Save to history
    if (this.options.includeHistory) {
      this.history.push(report);
      if (this.history.length > this.options.maxHistoryEntries) {
        this.history.shift();
      }
    }

    return report;
  }

  /**
   * Get scan count
   */
  getScanCount(): number {
    return this.scans.length;
  }

  /**
   * Get history
   */
  getHistory(): AggregatedReport[] {
    return [...this.history];
  }

  /**
   * Export report as JSON
   */
  exportJSON(report: AggregatedReport): string {
    return JSON.stringify(report, (_key, value) => {
      if (value instanceof Date) {
        return value.toISOString();
      }
      if (value instanceof Map) {
        return Object.fromEntries(value);
      }
      return value;
    }, 2);
  }

  /**
   * Export report as Markdown
   */
  exportMarkdown(report: AggregatedReport): string {
    const lines: string[] = [];
    
    lines.push('# Security Scan Aggregated Report');
    lines.push('');
    lines.push(`**Generated:** ${report.generatedAt.toISOString()}`);
    lines.push(`**Report ID:** ${report.reportId}`);
    lines.push('');

    // Summary
    lines.push('## Summary');
    lines.push('');
    lines.push(`- **Total Scans:** ${report.summary.totalScans}`);
    lines.push(`- **Total Findings:** ${report.summary.totalFindings}`);
    lines.push(`- **Security Score:** ${report.summary.securityScore}/100`);
    lines.push(`- **Risk Level:** ${report.summary.riskLevel.toUpperCase()}`);
    lines.push('');

    // Severity breakdown
    lines.push('### Findings by Severity');
    lines.push('');
    lines.push('| Severity | Count |');
    lines.push('|----------|-------|');
    for (const severity of ['critical', 'high', 'medium', 'low', 'info'] as Severity[]) {
      lines.push(`| ${severity} | ${report.summary.bySeverity[severity]} |`);
    }
    lines.push('');

    // Comparison
    if (report.comparison) {
      lines.push('## Changes from Previous');
      lines.push('');
      lines.push(`- **New Findings:** ${report.comparison.newFindings.length}`);
      lines.push(`- **Fixed Findings:** ${report.comparison.fixedFindings.length}`);
      lines.push(`- **Score Change:** ${report.comparison.scoreDelta > 0 ? '+' : ''}${report.comparison.scoreDelta}`);
      lines.push('');
    }

    // Top findings
    lines.push('## Top Findings');
    lines.push('');
    const topFindings = report.findings
      .filter(f => f.vulnerability.severity === 'critical' || f.vulnerability.severity === 'high')
      .slice(0, 10);
    
    for (const finding of topFindings) {
      lines.push(`### ${finding.vulnerability.ruleId}`);
      lines.push('');
      lines.push(`- **Severity:** ${finding.vulnerability.severity}`);
      lines.push(`- **File:** ${finding.vulnerability.location.file}:${finding.vulnerability.location.startLine}`);
      lines.push(`- **Occurrences:** ${finding.occurrences}`);
      lines.push(`- **Message:** ${finding.vulnerability.description}`);
      lines.push('');
    }

    return lines.join('\n');
  }

  // ============================================================================
  // Private Methods
  // ============================================================================

  private aggregateFindings(): AggregatedFinding[] {
    const findingsMap = new Map<string, AggregatedFinding>();

    for (const scan of this.scans) {
      for (const vuln of scan.result.vulnerabilities) {
        const fingerprint = this.generateFingerprint(vuln);
        
        const existing = findingsMap.get(fingerprint);
        if (existing) {
          existing.occurrences++;
          existing.sources.push(scan.source);
          existing.lastSeen = scan.timestamp;
        } else {
          findingsMap.set(fingerprint, {
            id: `finding-${findingsMap.size + 1}`,
            vulnerability: vuln,
            sources: [scan.source],
            occurrences: 1,
            firstSeen: scan.timestamp,
            lastSeen: scan.timestamp,
            isNew: false,
            isFixed: false,
            fingerprint,
          });
        }
      }
    }

    return Array.from(findingsMap.values());
  }

  private deduplicateFindings(findings: AggregatedFinding[]): AggregatedFinding[] {
    const deduplicated: AggregatedFinding[] = [];
    
    for (const finding of findings) {
      const similar = deduplicated.find(f => 
        this.calculateSimilarity(f, finding) >= this.options.similarityThreshold
      );
      
      if (similar) {
        similar.occurrences += finding.occurrences;
        similar.sources.push(...finding.sources);
        if (finding.firstSeen < similar.firstSeen) {
          similar.firstSeen = finding.firstSeen;
        }
        if (finding.lastSeen > similar.lastSeen) {
          similar.lastSeen = finding.lastSeen;
        }
      } else {
        deduplicated.push({ ...finding });
      }
    }

    return deduplicated;
  }

  private groupFindings(findings: AggregatedFinding[]): GroupedFindings {
    const byFile = new Map<string, AggregatedFinding[]>();
    const byRule = new Map<string, AggregatedFinding[]>();
    const bySeverity = new Map<Severity, AggregatedFinding[]>();
    const byCategory = new Map<string, AggregatedFinding[]>();

    for (const finding of findings) {
      // By file
      const file = finding.vulnerability.location.file;
      if (!byFile.has(file)) byFile.set(file, []);
      byFile.get(file)!.push(finding);

      // By rule
      const rule = finding.vulnerability.ruleId;
      if (!byRule.has(rule)) byRule.set(rule, []);
      byRule.get(rule)!.push(finding);

      // By severity
      const severity = finding.vulnerability.severity;
      if (!bySeverity.has(severity)) bySeverity.set(severity, []);
      bySeverity.get(severity)!.push(finding);

      // By category
      const category = finding.vulnerability.owasp?.[0] ?? 'unknown';
      if (!byCategory.has(category)) byCategory.set(category, []);
      byCategory.get(category)!.push(finding);
    }

    return { byFile, byRule, bySeverity, byCategory };
  }

  private generateSummary(findings: AggregatedFinding[]): AggregatedSummary {
    const bySeverity: Record<Severity, number> = {
      critical: 0,
      high: 0,
      medium: 0,
      low: 0,
      info: 0,
    };

    const byType: Record<ScanType, number> = {
      vulnerability: 0,
      secret: 0,
      dependency: 0,
      compliance: 0,
      container: 0,
      iac: 0,
      api: 0,
      full: 0,
    };

    const files = new Set<string>();
    const rules = new Set<string>();

    for (const finding of findings) {
      bySeverity[finding.vulnerability.severity]++;
      files.add(finding.vulnerability.location.file);
      rules.add(finding.vulnerability.ruleId);
    }

    for (const scan of this.scans) {
      byType[scan.type] += scan.result.vulnerabilities.length;
    }

    // Calculate security score
    const penalty = 
      bySeverity.critical * 25 +
      bySeverity.high * 10 +
      bySeverity.medium * 5 +
      bySeverity.low * 2 +
      bySeverity.info * 0.5;
    const securityScore = Math.max(0, Math.min(100, Math.round(100 - penalty)));

    // Determine risk level
    let riskLevel: AggregatedSummary['riskLevel'];
    if (bySeverity.critical > 0) riskLevel = 'critical';
    else if (bySeverity.high > 0) riskLevel = 'high';
    else if (bySeverity.medium > 0) riskLevel = 'medium';
    else if (bySeverity.low > 0) riskLevel = 'low';
    else riskLevel = 'minimal';

    return {
      totalScans: this.scans.length,
      totalFindings: findings.length,
      bySeverity,
      byType,
      filesAffected: files.size,
      rulesTriggered: rules.size,
      securityScore,
      riskLevel,
    };
  }

  private generateSources(): ScanSource[] {
    return this.scans.map(scan => ({
      id: scan.id,
      type: scan.type,
      timestamp: scan.timestamp,
      target: scan.source,
      findingCount: scan.result.vulnerabilities.length,
    }));
  }

  private generateTrends(findings: AggregatedFinding[]): TrendData {
    const dataPoints: TrendDataPoint[] = this.history.map(report => ({
      timestamp: report.generatedAt,
      totalFindings: report.summary.totalFindings,
      criticalFindings: report.summary.bySeverity.critical,
      securityScore: report.summary.securityScore,
    }));

    // Add current
    const currentScore = this.calculateSecurityScore(findings);
    dataPoints.push({
      timestamp: new Date(),
      totalFindings: findings.length,
      criticalFindings: findings.filter(f => f.vulnerability.severity === 'critical').length,
      securityScore: currentScore,
    });

    // Calculate direction
    let direction: TrendData['direction'] = 'stable';
    let changePercent = 0;
    
    if (dataPoints.length >= 2) {
      const prev = dataPoints[dataPoints.length - 2];
      const curr = dataPoints[dataPoints.length - 1];
      changePercent = prev.totalFindings > 0 
        ? Math.round((curr.totalFindings - prev.totalFindings) / prev.totalFindings * 100)
        : 0;
      
      if (changePercent < -10) direction = 'improving';
      else if (changePercent > 10) direction = 'degrading';
    }

    // Project risk
    const projectedRisk = direction === 'degrading' 
      ? 'Risk increasing - immediate attention recommended'
      : direction === 'improving'
      ? 'Risk decreasing - continue current practices'
      : 'Risk stable - maintain vigilance';

    return {
      dataPoints,
      direction,
      changePercent,
      projectedRisk,
    };
  }

  private compareWithPrevious(currentFindings: AggregatedFinding[]): ReportComparison {
    const previousReport = this.history[this.history.length - 1];
    if (!previousReport) {
      return {
        newFindings: currentFindings.map(f => ({ ...f, isNew: true })),
        fixedFindings: [],
        unchangedFindings: [],
        findingDelta: currentFindings.length,
        scoreDelta: 0,
        summaryText: 'First report - no comparison available',
      };
    }

    const prevFingerprints = new Set(previousReport.findings.map(f => f.fingerprint));
    const currFingerprints = new Set(currentFindings.map(f => f.fingerprint));

    const newFindings = currentFindings
      .filter(f => !prevFingerprints.has(f.fingerprint))
      .map(f => ({ ...f, isNew: true }));
    
    const fixedFindings = previousReport.findings
      .filter(f => !currFingerprints.has(f.fingerprint))
      .map(f => ({ ...f, isFixed: true }));
    
    const unchangedFindings = currentFindings
      .filter(f => prevFingerprints.has(f.fingerprint));

    const currentScore = this.calculateSecurityScore(currentFindings);
    const findingDelta = currentFindings.length - previousReport.findings.length;
    const scoreDelta = currentScore - previousReport.summary.securityScore;

    let summaryText: string;
    if (newFindings.length === 0 && fixedFindings.length === 0) {
      summaryText = 'No changes detected';
    } else if (fixedFindings.length > newFindings.length) {
      summaryText = `Improvement: ${fixedFindings.length} fixed, ${newFindings.length} new`;
    } else if (newFindings.length > fixedFindings.length) {
      summaryText = `Regression: ${newFindings.length} new, ${fixedFindings.length} fixed`;
    } else {
      summaryText = `Mixed: ${newFindings.length} new, ${fixedFindings.length} fixed`;
    }

    return {
      newFindings,
      fixedFindings,
      unchangedFindings,
      findingDelta,
      scoreDelta,
      summaryText,
    };
  }

  private generateFingerprint(vuln: Vulnerability): string {
    const parts = [
      vuln.ruleId,
      vuln.location.file,
      vuln.location.startLine.toString(),
      vuln.description.substring(0, 100),
    ];
    return parts.join('::');
  }

  private calculateSimilarity(a: AggregatedFinding, b: AggregatedFinding): number {
    // Same rule = high similarity
    if (a.vulnerability.ruleId === b.vulnerability.ruleId) {
      // Same file = very high similarity
      if (a.vulnerability.location.file === b.vulnerability.location.file) {
        // Same line = identical
        if (a.vulnerability.location.startLine === b.vulnerability.location.startLine) {
          return 1.0;
        }
        return 0.9;
      }
      return 0.7;
    }
    return 0;
  }

  private calculateSecurityScore(findings: AggregatedFinding[]): number {
    let penalty = 0;
    for (const finding of findings) {
      switch (finding.vulnerability.severity) {
        case 'critical': penalty += 25; break;
        case 'high': penalty += 10; break;
        case 'medium': penalty += 5; break;
        case 'low': penalty += 2; break;
        case 'info': penalty += 0.5; break;
      }
    }
    return Math.max(0, Math.min(100, Math.round(100 - penalty)));
  }
}

// ============================================================================
// Factory Functions
// ============================================================================

/**
 * Create a report aggregator
 */
export function createReportAggregator(options?: ReportAggregatorOptions): ReportAggregator {
  return new ReportAggregator(options);
}
