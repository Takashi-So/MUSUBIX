/**
 * @fileoverview Security Dashboard - Integrated security reporting and visualization
 * @module @nahisaho/musubix-security/analyzers/dashboard/security-dashboard
 * @trace DES-SEC3-DASH-001, REQ-SEC3-DASH-001
 */

import type { Vulnerability, Severity } from '../../types/vulnerability.js';

/**
 * Dashboard-specific scan result (simplified for dashboard reporting)
 */
export interface DashboardScanResult {
  scannedAt: Date;
  filesScanned: number;
  vulnerabilities: Vulnerability[];
  summary: {
    critical: number;
    high: number;
    medium: number;
    low: number;
    info: number;
    total: number;
  };
}

/**
 * Dashboard configuration
 */
export interface DashboardConfig {
  /** Project name */
  projectName: string;
  /** Report format */
  format?: 'json' | 'html' | 'markdown';
  /** Include trend data */
  includeTrends?: boolean;
  /** Include recommendations */
  includeRecommendations?: boolean;
  /** Custom branding */
  branding?: DashboardBranding;
}

/**
 * Custom branding options
 */
export interface DashboardBranding {
  logo?: string;
  title?: string;
  colors?: {
    critical?: string;
    high?: string;
    medium?: string;
    low?: string;
    info?: string;
  };
}

/**
 * Security metrics
 */
export interface SecurityMetrics {
  /** Total vulnerabilities found */
  totalVulnerabilities: number;
  /** Breakdown by severity */
  bySeverity: Record<Severity, number>;
  /** Breakdown by type */
  byType: Record<string, number>;
  /** Breakdown by file/component */
  byComponent: Record<string, number>;
  /** OWASP Top 10 coverage */
  owaspCoverage: OWASPCoverage[];
  /** CWE distribution */
  cweDistribution: CWEDistribution[];
  /** Overall security score (0-100) */
  securityScore: number;
  /** Risk level */
  riskLevel: 'critical' | 'high' | 'medium' | 'low' | 'minimal';
}

/**
 * OWASP Top 10 coverage
 */
export interface OWASPCoverage {
  id: string;
  name: string;
  count: number;
  percentage: number;
}

/**
 * CWE distribution
 */
export interface CWEDistribution {
  cwe: string;
  name: string;
  count: number;
  percentage: number;
}

/**
 * Trend data point
 */
export interface TrendDataPoint {
  timestamp: Date;
  totalVulnerabilities: number;
  critical: number;
  high: number;
  medium: number;
  low: number;
  securityScore: number;
}

/**
 * Security trend
 */
export interface SecurityTrend {
  period: 'day' | 'week' | 'month';
  dataPoints: TrendDataPoint[];
  improvement: number;
  direction: 'improving' | 'degrading' | 'stable';
}

/**
 * Top vulnerability
 */
export interface TopVulnerability {
  type: string;
  count: number;
  severity: Severity;
  cwes: string[];
  recommendation: string;
}

/**
 * Component risk
 */
export interface ComponentRisk {
  component: string;
  vulnerabilityCount: number;
  criticalCount: number;
  highCount: number;
  riskScore: number;
}

/**
 * Security recommendation
 */
export interface SecurityRecommendation {
  priority: 'critical' | 'high' | 'medium' | 'low';
  category: string;
  title: string;
  description: string;
  impact: string;
  effort: 'low' | 'medium' | 'high';
  affectedCount: number;
}

/**
 * Dashboard report
 */
export interface DashboardReport {
  /** Generation timestamp */
  generatedAt: Date;
  /** Project name */
  projectName: string;
  /** Report period */
  period?: { start: Date; end: Date };
  /** Executive summary */
  summary: ExecutiveSummary;
  /** Security metrics */
  metrics: SecurityMetrics;
  /** Top vulnerabilities */
  topVulnerabilities: TopVulnerability[];
  /** Component risks */
  componentRisks: ComponentRisk[];
  /** Trends (if enabled) */
  trends?: SecurityTrend;
  /** Recommendations (if enabled) */
  recommendations?: SecurityRecommendation[];
  /** Raw vulnerabilities */
  vulnerabilities: Vulnerability[];
  /** Scan results summary */
  scanSummary: ScanSummary;
}

/**
 * Executive summary
 */
export interface ExecutiveSummary {
  status: 'critical' | 'warning' | 'attention' | 'good' | 'excellent';
  statusMessage: string;
  highlights: string[];
  keyFindings: string[];
  immediateActions: string[];
}

/**
 * Scan summary
 */
export interface ScanSummary {
  totalScans: number;
  filesScanned: number;
  lastScanDate: Date;
  scanDuration?: number;
  coverage: number;
}

/**
 * OWASP Top 10 2021 categories
 */
const OWASP_TOP_10: Array<{ id: string; name: string; patterns: string[] }> = [
  {
    id: 'A01:2021',
    name: 'Broken Access Control',
    patterns: ['authorization', 'access-control', 'idor', 'privilege'],
  },
  {
    id: 'A02:2021',
    name: 'Cryptographic Failures',
    patterns: ['crypto', 'encryption', 'weak-cipher', 'hardcoded-key'],
  },
  {
    id: 'A03:2021',
    name: 'Injection',
    patterns: ['sql-injection', 'command-injection', 'xss', 'code-injection', 'ldap-injection'],
  },
  {
    id: 'A04:2021',
    name: 'Insecure Design',
    patterns: ['insecure-design', 'missing-auth', 'business-logic'],
  },
  {
    id: 'A05:2021',
    name: 'Security Misconfiguration',
    patterns: ['misconfiguration', 'default-credentials', 'verbose-errors'],
  },
  {
    id: 'A06:2021',
    name: 'Vulnerable and Outdated Components',
    patterns: ['vulnerable-dependency', 'outdated', 'component'],
  },
  {
    id: 'A07:2021',
    name: 'Identification and Authentication Failures',
    patterns: ['authentication', 'session', 'weak-password', 'brute-force'],
  },
  {
    id: 'A08:2021',
    name: 'Software and Data Integrity Failures',
    patterns: ['integrity', 'deserialization', 'ci-cd', 'supply-chain'],
  },
  {
    id: 'A09:2021',
    name: 'Security Logging and Monitoring Failures',
    patterns: ['logging', 'monitoring', 'audit'],
  },
  {
    id: 'A10:2021',
    name: 'Server-Side Request Forgery (SSRF)',
    patterns: ['ssrf', 'request-forgery'],
  },
];

/**
 * CWE names mapping (common ones)
 */
const CWE_NAMES: Record<string, string> = {
  'CWE-20': 'Improper Input Validation',
  'CWE-22': 'Path Traversal',
  'CWE-78': 'OS Command Injection',
  'CWE-79': 'Cross-site Scripting (XSS)',
  'CWE-89': 'SQL Injection',
  'CWE-94': 'Code Injection',
  'CWE-200': 'Information Exposure',
  'CWE-287': 'Improper Authentication',
  'CWE-306': 'Missing Authentication',
  'CWE-311': 'Missing Encryption',
  'CWE-327': 'Weak Cryptography',
  'CWE-352': 'Cross-Site Request Forgery (CSRF)',
  'CWE-400': 'Resource Exhaustion',
  'CWE-502': 'Deserialization of Untrusted Data',
  'CWE-522': 'Insufficiently Protected Credentials',
  'CWE-601': 'Open Redirect',
  'CWE-611': 'XXE',
  'CWE-798': 'Hardcoded Credentials',
  'CWE-918': 'Server-Side Request Forgery (SSRF)',
};

/**
 * Security Dashboard
 * @trace DES-SEC3-DASH-001
 */
export class SecurityDashboard {
  private config: Required<DashboardConfig>;
  private vulnerabilities: Vulnerability[] = [];
  private scanResults: DashboardScanResult[] = [];
  private trendHistory: TrendDataPoint[] = [];

  constructor(config: DashboardConfig) {
    this.config = {
      projectName: config.projectName,
      format: config.format ?? 'json',
      includeTrends: config.includeTrends ?? true,
      includeRecommendations: config.includeRecommendations ?? true,
      branding: config.branding ?? {},
    };
  }

  /**
   * Add scan results to dashboard
   * @trace REQ-SEC3-DASH-001
   */
  addScanResult(result: DashboardScanResult): void {
    this.scanResults.push(result);
    this.vulnerabilities.push(...result.vulnerabilities);
    
    // Add to trend history
    this.trendHistory.push({
      timestamp: result.scannedAt,
      totalVulnerabilities: this.vulnerabilities.length,
      critical: result.summary.critical,
      high: result.summary.high,
      medium: result.summary.medium,
      low: result.summary.low,
      securityScore: this.calculateSecurityScore(this.vulnerabilities),
    });
  }

  /**
   * Add vulnerabilities directly
   */
  addVulnerabilities(vulnerabilities: Vulnerability[]): void {
    this.vulnerabilities.push(...vulnerabilities);
  }

  /**
   * Clear all data
   */
  clear(): void {
    this.vulnerabilities = [];
    this.scanResults = [];
  }

  /**
   * Generate dashboard report
   */
  generateReport(): DashboardReport {
    const metrics = this.calculateMetrics();
    const topVulnerabilities = this.getTopVulnerabilities();
    const componentRisks = this.calculateComponentRisks();
    const summary = this.generateExecutiveSummary(metrics, topVulnerabilities);

    const report: DashboardReport = {
      generatedAt: new Date(),
      projectName: this.config.projectName,
      summary,
      metrics,
      topVulnerabilities,
      componentRisks,
      vulnerabilities: this.vulnerabilities,
      scanSummary: this.generateScanSummary(),
    };

    if (this.config.includeTrends) {
      report.trends = this.calculateTrends();
    }

    if (this.config.includeRecommendations) {
      report.recommendations = this.generateRecommendations(metrics, topVulnerabilities);
    }

    return report;
  }

  /**
   * Export report in specified format
   */
  exportReport(format?: 'json' | 'html' | 'markdown'): string {
    const report = this.generateReport();
    const outputFormat = format ?? this.config.format;

    switch (outputFormat) {
      case 'html':
        return this.toHTML(report);
      case 'markdown':
        return this.toMarkdown(report);
      default:
        return JSON.stringify(report, null, 2);
    }
  }

  /**
   * Calculate security metrics
   */
  private calculateMetrics(): SecurityMetrics {
    const bySeverity: Record<Severity, number> = {
      critical: 0,
      high: 0,
      medium: 0,
      low: 0,
      info: 0,
    };

    const byType: Record<string, number> = {};
    const byComponent: Record<string, number> = {};
    const cweCount: Record<string, number> = {};
    const owaspCount: Record<string, number> = {};

    for (const vuln of this.vulnerabilities) {
      // By severity
      bySeverity[vuln.severity]++;

      // By type
      byType[vuln.type] = (byType[vuln.type] ?? 0) + 1;

      // By component (file)
      const component = vuln.location.file;
      byComponent[component] = (byComponent[component] ?? 0) + 1;

      // CWE distribution
      for (const cwe of vuln.cwes ?? []) {
        cweCount[cwe] = (cweCount[cwe] ?? 0) + 1;
      }

      // OWASP coverage
      for (const owasp of vuln.owasp ?? []) {
        owaspCount[owasp] = (owaspCount[owasp] ?? 0) + 1;
      }
    }

    const total = this.vulnerabilities.length;

    // Calculate OWASP coverage
    const owaspCoverage: OWASPCoverage[] = OWASP_TOP_10.map(owasp => ({
      id: owasp.id,
      name: owasp.name,
      count: owaspCount[owasp.id] ?? 0,
      percentage: total > 0 ? Math.round(((owaspCount[owasp.id] ?? 0) / total) * 100) : 0,
    }));

    // Calculate CWE distribution
    const cweDistribution: CWEDistribution[] = Object.entries(cweCount)
      .sort(([, a], [, b]) => b - a)
      .slice(0, 10)
      .map(([cwe, count]) => ({
        cwe,
        name: CWE_NAMES[cwe] ?? cwe,
        count,
        percentage: total > 0 ? Math.round((count / total) * 100) : 0,
      }));

    const securityScore = this.calculateSecurityScore(this.vulnerabilities);
    const riskLevel = this.determineRiskLevel(bySeverity, securityScore);

    return {
      totalVulnerabilities: total,
      bySeverity,
      byType,
      byComponent,
      owaspCoverage,
      cweDistribution,
      securityScore,
      riskLevel,
    };
  }

  /**
   * Calculate security score
   */
  private calculateSecurityScore(vulnerabilities: Vulnerability[]): number {
    let score = 100;

    for (const vuln of vulnerabilities) {
      switch (vuln.severity) {
        case 'critical':
          score -= 15;
          break;
        case 'high':
          score -= 10;
          break;
        case 'medium':
          score -= 5;
          break;
        case 'low':
          score -= 2;
          break;
        case 'info':
          score -= 1;
          break;
      }
    }

    return Math.max(0, Math.min(100, score));
  }

  /**
   * Determine risk level
   */
  private determineRiskLevel(
    bySeverity: Record<Severity, number>,
    score: number
  ): SecurityMetrics['riskLevel'] {
    if (bySeverity.critical > 0 || score < 30) return 'critical';
    if (bySeverity.high > 2 || score < 50) return 'high';
    if (bySeverity.high > 0 || bySeverity.medium > 5 || score < 70) return 'medium';
    if (bySeverity.medium > 0 || score < 90) return 'low';
    return 'minimal';
  }

  /**
   * Get top vulnerabilities
   */
  private getTopVulnerabilities(): TopVulnerability[] {
    const typeMap = new Map<string, {
      count: number;
      severity: Severity;
      cwes: Set<string>;
      recommendation: string;
    }>();

    for (const vuln of this.vulnerabilities) {
      const existing = typeMap.get(vuln.type);
      if (existing) {
        existing.count++;
        for (const cwe of vuln.cwes ?? []) {
          existing.cwes.add(cwe);
        }
        // Keep highest severity
        if (this.severityValue(vuln.severity) > this.severityValue(existing.severity)) {
          existing.severity = vuln.severity;
        }
      } else {
        typeMap.set(vuln.type, {
          count: 1,
          severity: vuln.severity,
          cwes: new Set(vuln.cwes ?? []),
          recommendation: vuln.recommendation ?? 'Review and fix the vulnerability',
        });
      }
    }

    return Array.from(typeMap.entries())
      .map(([type, data]) => ({
        type,
        count: data.count,
        severity: data.severity,
        cwes: Array.from(data.cwes),
        recommendation: data.recommendation,
      }))
      .sort((a, b) => {
        const severityDiff = this.severityValue(b.severity) - this.severityValue(a.severity);
        return severityDiff !== 0 ? severityDiff : b.count - a.count;
      })
      .slice(0, 10);
  }

  /**
   * Calculate component risks
   */
  private calculateComponentRisks(): ComponentRisk[] {
    const componentMap = new Map<string, {
      total: number;
      critical: number;
      high: number;
    }>();

    for (const vuln of this.vulnerabilities) {
      const component = vuln.location.file;
      const existing = componentMap.get(component) ?? { total: 0, critical: 0, high: 0 };
      existing.total++;
      if (vuln.severity === 'critical') existing.critical++;
      if (vuln.severity === 'high') existing.high++;
      componentMap.set(component, existing);
    }

    return Array.from(componentMap.entries())
      .map(([component, data]) => ({
        component,
        vulnerabilityCount: data.total,
        criticalCount: data.critical,
        highCount: data.high,
        riskScore: data.critical * 15 + data.high * 10 + (data.total - data.critical - data.high) * 3,
      }))
      .sort((a, b) => b.riskScore - a.riskScore)
      .slice(0, 10);
  }

  /**
   * Generate executive summary
   */
  private generateExecutiveSummary(
    metrics: SecurityMetrics,
    topVulns: TopVulnerability[]
  ): ExecutiveSummary {
    const { bySeverity, securityScore, riskLevel } = metrics;

    let status: ExecutiveSummary['status'];
    let statusMessage: string;

    if (riskLevel === 'critical') {
      status = 'critical';
      statusMessage = `Critical security issues detected. Immediate attention required.`;
    } else if (riskLevel === 'high') {
      status = 'warning';
      statusMessage = `High-priority security issues found. Prompt remediation recommended.`;
    } else if (riskLevel === 'medium') {
      status = 'attention';
      statusMessage = `Medium-priority security issues identified. Plan for remediation.`;
    } else if (riskLevel === 'low') {
      status = 'good';
      statusMessage = `Security posture is good with minor issues to address.`;
    } else {
      status = 'excellent';
      statusMessage = `Excellent security posture. Continue monitoring.`;
    }

    const highlights: string[] = [];
    highlights.push(`Security Score: ${securityScore}/100`);
    highlights.push(`Total Vulnerabilities: ${metrics.totalVulnerabilities}`);
    if (bySeverity.critical > 0) {
      highlights.push(`⚠️ ${bySeverity.critical} critical issue(s) require immediate attention`);
    }
    if (bySeverity.high > 0) {
      highlights.push(`🔴 ${bySeverity.high} high severity issue(s) found`);
    }

    const keyFindings: string[] = [];
    for (const vuln of topVulns.slice(0, 3)) {
      keyFindings.push(`${vuln.type}: ${vuln.count} occurrence(s) (${vuln.severity})`);
    }

    const immediateActions: string[] = [];
    if (bySeverity.critical > 0) {
      immediateActions.push('Address all critical vulnerabilities immediately');
    }
    if (bySeverity.high > 0) {
      immediateActions.push('Prioritize remediation of high-severity issues');
    }
    const topType = topVulns[0];
    if (topType) {
      immediateActions.push(`Focus on most common issue type: ${topType.type}`);
    }

    return {
      status,
      statusMessage,
      highlights,
      keyFindings,
      immediateActions,
    };
  }

  /**
   * Generate scan summary
   */
  private generateScanSummary(): ScanSummary {
    const totalFiles = new Set(this.vulnerabilities.map(v => v.location.file)).size;
    const lastScan = this.scanResults.length > 0 
      ? this.scanResults[this.scanResults.length - 1].scannedAt 
      : new Date();

    return {
      totalScans: this.scanResults.length,
      filesScanned: this.scanResults.reduce((sum, r) => sum + r.filesScanned, 0) || totalFiles,
      lastScanDate: lastScan,
      coverage: 100, // Placeholder
    };
  }

  /**
   * Calculate trends
   */
  private calculateTrends(): SecurityTrend {
    const dataPoints = this.trendHistory.slice(-30); // Last 30 data points
    
    const firstScore = dataPoints[0]?.securityScore ?? 100;
    const lastScore = dataPoints[dataPoints.length - 1]?.securityScore ?? 100;
    const improvement = lastScore - firstScore;

    let direction: SecurityTrend['direction'];
    if (improvement > 5) direction = 'improving';
    else if (improvement < -5) direction = 'degrading';
    else direction = 'stable';

    return {
      period: 'day',
      dataPoints,
      improvement,
      direction,
    };
  }

  /**
   * Generate recommendations
   */
  private generateRecommendations(
    metrics: SecurityMetrics,
    topVulns: TopVulnerability[]
  ): SecurityRecommendation[] {
    const recommendations: SecurityRecommendation[] = [];

    // Critical/High severity recommendations
    if (metrics.bySeverity.critical > 0) {
      recommendations.push({
        priority: 'critical',
        category: 'Remediation',
        title: 'Address Critical Vulnerabilities',
        description: `${metrics.bySeverity.critical} critical vulnerabilities require immediate attention`,
        impact: 'System compromise, data breach risk',
        effort: 'high',
        affectedCount: metrics.bySeverity.critical,
      });
    }

    if (metrics.bySeverity.high > 0) {
      recommendations.push({
        priority: 'high',
        category: 'Remediation',
        title: 'Fix High-Severity Issues',
        description: `${metrics.bySeverity.high} high-severity vulnerabilities should be addressed promptly`,
        impact: 'Significant security exposure',
        effort: 'medium',
        affectedCount: metrics.bySeverity.high,
      });
    }

    // Type-specific recommendations
    for (const vuln of topVulns.slice(0, 3)) {
      if (vuln.count >= 3) {
        recommendations.push({
          priority: this.severityToPriority(vuln.severity),
          category: 'Pattern',
          title: `Reduce ${vuln.type} Vulnerabilities`,
          description: vuln.recommendation,
          impact: `${vuln.count} occurrences across the codebase`,
          effort: 'medium',
          affectedCount: vuln.count,
        });
      }
    }

    // General recommendations
    if (metrics.securityScore < 80) {
      recommendations.push({
        priority: 'medium',
        category: 'Process',
        title: 'Implement Security Code Review',
        description: 'Establish mandatory security review for all code changes',
        impact: 'Prevent introduction of new vulnerabilities',
        effort: 'medium',
        affectedCount: 0,
      });
    }

    if (metrics.totalVulnerabilities > 20) {
      recommendations.push({
        priority: 'medium',
        category: 'Process',
        title: 'Security Sprint Planning',
        description: 'Dedicate engineering time specifically for security remediation',
        impact: 'Systematic reduction of vulnerability backlog',
        effort: 'high',
        affectedCount: metrics.totalVulnerabilities,
      });
    }

    return recommendations.slice(0, 10);
  }

  /**
   * Convert severity to numeric value
   */
  private severityValue(severity: Severity): number {
    const values: Record<Severity, number> = {
      critical: 4,
      high: 3,
      medium: 2,
      low: 1,
      info: 0,
    };
    return values[severity];
  }

  /**
   * Convert severity to priority
   */
  private severityToPriority(severity: Severity): SecurityRecommendation['priority'] {
    const mapping: Record<Severity, SecurityRecommendation['priority']> = {
      critical: 'critical',
      high: 'high',
      medium: 'medium',
      low: 'low',
      info: 'low',
    };
    return mapping[severity];
  }

  /**
   * Export to HTML format
   */
  private toHTML(report: DashboardReport): string {
    const colors = this.config.branding.colors ?? {
      critical: '#dc2626',
      high: '#ea580c',
      medium: '#ca8a04',
      low: '#16a34a',
      info: '#2563eb',
    };

    return `<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>${this.config.branding.title ?? 'Security Dashboard'} - ${report.projectName}</title>
  <style>
    * { box-sizing: border-box; margin: 0; padding: 0; }
    body { font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif; background: #f3f4f6; color: #1f2937; line-height: 1.5; }
    .container { max-width: 1200px; margin: 0 auto; padding: 2rem; }
    .header { background: #1f2937; color: white; padding: 2rem; margin-bottom: 2rem; border-radius: 8px; }
    .header h1 { font-size: 1.5rem; }
    .header p { color: #9ca3af; margin-top: 0.5rem; }
    .card { background: white; border-radius: 8px; padding: 1.5rem; margin-bottom: 1rem; box-shadow: 0 1px 3px rgba(0,0,0,0.1); }
    .card h2 { font-size: 1.125rem; margin-bottom: 1rem; color: #374151; }
    .grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(200px, 1fr)); gap: 1rem; }
    .metric { text-align: center; padding: 1rem; }
    .metric .value { font-size: 2rem; font-weight: bold; }
    .metric .label { color: #6b7280; font-size: 0.875rem; }
    .severity-critical { color: ${colors.critical}; }
    .severity-high { color: ${colors.high}; }
    .severity-medium { color: ${colors.medium}; }
    .severity-low { color: ${colors.low}; }
    .severity-info { color: ${colors.info}; }
    .badge { display: inline-block; padding: 0.25rem 0.5rem; border-radius: 4px; font-size: 0.75rem; font-weight: 600; }
    .badge-critical { background: ${colors.critical}20; color: ${colors.critical}; }
    .badge-high { background: ${colors.high}20; color: ${colors.high}; }
    .badge-medium { background: ${colors.medium}20; color: ${colors.medium}; }
    .badge-low { background: ${colors.low}20; color: ${colors.low}; }
    .badge-info { background: ${colors.info}20; color: ${colors.info}; }
    table { width: 100%; border-collapse: collapse; }
    th, td { padding: 0.75rem; text-align: left; border-bottom: 1px solid #e5e7eb; }
    th { background: #f9fafb; font-weight: 600; }
    .status-${report.summary.status} { border-left: 4px solid ${this.getStatusColor(report.summary.status, colors)}; }
    .score-circle { width: 120px; height: 120px; border-radius: 50%; background: conic-gradient(#10b981 ${report.metrics.securityScore * 3.6}deg, #e5e7eb 0deg); display: flex; align-items: center; justify-content: center; margin: 0 auto; }
    .score-inner { width: 100px; height: 100px; border-radius: 50%; background: white; display: flex; align-items: center; justify-content: center; flex-direction: column; }
    .score-value { font-size: 2rem; font-weight: bold; }
    .list { list-style: none; }
    .list li { padding: 0.5rem 0; border-bottom: 1px solid #f3f4f6; }
    .list li:last-child { border-bottom: none; }
  </style>
</head>
<body>
  <div class="container">
    <div class="header">
      <h1>${this.config.branding.title ?? 'Security Dashboard'}</h1>
      <p>${report.projectName} - Generated: ${report.generatedAt.toISOString()}</p>
    </div>

    <div class="card status-${report.summary.status}">
      <h2>Executive Summary</h2>
      <p><strong>${report.summary.statusMessage}</strong></p>
      <ul class="list" style="margin-top: 1rem;">
        ${report.summary.highlights.map(h => `<li>${h}</li>`).join('')}
      </ul>
    </div>

    <div class="grid">
      <div class="card">
        <h2>Security Score</h2>
        <div class="score-circle">
          <div class="score-inner">
            <div class="score-value">${report.metrics.securityScore}</div>
            <div class="label">/100</div>
          </div>
        </div>
      </div>

      <div class="card">
        <h2>Vulnerabilities by Severity</h2>
        <div class="metric">
          <div class="value severity-critical">${report.metrics.bySeverity.critical}</div>
          <div class="label">Critical</div>
        </div>
        <div class="metric">
          <div class="value severity-high">${report.metrics.bySeverity.high}</div>
          <div class="label">High</div>
        </div>
        <div class="metric">
          <div class="value severity-medium">${report.metrics.bySeverity.medium}</div>
          <div class="label">Medium</div>
        </div>
        <div class="metric">
          <div class="value severity-low">${report.metrics.bySeverity.low}</div>
          <div class="label">Low</div>
        </div>
      </div>
    </div>

    <div class="card">
      <h2>Top Vulnerabilities</h2>
      <table>
        <thead>
          <tr><th>Type</th><th>Severity</th><th>Count</th><th>Recommendation</th></tr>
        </thead>
        <tbody>
          ${report.topVulnerabilities.map(v => `
            <tr>
              <td>${v.type}</td>
              <td><span class="badge badge-${v.severity}">${v.severity.toUpperCase()}</span></td>
              <td>${v.count}</td>
              <td>${v.recommendation}</td>
            </tr>
          `).join('')}
        </tbody>
      </table>
    </div>

    <div class="card">
      <h2>Component Risks</h2>
      <table>
        <thead>
          <tr><th>Component</th><th>Vulnerabilities</th><th>Critical</th><th>High</th><th>Risk Score</th></tr>
        </thead>
        <tbody>
          ${report.componentRisks.map(c => `
            <tr>
              <td><code>${c.component}</code></td>
              <td>${c.vulnerabilityCount}</td>
              <td class="severity-critical">${c.criticalCount}</td>
              <td class="severity-high">${c.highCount}</td>
              <td>${c.riskScore}</td>
            </tr>
          `).join('')}
        </tbody>
      </table>
    </div>

    ${report.recommendations ? `
    <div class="card">
      <h2>Recommendations</h2>
      <ul class="list">
        ${report.recommendations.map(r => `
          <li>
            <span class="badge badge-${r.priority}">${r.priority.toUpperCase()}</span>
            <strong>${r.title}</strong>: ${r.description}
          </li>
        `).join('')}
      </ul>
    </div>
    ` : ''}
  </div>
</body>
</html>`;
  }

  /**
   * Export to Markdown format
   */
  private toMarkdown(report: DashboardReport): string {
    return `# Security Dashboard - ${report.projectName}

Generated: ${report.generatedAt.toISOString()}

## Executive Summary

**Status: ${report.summary.status.toUpperCase()}**

${report.summary.statusMessage}

### Highlights
${report.summary.highlights.map(h => `- ${h}`).join('\n')}

### Key Findings
${report.summary.keyFindings.map(f => `- ${f}`).join('\n')}

### Immediate Actions
${report.summary.immediateActions.map(a => `- ${a}`).join('\n')}

---

## Security Metrics

| Metric | Value |
|--------|-------|
| Security Score | ${report.metrics.securityScore}/100 |
| Risk Level | ${report.metrics.riskLevel} |
| Total Vulnerabilities | ${report.metrics.totalVulnerabilities} |

### By Severity

| Severity | Count |
|----------|-------|
| Critical | ${report.metrics.bySeverity.critical} |
| High | ${report.metrics.bySeverity.high} |
| Medium | ${report.metrics.bySeverity.medium} |
| Low | ${report.metrics.bySeverity.low} |
| Info | ${report.metrics.bySeverity.info} |

---

## Top Vulnerabilities

| Type | Severity | Count | Recommendation |
|------|----------|-------|----------------|
${report.topVulnerabilities.map(v => 
  `| ${v.type} | ${v.severity} | ${v.count} | ${v.recommendation} |`
).join('\n')}

---

## Component Risks

| Component | Vulnerabilities | Critical | High | Risk Score |
|-----------|-----------------|----------|------|------------|
${report.componentRisks.map(c => 
  `| \`${c.component}\` | ${c.vulnerabilityCount} | ${c.criticalCount} | ${c.highCount} | ${c.riskScore} |`
).join('\n')}

---

${report.recommendations ? `
## Recommendations

${report.recommendations.map(r => `
### [${r.priority.toUpperCase()}] ${r.title}

- **Category:** ${r.category}
- **Description:** ${r.description}
- **Impact:** ${r.impact}
- **Effort:** ${r.effort}
- **Affected:** ${r.affectedCount} items
`).join('\n')}
` : ''}

---

## Scan Summary

| Metric | Value |
|--------|-------|
| Total Scans | ${report.scanSummary.totalScans} |
| Files Scanned | ${report.scanSummary.filesScanned} |
| Last Scan | ${report.scanSummary.lastScanDate.toISOString()} |
| Coverage | ${report.scanSummary.coverage}% |
`;
  }

  /**
   * Get status color
   */
  private getStatusColor(
    status: ExecutiveSummary['status'],
    colors: NonNullable<DashboardBranding['colors']>
  ): string {
    const mapping: Record<ExecutiveSummary['status'], string> = {
      critical: colors.critical ?? '#dc2626',
      warning: colors.high ?? '#ea580c',
      attention: colors.medium ?? '#ca8a04',
      good: colors.low ?? '#16a34a',
      excellent: colors.info ?? '#2563eb',
    };
    return mapping[status];
  }
}

/**
 * Create security dashboard instance
 */
export function createSecurityDashboard(config: DashboardConfig): SecurityDashboard {
  return new SecurityDashboard(config);
}
