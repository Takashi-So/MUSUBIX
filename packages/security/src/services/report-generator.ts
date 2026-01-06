/**
 * @fileoverview Report generator service - generates security reports in multiple formats
 * @module @nahisaho/musubix-security/services/report-generator
 * @trace REQ-SEC-REP-001
 */

import * as fs from 'node:fs/promises';
import * as path from 'node:path';

import type {
  Vulnerability,
  ScanResult,
  Severity,
  Fix,
  AuditResult,
  TaintResult,
  SecretScanResult,
  ReportConfig,
  ReportFormat,
} from '../types/index.js';

export type { ReportFormat };

/**
 * Combined scan results for report generation
 */
export interface CombinedResults {
  vulnerabilities: ScanResult;
  dependencies?: AuditResult;
  taint?: TaintResult;
  secrets?: SecretScanResult;
  fixes?: Fix[];
}

/**
 * Report metadata
 */
export interface ReportMetadata {
  title: string;
  project?: string;
  scanTime: Date;
  duration: number;
  targetPath: string;
}

/**
 * SARIF report structure (simplified)
 */
interface SARIFReport {
  $schema: string;
  version: string;
  runs: SARIFRun[];
}

interface SARIFRun {
  tool: {
    driver: {
      name: string;
      version: string;
      informationUri: string;
      rules: SARIFRule[];
    };
  };
  results: SARIFResult[];
}

interface SARIFRule {
  id: string;
  name: string;
  shortDescription: { text: string };
  fullDescription?: { text: string };
  helpUri?: string;
  defaultConfiguration: {
    level: 'error' | 'warning' | 'note';
  };
}

interface SARIFResult {
  ruleId: string;
  level: 'error' | 'warning' | 'note';
  message: { text: string };
  locations: Array<{
    physicalLocation: {
      artifactLocation: { uri: string };
      region?: {
        startLine: number;
        startColumn?: number;
        endLine?: number;
        endColumn?: number;
      };
    };
  }>;
}

/**
 * Report generator class
 */
export class ReportGenerator {
  private config: Required<Pick<ReportConfig, 'format' | 'includeCode' | 'includeFixes' | 'groupBy' | 'sortBy'>>;

  constructor(config: Partial<ReportConfig> = {}) {
    this.config = {
      format: Array.isArray(config.format) ? config.format : config.format ? [config.format] : ['json'],
      includeCode: config.includeCode ?? config.includeCodeSnippets ?? true,
      includeFixes: config.includeFixes ?? true,
      groupBy: config.groupBy ?? 'severity',
      sortBy: config.sortBy ?? 'severity',
    };
  }

  /**
   * Generate report in specified format
   */
  async generate(
    results: CombinedResults,
    metadata: ReportMetadata,
    format?: ReportFormat
  ): Promise<string> {
    const reportFormat = format ?? (this.config.format[0] as ReportFormat);

    switch (reportFormat) {
      case 'json':
        return this.generateJSON(results, metadata);
      case 'sarif':
        return this.generateSARIF(results, metadata);
      case 'markdown':
        return this.generateMarkdown(results, metadata);
      case 'html':
        return this.generateHTML(results, metadata);
      default:
        throw new Error(`Unsupported report format: ${reportFormat}`);
    }
  }

  /**
   * Generate and save report to file
   */
  async generateToFile(
    results: CombinedResults,
    metadata: ReportMetadata,
    outputPath: string,
    format?: ReportFormat
  ): Promise<string> {
    const content = await this.generate(results, metadata, format);
    
    // Ensure directory exists
    const dir = path.dirname(outputPath);
    await fs.mkdir(dir, { recursive: true });
    
    // Write file
    await fs.writeFile(outputPath, content, 'utf-8');
    
    return outputPath;
  }

  /**
   * Generate all configured formats
   */
  async generateAll(
    results: CombinedResults,
    metadata: ReportMetadata
  ): Promise<Map<ReportFormat, string>> {
    const reports = new Map<ReportFormat, string>();
    const formats = Array.isArray(this.config.format) ? this.config.format : [this.config.format];

    for (const format of formats) {
      const content = await this.generate(results, metadata, format);
      reports.set(format, content);
    }

    return reports;
  }

  /**
   * Generate JSON report
   */
  private generateJSON(results: CombinedResults, metadata: ReportMetadata): string {
    const report = {
      ...metadata,
      scanTime: metadata.scanTime.toISOString(),
      summary: this.generateSummary(results),
      vulnerabilities: this.formatVulnerabilities(results.vulnerabilities.vulnerabilities),
      dependencies: results.dependencies,
      taint: results.taint,
      secrets: results.secrets ? {
        ...results.secrets,
        secrets: results.secrets.secrets.map(s => ({
          ...s,
          value: s.maskedValue, // Only include masked value
        })),
      } : undefined,
      fixes: this.config.includeFixes ? results.fixes : undefined,
    };

    return JSON.stringify(report, null, 2);
  }

  /**
   * Generate SARIF report
   */
  private generateSARIF(results: CombinedResults, _metadata: ReportMetadata): string {
    const vulnerabilities = results.vulnerabilities.vulnerabilities;
    
    // Create rules from unique vulnerability types
    const ruleMap = new Map<string, SARIFRule>();
    for (const vuln of vulnerabilities) {
      if (!ruleMap.has(vuln.ruleId)) {
        const cweId = vuln.cwes[0];
        ruleMap.set(vuln.ruleId, {
          id: vuln.ruleId,
          name: vuln.type,
          shortDescription: { text: vuln.type },
          fullDescription: { text: vuln.description },
          helpUri: cweId ? `https://cwe.mitre.org/data/definitions/${cweId.replace('CWE-', '')}.html` : undefined,
          defaultConfiguration: {
            level: this.severityToSARIFLevel(vuln.severity),
          },
        });
      }
    }

    // Create results
    const sarifResults: SARIFResult[] = vulnerabilities.map((vuln) => ({
      ruleId: vuln.ruleId,
      level: this.severityToSARIFLevel(vuln.severity),
      message: { text: vuln.description },
      locations: [{
        physicalLocation: {
          artifactLocation: { uri: vuln.location.file },
          region: {
            startLine: vuln.location.startLine,
            startColumn: vuln.location.startColumn,
            endLine: vuln.location.endLine,
            endColumn: vuln.location.endColumn,
          },
        },
      }],
    }));

    const sarifReport: SARIFReport = {
      $schema: 'https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json',
      version: '2.1.0',
      runs: [{
        tool: {
          driver: {
            name: 'musubix-security',
            version: '1.8.0',
            informationUri: 'https://github.com/nahisaho/musubix',
            rules: Array.from(ruleMap.values()),
          },
        },
        results: sarifResults,
      }],
    };

    return JSON.stringify(sarifReport, null, 2);
  }

  /**
   * Generate Markdown report
   */
  private generateMarkdown(results: CombinedResults, metadata: ReportMetadata): string {
    const summary = this.generateSummary(results);
    const vulnerabilities = this.formatVulnerabilities(results.vulnerabilities.vulnerabilities);
    
    let md = `# Security Scan Report

## Summary

- **Project**: ${metadata.project ?? 'N/A'}
- **Target**: ${metadata.targetPath}
- **Scan Time**: ${metadata.scanTime.toISOString()}
- **Duration**: ${metadata.duration}ms

### Findings Overview

| Severity | Count |
|----------|-------|
| Critical | ${summary.critical} |
| High | ${summary.high} |
| Medium | ${summary.medium} |
| Low | ${summary.low} |
| Info | ${summary.info} |
| **Total** | **${summary.total}** |

`;

    // Group vulnerabilities by severity
    const grouped = this.groupBySeverity(vulnerabilities);

    for (const severity of ['critical', 'high', 'medium', 'low', 'info'] as Severity[]) {
      const vulns = grouped.get(severity) || [];
      if (vulns.length === 0) continue;

      md += `## ${severity.toUpperCase()} Severity (${vulns.length})\n\n`;

      for (const vuln of vulns) {
        md += `### ${vuln.type}\n\n`;
        md += `- **Rule**: ${vuln.ruleId}\n`;
        md += `- **File**: ${vuln.location.file}:${vuln.location.startLine}\n`;
        md += `- **CWE**: ${vuln.cwes[0] ?? 'N/A'}\n`;
        md += `- **OWASP**: ${vuln.owasp?.[0] ?? 'N/A'}\n\n`;
        md += `${vuln.description}\n\n`;
        
        if (this.config.includeCode && vuln.codeSnippet) {
          md += '```\n' + vuln.codeSnippet + '\n```\n\n';
        }

        if (vuln.recommendation) {
          md += `**Remediation**: ${vuln.recommendation}\n\n`;
        }
      }
    }

    // Dependencies section
    if (results.dependencies) {
      md += `## Dependency Audit\n\n`;
      md += `- **Vulnerabilities Found**: ${results.dependencies.vulnerableDependencies.length}\n`;
      md += `- **Audit Duration**: ${results.dependencies.duration}ms\n\n`;

      if (results.dependencies.vulnerableDependencies.length > 0) {
        md += `| Package | Version | Severity | Title |\n`;
        md += `|---------|---------|----------|-------|\n`;
        for (const dep of results.dependencies.vulnerableDependencies) {
          md += `| ${dep.name} | ${dep.installedVersion} | ${dep.highestSeverity} | ${dep.vulnerabilities[0]?.title ?? 'N/A'} |\n`;
        }
        md += '\n';
      }
    }

    // Secrets section
    if (results.secrets && results.secrets.summary.total > 0) {
      md += `## Secrets Detected\n\n`;
      md += `⚠️ **${results.secrets.summary.total} potential secrets found**\n\n`;
      
      for (const secret of results.secrets.secrets) {
        md += `- **${secret.type}** in ${secret.location.file}:${secret.location.startLine}\n`;
      }
      md += '\n';
    }

    // Taint analysis section
    if (results.taint && results.taint.unsafePaths.length > 0) {
      md += `## Taint Analysis\n\n`;
      md += `- **Tainted Paths**: ${results.taint.unsafePaths.length}\n\n`;
    }

    return md;
  }

  /**
   * Generate HTML report
   */
  private generateHTML(results: CombinedResults, metadata: ReportMetadata): string {
    const summary = this.generateSummary(results);
    const vulnerabilities = this.formatVulnerabilities(results.vulnerabilities.vulnerabilities);

    return `<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Security Scan Report - ${metadata.project ?? metadata.targetPath}</title>
  <style>
    :root {
      --critical: #d63031;
      --high: #e17055;
      --medium: #fdcb6e;
      --low: #00cec9;
      --info: #74b9ff;
      --bg: #f5f6fa;
      --card: #ffffff;
      --text: #2d3436;
    }
    body {
      font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
      background: var(--bg);
      color: var(--text);
      margin: 0;
      padding: 20px;
    }
    .container {
      max-width: 1200px;
      margin: 0 auto;
    }
    h1 { color: var(--text); }
    .card {
      background: var(--card);
      border-radius: 8px;
      padding: 20px;
      margin-bottom: 20px;
      box-shadow: 0 2px 4px rgba(0,0,0,0.1);
    }
    .summary-grid {
      display: grid;
      grid-template-columns: repeat(5, 1fr);
      gap: 10px;
      margin-bottom: 20px;
    }
    .summary-item {
      text-align: center;
      padding: 15px;
      border-radius: 8px;
      color: white;
    }
    .summary-item.critical { background: var(--critical); }
    .summary-item.high { background: var(--high); }
    .summary-item.medium { background: var(--medium); color: var(--text); }
    .summary-item.low { background: var(--low); }
    .summary-item.info { background: var(--info); }
    .summary-item .count { font-size: 2em; font-weight: bold; }
    .summary-item .label { font-size: 0.9em; text-transform: uppercase; }
    .vuln {
      border-left: 4px solid;
      padding-left: 15px;
      margin-bottom: 15px;
    }
    .vuln.critical { border-color: var(--critical); }
    .vuln.high { border-color: var(--high); }
    .vuln.medium { border-color: var(--medium); }
    .vuln.low { border-color: var(--low); }
    .vuln.info { border-color: var(--info); }
    .vuln-title {
      font-weight: bold;
      font-size: 1.1em;
    }
    .vuln-meta {
      color: #636e72;
      font-size: 0.9em;
      margin: 5px 0;
    }
    pre {
      background: #2d3436;
      color: #dfe6e9;
      padding: 15px;
      border-radius: 4px;
      overflow-x: auto;
    }
    .badge {
      display: inline-block;
      padding: 2px 8px;
      border-radius: 4px;
      font-size: 0.8em;
      font-weight: bold;
    }
    .badge.critical { background: var(--critical); color: white; }
    .badge.high { background: var(--high); color: white; }
    .badge.medium { background: var(--medium); color: var(--text); }
    .badge.low { background: var(--low); color: white; }
    .badge.info { background: var(--info); color: white; }
  </style>
</head>
<body>
  <div class="container">
    <h1>🔒 Security Scan Report</h1>
    
    <div class="card">
      <h2>Summary</h2>
      <p><strong>Target:</strong> ${this.escapeHtml(metadata.targetPath)}</p>
      <p><strong>Scan Time:</strong> ${metadata.scanTime.toISOString()}</p>
      <p><strong>Duration:</strong> ${metadata.duration}ms</p>
      
      <div class="summary-grid">
        <div class="summary-item critical">
          <div class="count">${summary.critical}</div>
          <div class="label">Critical</div>
        </div>
        <div class="summary-item high">
          <div class="count">${summary.high}</div>
          <div class="label">High</div>
        </div>
        <div class="summary-item medium">
          <div class="count">${summary.medium}</div>
          <div class="label">Medium</div>
        </div>
        <div class="summary-item low">
          <div class="count">${summary.low}</div>
          <div class="label">Low</div>
        </div>
        <div class="summary-item info">
          <div class="count">${summary.info}</div>
          <div class="label">Info</div>
        </div>
      </div>
    </div>

    <div class="card">
      <h2>Vulnerabilities</h2>
      ${vulnerabilities.map(vuln => `
        <div class="vuln ${vuln.severity}">
          <div class="vuln-title">
            <span class="badge ${vuln.severity}">${vuln.severity.toUpperCase()}</span>
            ${this.escapeHtml(vuln.type)}
          </div>
          <div class="vuln-meta">
            ${this.escapeHtml(vuln.location.file)}:${vuln.location.startLine} | 
            ${vuln.cwes[0] ?? 'N/A'} | 
            ${vuln.owasp?.[0] ?? 'N/A'}
          </div>
          <p>${this.escapeHtml(vuln.description)}</p>
          ${vuln.codeSnippet && this.config.includeCode ? `<pre>${this.escapeHtml(vuln.codeSnippet)}</pre>` : ''}
          ${vuln.recommendation ? `<p><strong>Remediation:</strong> ${this.escapeHtml(vuln.recommendation)}</p>` : ''}
        </div>
      `).join('')}
    </div>
  </div>
</body>
</html>`;
  }

  /**
   * Generate summary statistics
   */
  private generateSummary(results: CombinedResults): {
    critical: number;
    high: number;
    medium: number;
    low: number;
    info: number;
    total: number;
  } {
    const vulns = results.vulnerabilities.vulnerabilities;
    const summary = {
      critical: 0,
      high: 0,
      medium: 0,
      low: 0,
      info: 0,
      total: vulns.length,
    };

    for (const vuln of vulns) {
      summary[vuln.severity]++;
    }

    return summary;
  }

  /**
   * Format vulnerabilities based on config
   */
  private formatVulnerabilities(vulnerabilities: Vulnerability[]): Vulnerability[] {
    let formatted = [...vulnerabilities];

    // Sort
    if (this.config.sortBy === 'severity') {
      const severityOrder: Record<Severity, number> = {
        critical: 0,
        high: 1,
        medium: 2,
        low: 3,
        info: 4,
      };
      formatted.sort((a, b) => severityOrder[a.severity] - severityOrder[b.severity]);
    } else if (this.config.sortBy === 'file') {
      formatted.sort((a, b) => a.location.file.localeCompare(b.location.file));
    }

    return formatted;
  }

  /**
   * Group vulnerabilities by severity
   */
  private groupBySeverity(vulnerabilities: Vulnerability[]): Map<Severity, Vulnerability[]> {
    const grouped = new Map<Severity, Vulnerability[]>();
    
    for (const vuln of vulnerabilities) {
      const list = grouped.get(vuln.severity) || [];
      list.push(vuln);
      grouped.set(vuln.severity, list);
    }

    return grouped;
  }

  /**
   * Convert severity to SARIF level
   */
  private severityToSARIFLevel(severity: Severity): 'error' | 'warning' | 'note' {
    switch (severity) {
      case 'critical':
      case 'high':
        return 'error';
      case 'medium':
        return 'warning';
      case 'low':
      case 'info':
        return 'note';
    }
  }

  /**
   * Escape HTML entities
   */
  private escapeHtml(str: string): string {
    return str
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&#039;');
  }
}

/**
 * Create a report generator
 */
export function createReportGenerator(config?: Partial<ReportConfig>): ReportGenerator {
  return new ReportGenerator(config);
}
