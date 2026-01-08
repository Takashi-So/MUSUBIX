/**
 * @fileoverview CVE Report Generator
 * @module @nahisaho/musubix-security/cve/report-generator
 * @description Generates vulnerability reports in Markdown, JSON, and SARIF formats
 * @requirements REQ-SEC-CVE-003 - CVE report generation with multiple formats
 * @design DES-SEC-CVE-003 - Report generator with SARIF 2.1.0 support
 * @task TSK-CVE-008 - レポート生成
 */

import type { ScanResult, DetectedVulnerability } from './vulnerability-scanner.js';

/**
 * Report output format
 */
export type ReportFormat = 'markdown' | 'json' | 'sarif';

/**
 * Report generator options
 */
export interface ReportOptions {
  /** Report title */
  title?: string;
  /** Include detailed vulnerability information */
  includeDetails?: boolean;
  /** Include remediation suggestions */
  includeRemediation?: boolean;
  /** Minimum severity to include */
  minSeverity?: 'CRITICAL' | 'HIGH' | 'MEDIUM' | 'LOW' | 'NONE';
  /** Group vulnerabilities by severity */
  groupBySeverity?: boolean;
  /** Include scan metadata */
  includeMetadata?: boolean;
  /** Project URL for SARIF */
  projectUrl?: string;
}

/**
 * SARIF 2.1.0 compatible report structure
 */
export interface SARIFReport {
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
  invocations: Array<{
    executionSuccessful: boolean;
    endTimeUtc: string;
  }>;
}

interface SARIFRule {
  id: string;
  name: string;
  shortDescription: { text: string };
  fullDescription: { text: string };
  helpUri?: string;
  defaultConfiguration: {
    level: 'error' | 'warning' | 'note' | 'none';
  };
  properties: {
    precision: string;
    'security-severity': string;
    tags: string[];
  };
}

interface SARIFResult {
  ruleId: string;
  level: 'error' | 'warning' | 'note' | 'none';
  message: { text: string };
  locations: Array<{
    physicalLocation: {
      artifactLocation: {
        uri: string;
        uriBaseId: string;
      };
    };
  }>;
  properties: {
    packageName: string;
    packageVersion: string;
    fixedVersion?: string;
    cvssScore?: number;
    cwes?: string[];
  };
}

/**
 * Severity level mapping
 */
const SEVERITY_ORDER: Record<string, number> = {
  CRITICAL: 0,
  HIGH: 1,
  MEDIUM: 2,
  LOW: 3,
  NONE: 4,
  UNKNOWN: 5,
};

/**
 * Get SARIF level from CVSS severity
 */
function getSARIFLevel(severity?: string): 'error' | 'warning' | 'note' | 'none' {
  switch (severity?.toUpperCase()) {
    case 'CRITICAL':
    case 'HIGH':
      return 'error';
    case 'MEDIUM':
      return 'warning';
    case 'LOW':
      return 'note';
    default:
      return 'none';
  }
}

/**
 * Get emoji for severity level
 */
function getSeverityEmoji(severity?: string): string {
  switch (severity?.toUpperCase()) {
    case 'CRITICAL':
      return '🔴';
    case 'HIGH':
      return '🟠';
    case 'MEDIUM':
      return '🟡';
    case 'LOW':
      return '🟢';
    default:
      return '⚪';
  }
}

/**
 * CVE Report Generator
 */
export class ReportGenerator {
  private readonly options: Required<ReportOptions>;

  constructor(options: ReportOptions = {}) {
    this.options = {
      title: options.title ?? 'Vulnerability Scan Report',
      includeDetails: options.includeDetails ?? true,
      includeRemediation: options.includeRemediation ?? true,
      minSeverity: options.minSeverity ?? 'NONE',
      groupBySeverity: options.groupBySeverity ?? true,
      includeMetadata: options.includeMetadata ?? true,
      projectUrl: options.projectUrl ?? '',
    };
  }

  /**
   * Generate report in specified format
   */
  generate(result: ScanResult, format: ReportFormat): string {
    const filteredResult = this.filterBySeverity(result);

    switch (format) {
      case 'markdown':
        return this.generateMarkdown(filteredResult);
      case 'json':
        return this.generateJSON(filteredResult);
      case 'sarif':
        return this.generateSARIF(filteredResult);
      default:
        throw new Error(`Unsupported format: ${format}`);
    }
  }

  /**
   * Filter vulnerabilities by minimum severity
   */
  private filterBySeverity(result: ScanResult): ScanResult {
    const minLevel = SEVERITY_ORDER[this.options.minSeverity] ?? 4;
    
    const filtered = result.vulnerabilities.filter(vuln => {
      const level = SEVERITY_ORDER[vuln.severity?.toUpperCase() ?? 'UNKNOWN'] ?? 5;
      return level <= minLevel;
    });

    // Recalculate summary
    const summary = {
      total: filtered.length,
      critical: 0,
      high: 0,
      medium: 0,
      low: 0,
      none: 0,
    };

    for (const vuln of filtered) {
      const sev = vuln.severity?.toLowerCase() as keyof typeof summary;
      if (sev && sev in summary && sev !== 'total') {
        summary[sev]++;
      }
    }

    return {
      ...result,
      vulnerabilities: filtered,
      summary,
    };
  }

  /**
   * Generate Markdown report
   */
  private generateMarkdown(result: ScanResult): string {
    const lines: string[] = [];

    // Title
    lines.push(`# ${this.options.title}`);
    lines.push('');

    // Metadata
    if (this.options.includeMetadata) {
      lines.push('## 📊 Scan Summary');
      lines.push('');
      lines.push(`| Metric | Value |`);
      lines.push(`|--------|-------|`);
      lines.push(`| Project | ${result.projectName ?? 'Unknown'} |`);
      lines.push(`| Scan Time | ${result.scanTimestamp} |`);
      lines.push(`| Duration | ${result.durationMs}ms |`);
      lines.push(`| Packages Scanned | ${result.totalPackages} |`);
      lines.push(`| Total Vulnerabilities | ${result.summary.total} |`);
      lines.push('');
    }

    // Severity breakdown
    lines.push('## 🎯 Severity Breakdown');
    lines.push('');
    lines.push(`| Severity | Count |`);
    lines.push(`|----------|-------|`);
    lines.push(`| 🔴 Critical | ${result.summary.critical} |`);
    lines.push(`| 🟠 High | ${result.summary.high} |`);
    lines.push(`| 🟡 Medium | ${result.summary.medium} |`);
    lines.push(`| 🟢 Low | ${result.summary.low} |`);
    lines.push('');

    // Vulnerabilities
    if (result.vulnerabilities.length === 0) {
      lines.push('## ✅ No Vulnerabilities Found');
      lines.push('');
      lines.push('Great news! No vulnerabilities were detected in the scanned packages.');
      return lines.join('\n');
    }

    lines.push('## 🔒 Detected Vulnerabilities');
    lines.push('');

    if (this.options.groupBySeverity) {
      const grouped = this.groupBySeverity(result.vulnerabilities);
      
      for (const [severity, vulns] of grouped) {
        if (vulns.length === 0) continue;
        
        lines.push(`### ${getSeverityEmoji(severity)} ${severity} (${vulns.length})`);
        lines.push('');
        
        for (const vuln of vulns) {
          lines.push(...this.formatVulnerabilityMarkdown(vuln));
        }
      }
    } else {
      for (const vuln of result.vulnerabilities) {
        lines.push(...this.formatVulnerabilityMarkdown(vuln));
      }
    }

    return lines.join('\n');
  }

  /**
   * Format a single vulnerability as Markdown
   */
  private formatVulnerabilityMarkdown(vuln: DetectedVulnerability): string[] {
    const lines: string[] = [];

    lines.push(`#### ${vuln.cveId}`);
    lines.push('');
    lines.push(`**Package:** \`${vuln.packageName}@${vuln.installedVersion}\``);
    
    if (vuln.cvssScore !== undefined) {
      lines.push(`**CVSS Score:** ${vuln.cvssScore.toFixed(1)} (${vuln.severity})`);
    }

    if (this.options.includeDetails) {
      lines.push('');
      lines.push(`**Description:** ${vuln.description ?? 'No description available'}`);
      
      if (vuln.cwes && vuln.cwes.length > 0) {
        lines.push(`**CWEs:** ${vuln.cwes.join(', ')}`);
      }

      if (vuln.references && vuln.references.length > 0) {
        lines.push('');
        lines.push('**References:**');
        for (const ref of vuln.references.slice(0, 3)) {
          lines.push(`- [Link](${ref})`);
        }
      }
    }

    if (this.options.includeRemediation && vuln.fixedVersion) {
      lines.push('');
      lines.push(`**✅ Fix Available:** Upgrade to \`${vuln.packageName}@${vuln.fixedVersion}\` or later`);
    }

    lines.push('');
    lines.push('---');
    lines.push('');

    return lines;
  }

  /**
   * Group vulnerabilities by severity
   */
  private groupBySeverity(
    vulns: DetectedVulnerability[]
  ): Map<string, DetectedVulnerability[]> {
    const groups = new Map<string, DetectedVulnerability[]>([
      ['CRITICAL', []],
      ['HIGH', []],
      ['MEDIUM', []],
      ['LOW', []],
    ]);

    for (const vuln of vulns) {
      const severity = vuln.severity?.toUpperCase() ?? 'UNKNOWN';
      const group = groups.get(severity) ?? [];
      group.push(vuln);
      if (!groups.has(severity)) {
        groups.set(severity, group);
      }
    }

    return groups;
  }

  /**
   * Generate JSON report
   */
  private generateJSON(result: ScanResult): string {
    const report = {
      meta: {
        title: this.options.title,
        generated: new Date().toISOString(),
        generator: 'MUSUBIX Security Scanner',
        version: '2.0.0',
      },
      scan: {
        project: result.projectName,
        timestamp: result.scanTimestamp,
        durationMs: result.durationMs,
        totalPackages: result.totalPackages,
      },
      summary: result.summary,
      vulnerabilities: result.vulnerabilities.map(vuln => ({
        id: vuln.cveId,
        package: {
          name: vuln.packageName,
          version: vuln.installedVersion,
          fixedVersion: vuln.fixedVersion,
        },
        severity: vuln.severity,
        cvssScore: vuln.cvssScore,
        description: vuln.description,
        cwes: vuln.cwes,
        references: vuln.references,
      })),
    };

    return JSON.stringify(report, null, 2);
  }

  /**
   * Generate SARIF 2.1.0 report
   */
  private generateSARIF(result: ScanResult): string {
    const rules: SARIFRule[] = [];
    const results: SARIFResult[] = [];
    const ruleIdSet = new Set<string>();

    for (const vuln of result.vulnerabilities) {
      // Add rule if not already added
      if (!ruleIdSet.has(vuln.cveId)) {
        ruleIdSet.add(vuln.cveId);
        rules.push({
          id: vuln.cveId,
          name: `Vulnerability in ${vuln.packageName}`,
          shortDescription: { text: vuln.description ?? `CVE ${vuln.cveId}` },
          fullDescription: { text: vuln.description ?? `Security vulnerability ${vuln.cveId}` },
          helpUri: `https://nvd.nist.gov/vuln/detail/${vuln.cveId}`,
          defaultConfiguration: {
            level: getSARIFLevel(vuln.severity),
          },
          properties: {
            precision: 'high',
            'security-severity': (vuln.cvssScore ?? 0).toString(),
            tags: [
              'security',
              'vulnerability',
              vuln.severity?.toLowerCase() ?? 'unknown',
              ...(vuln.cwes ?? []),
            ],
          },
        });
      }

      // Add result
      results.push({
        ruleId: vuln.cveId,
        level: getSARIFLevel(vuln.severity),
        message: {
          text: `Vulnerable package ${vuln.packageName}@${vuln.installedVersion}: ${vuln.description ?? vuln.cveId}`,
        },
        locations: [
          {
            physicalLocation: {
              artifactLocation: {
                uri: 'package.json',
                uriBaseId: '%SRCROOT%',
              },
            },
          },
        ],
        properties: {
          packageName: vuln.packageName,
          packageVersion: vuln.installedVersion,
          fixedVersion: vuln.fixedVersion,
          cvssScore: vuln.cvssScore,
          cwes: vuln.cwes,
        },
      });
    }

    const sarif: SARIFReport = {
      $schema: 'https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json',
      version: '2.1.0',
      runs: [
        {
          tool: {
            driver: {
              name: 'MUSUBIX Security Scanner',
              version: '2.0.0',
              informationUri: 'https://github.com/nahisaho/musubix',
              rules,
            },
          },
          results,
          invocations: [
            {
              executionSuccessful: true,
              endTimeUtc: result.scanTimestamp,
            },
          ],
        },
      ],
    };

    return JSON.stringify(sarif, null, 2);
  }
}

/**
 * Quick report generation function
 */
export function generateReport(
  result: ScanResult,
  format: ReportFormat,
  options?: ReportOptions
): string {
  const generator = new ReportGenerator(options);
  return generator.generate(result, format);
}

/**
 * Generate and save report to file
 */
export async function generateReportToFile(
  result: ScanResult,
  filePath: string,
  format: ReportFormat,
  options?: ReportOptions
): Promise<void> {
  const { writeFile } = await import('node:fs/promises');
  const report = generateReport(result, format, options);
  await writeFile(filePath, report, 'utf-8');
}

/**
 * Determine format from file extension
 */
export function getFormatFromExtension(filePath: string): ReportFormat {
  const ext = filePath.toLowerCase().split('.').pop();
  switch (ext) {
    case 'md':
    case 'markdown':
      return 'markdown';
    case 'sarif':
      return 'sarif';
    case 'json':
    default:
      return 'json';
  }
}
