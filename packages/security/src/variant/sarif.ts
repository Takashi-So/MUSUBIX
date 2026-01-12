/**
 * @fileoverview SARIF Report Generator
 * @module @nahisaho/musubix-security/variant/sarif
 * @trace TSK-026, REQ-SEC-VARIANT-004
 */

import type {
  VulnerabilityFinding,
  VulnerabilitySeverity,
  ScanResult,
  SARIFReport,
  SARIFRun,
  SARIFRule,
  SARIFResult,
  SARIFLocation,
  SARIFCodeFlow,
} from '../types/variant.js';
import { CWE_DATABASE } from './model.js';

// ============================================================================
// Constants
// ============================================================================

const TOOL_INFO = {
  name: 'musubix-security',
  fullName: 'MUSUBIX Security Analyzer',
  version: '3.0.11',
  informationUri: 'https://github.com/nahisaho/MUSUBIX',
};

const SARIF_SCHEMA = 'https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json';

// ============================================================================
// SARIF Generator
// ============================================================================

/**
 * SARIF Report Generator
 */
export class SARIFGenerator {
  /**
   * Generate SARIF report from scan result
   */
  generate(scanResult: ScanResult): SARIFReport {
    return {
      version: '2.1.0',
      $schema: SARIF_SCHEMA,
      runs: [this.createRun(scanResult)],
    };
  }

  /**
   * Generate SARIF report from findings
   */
  generateFromFindings(findings: VulnerabilityFinding[]): SARIFReport {
    return {
      version: '2.1.0',
      $schema: SARIF_SCHEMA,
      runs: [this.createRunFromFindings(findings)],
    };
  }

  /**
   * Create SARIF run from scan result
   */
  private createRun(scanResult: ScanResult): SARIFRun {
    const rules = this.createRules(scanResult.findings);
    const results = this.createResults(scanResult.findings, rules);

    return {
      tool: {
        driver: {
          name: TOOL_INFO.name,
          version: TOOL_INFO.version,
          informationUri: TOOL_INFO.informationUri,
          rules,
        },
      },
      results,
    };
  }

  /**
   * Create SARIF run from findings
   */
  private createRunFromFindings(findings: VulnerabilityFinding[]): SARIFRun {
    const rules = this.createRules(findings);
    const results = this.createResults(findings, rules);

    return {
      tool: {
        driver: {
          name: TOOL_INFO.name,
          version: TOOL_INFO.version,
          informationUri: TOOL_INFO.informationUri,
          rules,
        },
      },
      results,
    };
  }

  /**
   * Create SARIF rules from findings
   */
  private createRules(findings: VulnerabilityFinding[]): SARIFRule[] {
    const ruleMap = new Map<string, SARIFRule>();

    for (const finding of findings) {
      if (ruleMap.has(finding.ruleId)) continue;

      const cweId = finding.cwe[0];
      const cweKey = `CWE-${cweId}`;
      const cweInfo = CWE_DATABASE[cweKey];

      const rule: SARIFRule = {
        id: finding.ruleId,
        name: finding.ruleName,
        shortDescription: {
          text: finding.ruleName,
        },
        fullDescription: {
          text: cweInfo?.description ?? finding.message,
        },
        defaultConfiguration: {
          level: this.severityToLevel(finding.severity),
        },
        help: {
          text: `See CWE-${cweId} for more information.`,
          markdown: `See [CWE-${cweId}](https://cwe.mitre.org/data/definitions/${cweId}.html) for more information.`,
        },
        properties: {
          tags: [finding.ruleId, cweKey],
          'security-severity': this.severityToScore(finding.severity).toString(),
        },
      };

      ruleMap.set(finding.ruleId, rule);
    }

    return Array.from(ruleMap.values());
  }

  /**
   * Create SARIF results from findings
   */
  private createResults(findings: VulnerabilityFinding[], rules: SARIFRule[]): SARIFResult[] {
    const ruleIndex = new Map<string, number>();
    rules.forEach((rule, index) => ruleIndex.set(rule.id, index));

    return findings.map((finding) => {
      const result: SARIFResult = {
        ruleId: finding.ruleId,
        ruleIndex: ruleIndex.get(finding.ruleId),
        level: this.severityToLevel(finding.severity),
        message: {
          text: finding.message,
        },
        locations: [this.createLocation(finding)],
      };

      // Add code flows for taint paths
      if (finding.taintPath) {
        result.codeFlows = [this.createCodeFlow(finding)];
      }

      return result;
    });
  }

  /**
   * Create SARIF location
   */
  private createLocation(finding: VulnerabilityFinding): SARIFLocation {
    return {
      physicalLocation: {
        artifactLocation: {
          uri: this.toFileUri(finding.location.file),
        },
        region: {
          startLine: finding.location.startLine,
          startColumn: finding.location.startColumn,
          endLine: finding.location.endLine,
          endColumn: finding.location.endColumn,
        },
      },
    };
  }

  /**
   * Create SARIF code flow from taint path
   */
  private createCodeFlow(finding: VulnerabilityFinding): SARIFCodeFlow {
    if (!finding.taintPath) {
      return { threadFlows: [] };
    }

    const locations: Array<{ location: SARIFLocation; message?: { text: string } }> = [];

    // Add source
    locations.push({
      location: {
        physicalLocation: {
          artifactLocation: {
            uri: this.toFileUri(finding.taintPath.source.location.file),
          },
          region: {
            startLine: finding.taintPath.source.location.startLine,
            startColumn: finding.taintPath.source.location.startColumn,
          },
        },
      },
      message: {
        text: `Source: ${finding.taintPath.source.snippet || 'user input'}`,
      },
    });

    // Add intermediate nodes
    for (const node of finding.taintPath.path) {
      locations.push({
        location: {
          physicalLocation: {
            artifactLocation: {
              uri: this.toFileUri(node.location.file),
            },
            region: {
              startLine: node.location.startLine,
              startColumn: node.location.startColumn,
            },
          },
        },
        message: {
          text: node.description ?? 'Data flows through here',
        },
      });
    }

    // Add sink
    locations.push({
      location: {
        physicalLocation: {
          artifactLocation: {
            uri: this.toFileUri(finding.taintPath.sink.location.file),
          },
          region: {
            startLine: finding.taintPath.sink.location.startLine,
            startColumn: finding.taintPath.sink.location.startColumn,
          },
        },
      },
      message: {
        text: `Sink: ${finding.taintPath.sink.snippet || 'dangerous operation'}`,
      },
    });

    return {
      threadFlows: [{ locations }],
    };
  }

  /**
   * Convert severity to SARIF level
   */
  private severityToLevel(severity: VulnerabilitySeverity): 'error' | 'warning' | 'note' | 'none' {
    switch (severity) {
      case 'critical':
      case 'high':
        return 'error';
      case 'medium':
        return 'warning';
      case 'low':
      case 'info':
        return 'note';
      default:
        return 'none';
    }
  }

  /**
   * Convert severity to numeric score
   */
  private severityToScore(severity: VulnerabilitySeverity): number {
    switch (severity) {
      case 'critical':
        return 9.0;
      case 'high':
        return 7.0;
      case 'medium':
        return 5.0;
      case 'low':
        return 3.0;
      case 'info':
        return 1.0;
      default:
        return 0.0;
    }
  }

  /**
   * Convert file path to URI
   */
  private toFileUri(filePath: string): string {
    // Normalize path separators
    const normalized = filePath.replace(/\\/g, '/');

    // If already a URI, return as-is
    if (normalized.startsWith('file://')) {
      return normalized;
    }

    // Make relative paths
    if (normalized.startsWith('/')) {
      return normalized.substring(1);
    }

    return normalized;
  }
}

/**
 * Create SARIF generator
 */
export function createSARIFGenerator(): SARIFGenerator {
  return new SARIFGenerator();
}

/**
 * Generate SARIF report
 */
export function generateSARIF(scanResult: ScanResult): SARIFReport {
  return new SARIFGenerator().generate(scanResult);
}

/**
 * Generate SARIF from findings
 */
export function generateSARIFFromFindings(findings: VulnerabilityFinding[]): SARIFReport {
  return new SARIFGenerator().generateFromFindings(findings);
}
