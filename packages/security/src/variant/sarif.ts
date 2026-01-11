/**
 * @fileoverview SARIF Report Generator
 * @module @nahisaho/musubix-security/variant/sarif
 * @trace TSK-026, REQ-SEC-VARIANT-004
 */

import type {
  VulnerabilityFinding,
  ScanResult,
  SARIFReport,
  SARIFRun,
  SARIFResult,
  SARIFRule,
  SARIFLocation,
  SARIFArtifactLocation,
  SARIFPhysicalLocation,
  SARIFRegion,
  SARIFMessage,
  SARIFCodeFlow,
  SARIFThreadFlow,
  SARIFThreadFlowLocation,
} from '../types/variant.js';
import { CWE_DATABASE } from './model.js';

/**
 * SARIF version
 */
const SARIF_VERSION = '2.1.0';

/**
 * SARIF schema URI
 */
const SARIF_SCHEMA = 'https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json';

/**
 * Tool information
 */
const TOOL_INFO = {
  name: 'musubix-security',
  fullName: 'MUSUBIX Security Scanner',
  version: '3.0.10',
  informationUri: 'https://github.com/nahisaho/musubix',
  organization: 'MUSUBIX',
};

/**
 * SARIF Report Generator
 */
export class SARIFGenerator {
  /**
   * Generate SARIF report from scan result
   */
  generate(scanResult: ScanResult): SARIFReport {
    const rules = this.generateRules(scanResult.findings);
    const results = this.generateResults(scanResult.findings);

    const run: SARIFRun = {
      tool: {
        driver: {
          name: TOOL_INFO.name,
          fullName: TOOL_INFO.fullName,
          version: TOOL_INFO.version,
          informationUri: TOOL_INFO.informationUri,
          organization: TOOL_INFO.organization,
          rules,
        },
      },
      results,
      invocations: [
        {
          executionSuccessful: true,
          startTimeUtc: scanResult.metadata.startTime,
          endTimeUtc: scanResult.metadata.endTime,
          workingDirectory: {
            uri: this.toFileUri(scanResult.metadata.rootPath),
          },
        },
      ],
    };

    return {
      $schema: SARIF_SCHEMA,
      version: SARIF_VERSION,
      runs: [run],
    };
  }

  /**
   * Generate SARIF rules from findings
   */
  private generateRules(findings: VulnerabilityFinding[]): SARIFRule[] {
    const ruleMap = new Map<string, SARIFRule>();

    for (const finding of findings) {
      if (ruleMap.has(finding.modelId)) continue;

      const cweInfo = CWE_DATABASE[finding.cweId];

      const rule: SARIFRule = {
        id: finding.modelId,
        name: finding.modelName,
        shortDescription: {
          text: finding.modelName,
        },
        fullDescription: {
          text: cweInfo?.description ?? finding.description,
        },
        helpUri: `https://cwe.mitre.org/data/definitions/${finding.cweId.replace('CWE-', '')}.html`,
        properties: {
          tags: [finding.category, finding.cweId],
          security: {
            severity: this.mapSeverityToSecurityLevel(finding.severity),
            cwe: finding.cweId,
          },
        },
        defaultConfiguration: {
          level: this.mapSeverityToLevel(finding.severity),
        },
      };

      ruleMap.set(finding.modelId, rule);
    }

    return [...ruleMap.values()];
  }

  /**
   * Generate SARIF results from findings
   */
  private generateResults(findings: VulnerabilityFinding[]): SARIFResult[] {
    return findings.map((finding) => this.generateResult(finding));
  }

  /**
   * Generate single SARIF result
   */
  private generateResult(finding: VulnerabilityFinding): SARIFResult {
    const result: SARIFResult = {
      ruleId: finding.modelId,
      level: this.mapSeverityToLevel(finding.severity),
      message: {
        text: finding.description,
      },
      locations: [this.generateLocation(finding)],
      fingerprints: {
        primaryLocationLineHash: `${finding.location.file}:${finding.location.startLine}`,
      },
      properties: {
        confidence: finding.confidence,
        detectionMethod: finding.detectionMethod,
      },
    };

    // Add code flow for taint findings
    if (finding.taintFlow) {
      result.codeFlows = [this.generateCodeFlow(finding)];
    }

    return result;
  }

  /**
   * Generate SARIF location
   */
  private generateLocation(finding: VulnerabilityFinding): SARIFLocation {
    return {
      physicalLocation: {
        artifactLocation: {
          uri: finding.location.file,
          uriBaseId: '%SRCROOT%',
        },
        region: {
          startLine: finding.location.startLine,
          endLine: finding.location.endLine,
          startColumn: finding.location.startColumn,
          endColumn: finding.location.endColumn,
        },
      },
    };
  }

  /**
   * Generate code flow for taint analysis
   */
  private generateCodeFlow(finding: VulnerabilityFinding): SARIFCodeFlow {
    if (!finding.taintFlow) {
      return { threadFlows: [] };
    }

    const locations: SARIFThreadFlowLocation[] = [];

    // Add source
    locations.push({
      location: {
        physicalLocation: {
          artifactLocation: {
            uri: finding.taintFlow.source.location?.file ?? finding.location.file,
          },
          region: {
            startLine: finding.taintFlow.source.location?.line ?? finding.location.startLine,
            startColumn: finding.taintFlow.source.location?.column ?? 1,
          },
        },
        message: {
          text: `Source: ${finding.taintFlow.source.codeSnippet ?? 'user input'}`,
        },
      },
      kinds: ['source'],
      nestingLevel: 0,
    });

    // Add intermediate steps
    for (let i = 0; i < finding.taintFlow.steps.length; i++) {
      const step = finding.taintFlow.steps[i];
      if (step.kind === 'source' || step.kind === 'sink') continue;

      locations.push({
        location: {
          physicalLocation: {
            artifactLocation: {
              uri: step.location?.file ?? finding.location.file,
            },
            region: {
              startLine: step.location?.line ?? finding.location.startLine,
              startColumn: step.location?.column ?? 1,
            },
          },
          message: {
            text: `Step ${i + 1}: ${step.codeSnippet ?? 'data flow'}`,
          },
        },
        kinds: ['pass-through'],
        nestingLevel: 1,
      });
    }

    // Add sink
    locations.push({
      location: {
        physicalLocation: {
          artifactLocation: {
            uri: finding.taintFlow.sink.location?.file ?? finding.location.file,
          },
          region: {
            startLine: finding.taintFlow.sink.location?.line ?? finding.location.startLine,
            startColumn: finding.taintFlow.sink.location?.column ?? 1,
          },
        },
        message: {
          text: `Sink: ${finding.taintFlow.sink.codeSnippet ?? 'dangerous operation'}`,
        },
      },
      kinds: ['sink'],
      nestingLevel: 0,
    });

    return {
      threadFlows: [
        {
          locations,
        },
      ],
      message: {
        text: `Data flows from source to sink in ${finding.taintFlow.pathLength} steps`,
      },
    };
  }

  /**
   * Map severity to SARIF level
   */
  private mapSeverityToLevel(
    severity: 'critical' | 'high' | 'medium' | 'low' | 'info',
  ): 'error' | 'warning' | 'note' | 'none' {
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
   * Map severity to security level
   */
  private mapSeverityToSecurityLevel(
    severity: 'critical' | 'high' | 'medium' | 'low' | 'info',
  ): string {
    return severity.toUpperCase();
  }

  /**
   * Convert path to file URI
   */
  private toFileUri(path: string): string {
    if (path.startsWith('file://')) return path;
    return `file://${path}`;
  }

  /**
   * Export SARIF report to JSON string
   */
  export(scanResult: ScanResult): string {
    const report = this.generate(scanResult);
    return JSON.stringify(report, null, 2);
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
  const generator = new SARIFGenerator();
  return generator.generate(scanResult);
}

/**
 * Export SARIF report to JSON string
 */
export function exportSARIF(scanResult: ScanResult): string {
  const generator = new SARIFGenerator();
  return generator.export(scanResult);
}
