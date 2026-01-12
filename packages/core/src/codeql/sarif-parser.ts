/**
 * SARIF Parser - Parse CodeQL SARIF 2.1.0 output
 *
 * Implements: TSK-CODEQL-001, REQ-CODEQL-001〜002, DES-CODEQL-001
 */

import { readFile } from 'node:fs/promises';
import type {
  SARIFLog,
  SARIFRun,
  SARIFResult,
  SARIFRule,
  CodeQLFinding,
  CodeQLScanResult,
  CodeFlowStep,
} from './types.js';
import { mapCWE, extractCWEIds } from './cwe-mapper.js';

/**
 * SARIF Parser configuration
 */
export interface SARIFParserConfig {
  /** Include raw SARIF result in findings */
  includeRaw?: boolean;
  
  /** Base path to resolve relative URIs */
  basePath?: string;
  
  /** Filter by severity */
  minSeverity?: 'critical' | 'high' | 'medium' | 'low' | 'info';
  
  /** Filter by rule IDs */
  ruleFilter?: string[];
  
  /** Include CWE mappings */
  includeCWE?: boolean;
  
  /** Include Japanese explanations */
  includeExplanations?: boolean;
}

/**
 * SARIF Parser class
 */
export class SARIFParser {
  private config: SARIFParserConfig;

  constructor(config: SARIFParserConfig = {}) {
    this.config = {
      includeRaw: false,
      includeCWE: true,
      includeExplanations: true,
      ...config,
    };
  }

  /**
   * Parse SARIF from file
   */
  async parseFile(filePath: string): Promise<CodeQLScanResult> {
    const content = await readFile(filePath, 'utf-8');
    return this.parse(content);
  }

  /**
   * Parse SARIF from string
   */
  parse(content: string): CodeQLScanResult {
    const sarif = this.parseSARIFLog(content);
    return this.convertToCodeQLResult(sarif);
  }

  /**
   * Parse and validate SARIF log
   */
  private parseSARIFLog(content: string): SARIFLog {
    let sarif: SARIFLog;

    try {
      sarif = JSON.parse(content);
    } catch (error) {
      throw new Error(
        `Failed to parse SARIF JSON: ${error instanceof Error ? error.message : String(error)}`
      );
    }

    // Validate version
    if (sarif.version !== '2.1.0') {
      console.warn(
        `SARIF version ${sarif.version} may not be fully supported. Expected 2.1.0`
      );
    }

    // Validate structure
    if (!Array.isArray(sarif.runs)) {
      throw new Error('Invalid SARIF: missing or invalid "runs" array');
    }

    return sarif;
  }

  /**
   * Convert SARIF log to CodeQL scan result
   */
  private convertToCodeQLResult(sarif: SARIFLog): CodeQLScanResult {
    const findings: CodeQLFinding[] = [];
    let toolName = 'unknown';
    let toolVersion: string | undefined;

    for (const run of sarif.runs) {
      // Extract tool info
      if (run.tool?.driver) {
        toolName = run.tool.driver.name;
        toolVersion = run.tool.driver.version ?? run.tool.driver.semanticVersion;
      }

      // Build rule map
      const ruleMap = this.buildRuleMap(run);

      // Parse results
      if (run.results) {
        for (const result of run.results) {
          const finding = this.convertResult(result, ruleMap);
          if (finding && this.passesFilters(finding)) {
            findings.push(finding);
          }
        }
      }
    }

    // Calculate statistics
    const stats = this.calculateStats(findings);

    return {
      timestamp: new Date(),
      tool: {
        name: toolName,
        version: toolVersion,
      },
      findings,
      stats,
    };
  }

  /**
   * Build rule ID to rule definition map
   */
  private buildRuleMap(run: SARIFRun): Map<string, SARIFRule> {
    const ruleMap = new Map<string, SARIFRule>();

    if (run.tool?.driver?.rules) {
      for (const rule of run.tool.driver.rules) {
        ruleMap.set(rule.id, rule);
      }
    }

    if (run.tool?.extensions) {
      for (const extension of run.tool.extensions) {
        if (extension.rules) {
          for (const rule of extension.rules) {
            ruleMap.set(rule.id, rule);
          }
        }
      }
    }

    return ruleMap;
  }

  /**
   * Convert SARIF result to CodeQL finding
   */
  private convertResult(
    result: SARIFResult,
    ruleMap: Map<string, SARIFRule>
  ): CodeQLFinding | null {
    // Get rule ID
    const ruleId =
      result.ruleId ?? result.rule?.id ?? `rule-${result.ruleIndex ?? 'unknown'}`;

    // Get rule definition
    const rule = ruleMap.get(ruleId);

    // Get location
    const location = result.locations?.[0]?.physicalLocation;
    const file = this.resolveUri(location?.artifactLocation?.uri ?? '');
    const region = location?.region;

    // Get severity
    const severity = this.mapSeverity(result.level, rule);

    // Get message
    const message = result.message.text ?? result.message.markdown ?? '';

    // Extract CWE IDs
    let cweIds: string[] | undefined;
    let explanation: string | undefined;

    if (this.config.includeCWE) {
      cweIds = this.extractCWEFromResult(result, rule);
      
      if (this.config.includeExplanations && cweIds && cweIds.length > 0) {
        const cweInfo = mapCWE(cweIds[0]);
        explanation = cweInfo?.explanation;
      }
    }

    // Parse code flow
    const codeFlow = this.parseCodeFlow(result);

    // Build finding
    const finding: CodeQLFinding = {
      id: `${ruleId}-${file}-${region?.startLine ?? 0}`,
      ruleId,
      ruleName: rule?.name ?? rule?.shortDescription?.text,
      severity,
      message,
      file,
      startLine: region?.startLine,
      endLine: region?.endLine,
      startColumn: region?.startColumn,
      endColumn: region?.endColumn,
      snippet: region?.snippet?.text,
      cweIds,
      explanation,
      codeFlow,
    };

    // Include raw if configured
    if (this.config.includeRaw) {
      finding.raw = result;
    }

    return finding;
  }

  /**
   * Map SARIF level to severity
   */
  private mapSeverity(
    level: SARIFResult['level'] | undefined,
    rule?: SARIFRule
  ): CodeQLFinding['severity'] {
    // Check rule default configuration
    const ruleLevel = rule?.defaultConfiguration?.level;

    const effectiveLevel = level ?? ruleLevel ?? 'warning';

    switch (effectiveLevel) {
      case 'error':
        return 'high';
      case 'warning':
        return 'medium';
      case 'note':
        return 'low';
      case 'none':
        return 'info';
      default:
        return 'medium';
    }
  }

  /**
   * Extract CWE IDs from result and rule
   */
  private extractCWEFromResult(result: SARIFResult, rule?: SARIFRule): string[] {
    const cweIds: string[] = [];

    // From result taxa
    if (result.taxa) {
      for (const taxa of result.taxa) {
        if (taxa.id?.startsWith('CWE-')) {
          cweIds.push(taxa.id);
        }
      }
    }

    // From rule relationships
    if (rule?.relationships) {
      for (const rel of rule.relationships) {
        if (rel.target?.id?.startsWith('CWE-')) {
          cweIds.push(rel.target.id);
        }
      }
    }

    // From rule properties
    if (rule?.properties) {
      const props = rule.properties as Record<string, unknown>;
      if (Array.isArray(props.cwe)) {
        cweIds.push(...(props.cwe as string[]).filter((c) => typeof c === 'string'));
      }
      if (typeof props.cwe === 'string') {
        cweIds.push(props.cwe);
      }
    }

    // Extract from message text
    const messageText = result.message.text ?? '';
    cweIds.push(...extractCWEIds(messageText));

    return [...new Set(cweIds)];
  }

  /**
   * Parse code flow from result
   */
  private parseCodeFlow(result: SARIFResult): CodeFlowStep[] | undefined {
    if (!result.codeFlows || result.codeFlows.length === 0) {
      return undefined;
    }

    const steps: CodeFlowStep[] = [];

    for (const codeFlow of result.codeFlows) {
      for (const threadFlow of codeFlow.threadFlows) {
        for (const loc of threadFlow.locations) {
          const physLoc = loc.location?.physicalLocation;
          steps.push({
            file: this.resolveUri(physLoc?.artifactLocation?.uri ?? ''),
            line: physLoc?.region?.startLine,
            column: physLoc?.region?.startColumn,
            message: loc.location?.message?.text,
            kind: loc.kinds?.[0],
          });
        }
      }
    }

    return steps.length > 0 ? steps : undefined;
  }

  /**
   * Resolve URI with base path
   */
  private resolveUri(uri: string): string {
    if (!uri) return '';

    // Remove file:// prefix
    let resolved = uri.replace(/^file:\/\//, '');

    // Apply base path if relative
    if (this.config.basePath && !resolved.startsWith('/')) {
      resolved = `${this.config.basePath}/${resolved}`;
    }

    return resolved;
  }

  /**
   * Check if finding passes filters
   */
  private passesFilters(finding: CodeQLFinding): boolean {
    // Severity filter
    if (this.config.minSeverity) {
      const severityOrder = ['info', 'low', 'medium', 'high', 'critical'];
      const minIndex = severityOrder.indexOf(this.config.minSeverity);
      const findingIndex = severityOrder.indexOf(finding.severity);
      if (findingIndex < minIndex) {
        return false;
      }
    }

    // Rule filter
    if (this.config.ruleFilter && this.config.ruleFilter.length > 0) {
      if (!this.config.ruleFilter.includes(finding.ruleId)) {
        return false;
      }
    }

    return true;
  }

  /**
   * Calculate statistics from findings
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
}

/**
 * Create a SARIF parser instance
 */
export function createSARIFParser(config?: SARIFParserConfig): SARIFParser {
  return new SARIFParser(config);
}

/**
 * Parse SARIF file (convenience function)
 */
export async function parseSARIFFile(
  filePath: string,
  config?: SARIFParserConfig
): Promise<CodeQLScanResult> {
  const parser = new SARIFParser(config);
  return parser.parseFile(filePath);
}

/**
 * Parse SARIF string (convenience function)
 */
export function parseSARIF(
  content: string,
  config?: SARIFParserConfig
): CodeQLScanResult {
  const parser = new SARIFParser(config);
  return parser.parse(content);
}
