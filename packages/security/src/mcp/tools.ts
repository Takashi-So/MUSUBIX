/**
 * @fileoverview MCP Tools for security scanning
 * @module @nahisaho/musubix-security/mcp/tools
 * @trace REQ-SEC-MCP-001
 */

import * as path from 'node:path';

import {
  SecurityService,
  createSecurityService,
  type CompleteScanResult,
} from '../services/index.js';

/**
 * Tool parameter schema definition
 */
export interface ToolSchema {
  name: string;
  description: string;
  inputSchema: {
    type: 'object';
    properties: Record<string, {
      type: string;
      description: string;
      enum?: string[];
      default?: unknown;
    }>;
    required?: string[];
  };
}

/**
 * Tool result
 */
export interface ToolResult {
  content: Array<{
    type: 'text';
    text: string;
  }>;
  isError?: boolean;
}

/**
 * Security scan tool definitions
 */
export const SECURITY_TOOLS: ToolSchema[] = [
  {
    name: 'security_scan',
    description: 'Run a comprehensive security scan on the target path. Detects vulnerabilities, hardcoded secrets, tainted data flows, and vulnerable dependencies.',
    inputSchema: {
      type: 'object',
      properties: {
        target: {
          type: 'string',
          description: 'Target path to scan (file or directory)',
        },
        vulnerabilities: {
          type: 'boolean',
          description: 'Enable vulnerability scanning',
          default: true,
        },
        taint: {
          type: 'boolean',
          description: 'Enable taint analysis',
          default: true,
        },
        secrets: {
          type: 'boolean',
          description: 'Enable secret detection',
          default: true,
        },
        dependencies: {
          type: 'boolean',
          description: 'Enable dependency audit',
          default: true,
        },
        generateFixes: {
          type: 'boolean',
          description: 'Generate fix suggestions',
          default: true,
        },
      },
      required: ['target'],
    },
  },
  {
    name: 'security_quick_scan',
    description: 'Quick vulnerability scan without taint analysis, secret detection, or dependency audit.',
    inputSchema: {
      type: 'object',
      properties: {
        target: {
          type: 'string',
          description: 'Target path to scan',
        },
      },
      required: ['target'],
    },
  },
  {
    name: 'security_taint_analysis',
    description: 'Run taint analysis to trace data flow from untrusted sources to sensitive sinks.',
    inputSchema: {
      type: 'object',
      properties: {
        target: {
          type: 'string',
          description: 'Target path to analyze',
        },
      },
      required: ['target'],
    },
  },
  {
    name: 'security_detect_secrets',
    description: 'Detect hardcoded secrets like API keys, passwords, and tokens.',
    inputSchema: {
      type: 'object',
      properties: {
        target: {
          type: 'string',
          description: 'Target path to scan',
        },
      },
      required: ['target'],
    },
  },
  {
    name: 'security_audit_deps',
    description: 'Audit project dependencies for known vulnerabilities.',
    inputSchema: {
      type: 'object',
      properties: {
        target: {
          type: 'string',
          description: 'Project directory containing package.json',
        },
        generateSBOM: {
          type: 'boolean',
          description: 'Generate Software Bill of Materials',
          default: false,
        },
      },
      required: ['target'],
    },
  },
  {
    name: 'security_generate_fix',
    description: 'Generate a fix for a specific vulnerability.',
    inputSchema: {
      type: 'object',
      properties: {
        vulnerabilityId: {
          type: 'string',
          description: 'ID of the vulnerability to fix',
        },
        scanResultJson: {
          type: 'string',
          description: 'JSON string of previous scan result',
        },
      },
      required: ['vulnerabilityId', 'scanResultJson'],
    },
  },
  {
    name: 'security_generate_report',
    description: 'Generate a security report from scan results.',
    inputSchema: {
      type: 'object',
      properties: {
        scanResultJson: {
          type: 'string',
          description: 'JSON string of scan result',
        },
        format: {
          type: 'string',
          description: 'Report format',
          enum: ['json', 'sarif', 'markdown', 'html'],
          default: 'markdown',
        },
      },
      required: ['scanResultJson'],
    },
  },
];

/**
 * Security tool handlers
 */
export class SecurityToolHandler {
  private service: SecurityService;

  constructor() {
    this.service = createSecurityService();
  }

  /**
   * Handle tool call
   */
  async handleTool(name: string, args: Record<string, unknown>): Promise<ToolResult> {
    try {
      switch (name) {
        case 'security_scan':
          return this.handleScan(args);
        case 'security_quick_scan':
          return this.handleQuickScan(args);
        case 'security_taint_analysis':
          return this.handleTaintAnalysis(args);
        case 'security_detect_secrets':
          return this.handleDetectSecrets(args);
        case 'security_audit_deps':
          return this.handleAuditDeps(args);
        case 'security_generate_fix':
          return this.handleGenerateFix(args);
        case 'security_generate_report':
          return this.handleGenerateReport(args);
        default:
          return {
            content: [{ type: 'text', text: `Unknown tool: ${name}` }],
            isError: true,
          };
      }
    } catch (error: any) {
      return {
        content: [{ type: 'text', text: `Error: ${error.message}` }],
        isError: true,
      };
    }
  }

  /**
   * Handle full security scan
   */
  private async handleScan(args: Record<string, unknown>): Promise<ToolResult> {
    const target = String(args.target);
    const result = await this.service.scan({
      target: path.resolve(target),
      vulnerabilities: args.vulnerabilities !== false,
      taint: args.taint !== false,
      secrets: args.secrets !== false,
      dependencies: args.dependencies !== false,
      generateFixes: args.generateFixes !== false,
    });

    return {
      content: [{
        type: 'text',
        text: this.formatScanResult(result),
      }],
    };
  }

  /**
   * Handle quick scan
   */
  private async handleQuickScan(args: Record<string, unknown>): Promise<ToolResult> {
    const target = String(args.target);
    const result = await this.service.quickScan(path.resolve(target));

    return {
      content: [{
        type: 'text',
        text: `# Quick Scan Results

**Files Scanned:** ${result.scannedFiles}
**Vulnerabilities Found:** ${result.vulnerabilities.length}

${result.vulnerabilities.map(v => `- **${v.severity.toUpperCase()}**: ${v.type}
  - File: ${v.location.file}:${v.location.startLine}
  - ${v.description}`).join('\n\n')}

${result.vulnerabilities.length === 0 ? '✅ No vulnerabilities found.' : ''}`,
      }],
    };
  }

  /**
   * Handle taint analysis
   */
  private async handleTaintAnalysis(args: Record<string, unknown>): Promise<ToolResult> {
    const target = String(args.target);
    const result = await this.service.analyzeTaint(path.resolve(target));

    return {
      content: [{
        type: 'text',
        text: `# Taint Analysis Results

**Sources Found:** ${result.sources.length}
**Sinks Found:** ${result.sinks.length}
**Tainted Paths:** ${result.unsafePaths.length}

## Tainted Data Flows
${result.unsafePaths.map((p, idx) => `
### Path ${idx + 1}
- **Source:** ${p.source.variableName ?? p.source.expression} (${p.source.category})
  - ${p.source.location.file}:${p.source.location.startLine}
- **Sink:** ${p.sink.functionName} (${p.sink.category})
  - ${p.sink.location.file}:${p.sink.location.startLine}
- **Sanitized:** ${p.sanitized ? '✅ Yes' : '❌ No'}
`).join('\n')}

${result.unsafePaths.length === 0 ? '✅ No tainted paths found.' : ''}`,
      }],
    };
  }

  /**
   * Handle secret detection
   */
  private async handleDetectSecrets(args: Record<string, unknown>): Promise<ToolResult> {
    const target = String(args.target);
    const result = await this.service.detectSecrets(path.resolve(target));

    return {
      content: [{
        type: 'text',
        text: `# Secret Detection Results

**Files Scanned:** ${result.scannedFiles}
**Secrets Found:** ${result.summary.total}

${result.secrets.map(s => `- **${s.type}** in \`${s.location.file}:${s.location.startLine}\`
  - Value: \`${s.maskedValue}\`
  - Confidence: ${(s.confidence * 100).toFixed(0)}%`).join('\n\n')}

${result.summary.total === 0 ? '✅ No hardcoded secrets detected.' : '⚠️ Please rotate any exposed secrets immediately.'}`,
      }],
    };
  }

  /**
   * Handle dependency audit
   */
  private async handleAuditDeps(args: Record<string, unknown>): Promise<ToolResult> {
    const target = String(args.target);

    if (args.generateSBOM) {
      const { DependencyAuditor } = await import('../analysis/index.js');
      const auditor = new DependencyAuditor();
      const sbom = await auditor.generateSBOM(path.resolve(target));
      return {
        content: [{
          type: 'text',
          text: `# Software Bill of Materials (SBOM)

\`\`\`json
${JSON.stringify(sbom, null, 2)}
\`\`\``,
        }],
      };
    }

    const result = await this.service.auditDependencies(path.resolve(target));

    return {
      content: [{
        type: 'text',
        text: `# Dependency Audit Results

**Vulnerable Dependencies:** ${result.vulnerableDependencies.length}

${result.vulnerableDependencies.map(d => `- **${d.highestSeverity.toUpperCase()}**: ${d.name}@${d.installedVersion}
  - Title: ${d.vulnerabilities[0]?.title ?? 'N/A'}
  - Patched: ${d.vulnerabilities[0]?.patchedVersion ?? 'No patch available'}
  - ${d.vulnerabilities[0]?.url ?? ''}`).join('\n\n')}

${result.vulnerableDependencies.length === 0 ? '✅ No vulnerable dependencies found.' : ''}`,
      }],
    };
  }

  /**
   * Handle fix generation
   */
  private async handleGenerateFix(args: Record<string, unknown>): Promise<ToolResult> {
    const vulnerabilityId = String(args.vulnerabilityId);
    const scanResult = JSON.parse(String(args.scanResultJson));

    const fix = await this.service.generateFix(vulnerabilityId, scanResult.vulnerabilities);

    if (!fix) {
      return {
        content: [{
          type: 'text',
          text: `No fix found for vulnerability: ${vulnerabilityId}`,
        }],
        isError: true,
      };
    }

    return {
      content: [{
        type: 'text',
        text: `# Fix Suggestion

**Description:** ${fix.description}
**Strategy:** ${fix.strategy}
**Confidence:** ${(fix.confidence * 100).toFixed(0)}%

## Code Changes

${fix.edits.map(e => `### ${e.location.file}:${e.location.startLine}-${e.location.endLine}

**Before:**
\`\`\`
${e.originalCode}
\`\`\`

**After:**
\`\`\`
${e.newCode}
\`\`\``).join('\n\n')}

**Note:** Please review the fix carefully before applying.`,
      }],
    };
  }

  /**
   * Handle report generation
   */
  private async handleGenerateReport(args: Record<string, unknown>): Promise<ToolResult> {
    const scanResult = JSON.parse(String(args.scanResultJson)) as CompleteScanResult;
    const format = (args.format as string) || 'markdown';

    const report = await this.service.generateReport(
      scanResult,
      format as 'json' | 'sarif' | 'markdown' | 'html'
    );

    return {
      content: [{
        type: 'text',
        text: report,
      }],
    };
  }

  /**
   * Format scan result for display
   */
  private formatScanResult(result: CompleteScanResult): string {
    const s = result.summary;

    let output = `# Security Scan Results

## Summary
- **Target:** ${result.metadata.target}
- **Duration:** ${result.metadata.duration}ms
- **Files Scanned:** ${result.metadata.filesScanned}

### Vulnerabilities by Severity
| Severity | Count |
|----------|-------|
| Critical | ${s.bySeverity.critical} |
| High | ${s.bySeverity.high} |
| Medium | ${s.bySeverity.medium} |
| Low | ${s.bySeverity.low} |
| Info | ${s.bySeverity.info} |
| **Total** | **${s.totalVulnerabilities}** |

`;

    if (result.vulnerabilities && result.vulnerabilities.vulnerabilities.length > 0) {
      output += `## Vulnerabilities\n\n`;
      for (const v of result.vulnerabilities.vulnerabilities.slice(0, 10)) {
        output += `### ${v.type} (${v.severity.toUpperCase()})\n`;
        output += `- **Location:** ${v.location.file}:${v.location.startLine}\n`;
        output += `- **CWE:** ${v.cwes[0] ?? 'N/A'}\n`;
        output += `- **Description:** ${v.description}\n\n`;
      }
      if (result.vulnerabilities.vulnerabilities.length > 10) {
        output += `... and ${result.vulnerabilities.vulnerabilities.length - 10} more\n\n`;
      }
    }

    if (s.secretsFound > 0) {
      output += `## ⚠️ Secrets Detected: ${s.secretsFound}\n\n`;
    }

    if (s.taintedPaths > 0) {
      output += `## Tainted Data Flows: ${s.taintedPaths}\n\n`;
    }

    if (s.vulnerableDependencies > 0) {
      output += `## Vulnerable Dependencies: ${s.vulnerableDependencies}\n\n`;
    }

    if (result.fixes && result.fixes.length > 0) {
      output += `## Fixes Available: ${s.fixesGenerated}\n\n`;
      output += `Use \`security_generate_fix\` to get detailed fix suggestions.\n`;
    }

    return output;
  }
}

/**
 * Get all tool schemas
 */
export function getToolSchemas(): ToolSchema[] {
  return SECURITY_TOOLS;
}

/**
 * Create tool handler
 */
export function createToolHandler(): SecurityToolHandler {
  return new SecurityToolHandler();
}
