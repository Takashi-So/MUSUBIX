/**
 * @fileoverview VS Code Integration for Security Scanning
 * @module @nahisaho/musubix-security/integrations/vscode-integration
 * 
 * Provides API for VS Code extension integration with diagnostic
 * and code action capabilities.
 */

import type { ScanResult, Vulnerability, Severity, Fix } from '../types/index.js';

// ============================================================================
// Types
// ============================================================================

/**
 * VS Code diagnostic severity (mirrors vscode.DiagnosticSeverity)
 */
export enum DiagnosticSeverity {
  Error = 0,
  Warning = 1,
  Information = 2,
  Hint = 3,
}

/**
 * VS Code position
 */
export interface Position {
  line: number;
  character: number;
}

/**
 * VS Code range
 */
export interface Range {
  start: Position;
  end: Position;
}

/**
 * VS Code diagnostic
 */
export interface Diagnostic {
  /** Range where the diagnostic applies */
  range: Range;
  /** Human-readable message */
  message: string;
  /** Severity level */
  severity: DiagnosticSeverity;
  /** Diagnostic code */
  code?: string | number;
  /** Source of the diagnostic */
  source: string;
  /** Related information */
  relatedInformation?: DiagnosticRelatedInformation[];
  /** Tags for special handling */
  tags?: DiagnosticTag[];
}

/**
 * Diagnostic related information
 */
export interface DiagnosticRelatedInformation {
  location: {
    uri: string;
    range: Range;
  };
  message: string;
}

/**
 * Diagnostic tag
 */
export enum DiagnosticTag {
  Unnecessary = 1,
  Deprecated = 2,
}

/**
 * Code action
 */
export interface CodeAction {
  /** Title shown in UI */
  title: string;
  /** Kind of code action */
  kind: CodeActionKind;
  /** Diagnostics this action resolves */
  diagnostics?: Diagnostic[];
  /** Workspace edit to apply */
  edit?: WorkspaceEdit;
  /** Command to execute */
  command?: Command;
  /** Whether this is preferred action */
  isPreferred?: boolean;
}

/**
 * Code action kind
 */
export type CodeActionKind = 
  | 'quickfix'
  | 'quickfix.security'
  | 'refactor'
  | 'refactor.security'
  | 'source'
  | 'source.fixAll.security';

/**
 * Workspace edit
 */
export interface WorkspaceEdit {
  /** Map of URI to text edits */
  changes: Map<string, TextEdit[]>;
}

/**
 * Text edit
 */
export interface TextEdit {
  range: Range;
  newText: string;
}

/**
 * Command
 */
export interface Command {
  title: string;
  command: string;
  arguments?: unknown[];
}

/**
 * Status bar item
 */
export interface StatusBarItem {
  text: string;
  tooltip: string;
  color?: string;
  backgroundColor?: string;
  command?: string;
}

/**
 * Tree item for explorer view
 */
export interface TreeItem {
  label: string;
  description?: string;
  tooltip?: string;
  iconPath?: string;
  collapsibleState: 'none' | 'collapsed' | 'expanded';
  children?: TreeItem[];
  command?: Command;
  contextValue?: string;
}

/**
 * Hover content
 */
export interface HoverContent {
  contents: string[];
  range?: Range;
}

/**
 * Decoration
 */
export interface Decoration {
  range: Range;
  renderOptions: {
    after?: {
      contentText: string;
      color?: string;
      backgroundColor?: string;
    };
    before?: {
      contentText: string;
      color?: string;
      backgroundColor?: string;
    };
  };
}

/**
 * VS Code integration options
 */
export interface VSCodeIntegrationOptions {
  /** Source name for diagnostics */
  diagnosticSource?: string;
  /** Collection name for diagnostics */
  diagnosticCollection?: string;
  /** Enable inline decorations */
  enableDecorations?: boolean;
  /** Enable code lens */
  enableCodeLens?: boolean;
  /** Severity mapping override */
  severityMapping?: Partial<Record<Severity, DiagnosticSeverity>>;
}

// ============================================================================
// VS Code Integration Class
// ============================================================================

/**
 * VS Code integration adapter for security scanning
 * 
 * @example
 * ```typescript
 * const integration = createVSCodeIntegration();
 * 
 * // Convert scan result to diagnostics
 * const diagnostics = integration.toDiagnostics(scanResult);
 * 
 * // Generate code actions for fixes
 * const actions = integration.toCodeActions(vulnerability, fixes);
 * ```
 */
export class VSCodeIntegration {
  private options: Required<VSCodeIntegrationOptions>;
  private severityMap: Record<Severity, DiagnosticSeverity>;

  constructor(options: VSCodeIntegrationOptions = {}) {
    this.options = {
      diagnosticSource: options.diagnosticSource ?? 'MUSUBIX Security',
      diagnosticCollection: options.diagnosticCollection ?? 'musubix-security',
      enableDecorations: options.enableDecorations ?? true,
      enableCodeLens: options.enableCodeLens ?? true,
      severityMapping: options.severityMapping ?? {},
    };

    this.severityMap = {
      critical: options.severityMapping?.critical ?? DiagnosticSeverity.Error,
      high: options.severityMapping?.high ?? DiagnosticSeverity.Error,
      medium: options.severityMapping?.medium ?? DiagnosticSeverity.Warning,
      low: options.severityMapping?.low ?? DiagnosticSeverity.Information,
      info: options.severityMapping?.info ?? DiagnosticSeverity.Hint,
    };
  }

  /**
   * Convert vulnerability to VS Code diagnostic
   */
  toDiagnostic(vulnerability: Vulnerability): Diagnostic {
    const range = this.locationToRange(vulnerability.location);
    
    const diagnostic: Diagnostic = {
      range,
      message: this.formatDiagnosticMessage(vulnerability),
      severity: this.severityMap[vulnerability.severity],
      code: vulnerability.ruleId,
      source: this.options.diagnosticSource,
      relatedInformation: this.getRelatedInformation(vulnerability),
    };

    return diagnostic;
  }

  /**
   * Convert scan result to VS Code diagnostics grouped by file
   */
  toDiagnostics(scanResult: ScanResult): Map<string, Diagnostic[]> {
    const diagnosticsMap = new Map<string, Diagnostic[]>();

    for (const vuln of scanResult.vulnerabilities) {
      const uri = vuln.location.file;
      
      if (!diagnosticsMap.has(uri)) {
        diagnosticsMap.set(uri, []);
      }
      
      diagnosticsMap.get(uri)!.push(this.toDiagnostic(vuln));
    }

    return diagnosticsMap;
  }

  /**
   * Convert fix to VS Code code action
   */
  toCodeAction(vulnerability: Vulnerability, fix: Fix): CodeAction {
    const diagnostic = this.toDiagnostic(vulnerability);
    
    const action: CodeAction = {
      title: fix.description,
      kind: 'quickfix.security',
      diagnostics: [diagnostic],
      isPreferred: fix.confidence >= 0.8,
    };

    // Convert fix edits to workspace edit
    if (fix.edits.length > 0) {
      const changes = new Map<string, TextEdit[]>();
      
      for (const edit of fix.edits) {
        const uri = vulnerability.location.file;
        if (!changes.has(uri)) {
          changes.set(uri, []);
        }
        
        changes.get(uri)!.push({
          range: {
            start: { line: edit.location.startLine - 1, character: edit.location.startColumn ?? 0 },
            end: { line: edit.location.endLine - 1, character: edit.location.endColumn ?? 0 },
          },
          newText: edit.newCode ?? '',
        });
      }
      
      action.edit = { changes };
    }

    return action;
  }

  /**
   * Convert multiple fixes to code actions
   */
  toCodeActions(vulnerability: Vulnerability, fixes: Fix[]): CodeAction[] {
    return fixes.map(fix => this.toCodeAction(vulnerability, fix));
  }

  /**
   * Generate "Fix All" code action
   */
  toFixAllAction(scanResult: ScanResult, fixes: Map<string, Fix[]>): CodeAction {
    const allEdits = new Map<string, TextEdit[]>();
    let fixCount = 0;

    for (const vuln of scanResult.vulnerabilities) {
      const vulnFixes = fixes.get(vuln.id);
      if (vulnFixes && vulnFixes.length > 0) {
        const bestFix = vulnFixes[0];
        
        for (const edit of bestFix.edits) {
          const uri = vuln.location.file;
          if (!allEdits.has(uri)) {
            allEdits.set(uri, []);
          }
          
          allEdits.get(uri)!.push({
            range: {
              start: { line: edit.location.startLine - 1, character: edit.location.startColumn ?? 0 },
              end: { line: edit.location.endLine - 1, character: edit.location.endColumn ?? 0 },
            },
            newText: edit.newCode ?? '',
          });
          fixCount++;
        }
      }
    }

    return {
      title: `Fix all ${fixCount} security issues`,
      kind: 'source.fixAll.security',
      edit: { changes: allEdits },
    };
  }

  /**
   * Generate status bar item
   */
  toStatusBarItem(scanResult: ScanResult): StatusBarItem {
    const { critical, high, medium, low } = scanResult.summary;
    const total = critical + high + medium + low;

    let text: string;
    let color: string | undefined;
    let backgroundColor: string | undefined;

    if (critical > 0) {
      text = `$(shield) ${total} Security Issues (${critical} Critical)`;
      color = '#ffffff';
      backgroundColor = '#cc0000';
    } else if (high > 0) {
      text = `$(shield) ${total} Security Issues (${high} High)`;
      color = '#ffffff';
      backgroundColor = '#ff8c00';
    } else if (total > 0) {
      text = `$(shield) ${total} Security Issues`;
      color = '#ffcc00';
    } else {
      text = '$(shield) No Security Issues';
      color = '#00cc00';
    }

    return {
      text,
      tooltip: this.formatStatusTooltip(scanResult),
      color,
      backgroundColor,
      command: 'musubix-security.showReport',
    };
  }

  /**
   * Generate tree items for explorer view
   */
  toTreeItems(scanResult: ScanResult): TreeItem[] {
    const items: TreeItem[] = [];

    // Group by severity
    const bySeverity = new Map<Severity, Vulnerability[]>();
    for (const vuln of scanResult.vulnerabilities) {
      if (!bySeverity.has(vuln.severity)) {
        bySeverity.set(vuln.severity, []);
      }
      bySeverity.get(vuln.severity)!.push(vuln);
    }

    // Create tree structure
    for (const severity of ['critical', 'high', 'medium', 'low', 'info'] as Severity[]) {
      const vulns = bySeverity.get(severity) ?? [];
      if (vulns.length === 0) continue;

      const severityItem: TreeItem = {
        label: `${severity.toUpperCase()} (${vulns.length})`,
        iconPath: this.getSeverityIcon(severity),
        collapsibleState: severity === 'critical' || severity === 'high' ? 'expanded' : 'collapsed',
        children: vulns.map(vuln => this.vulnerabilityToTreeItem(vuln)),
      };

      items.push(severityItem);
    }

    return items;
  }

  /**
   * Generate hover content for a vulnerability
   */
  toHoverContent(vulnerability: Vulnerability): HoverContent {
    const contents: string[] = [];

    // Header
    contents.push(`### 🔒 ${vulnerability.ruleId}`);
    contents.push('');

    // Severity badge
    const badge = this.getSeverityBadge(vulnerability.severity);
    contents.push(`**Severity:** ${badge}`);
    contents.push('');

    // Message
    contents.push(`**Issue:** ${vulnerability.description}`);
    contents.push('');

    // OWASP/CWE
    if (vulnerability.owasp || vulnerability.cwes) {
      contents.push('**References:**');
      if (vulnerability.owasp) {
        contents.push(`- OWASP: ${vulnerability.owasp.join(', ')}`);
      }
      if (vulnerability.cwes && vulnerability.cwes.length > 0) {
        contents.push(`- CWE: ${vulnerability.cwes.join(', ')}`);
      }
      contents.push('');
    }

    // Remediation (recommendation in the type)
    if (vulnerability.recommendation) {
      contents.push('**Remediation:**');
      contents.push(vulnerability.recommendation);
    }

    return {
      contents,
      range: this.locationToRange(vulnerability.location),
    };
  }

  /**
   * Generate inline decorations for vulnerabilities
   */
  toDecorations(vulnerabilities: Vulnerability[]): Decoration[] {
    if (!this.options.enableDecorations) return [];

    return vulnerabilities.map(vuln => ({
      range: this.locationToRange(vuln.location),
      renderOptions: {
        after: {
          contentText: ` ⚠️ ${vuln.severity.toUpperCase()}: ${vuln.ruleId}`,
          color: this.getSeverityColor(vuln.severity),
        },
      },
    }));
  }

  /**
   * Generate webview HTML content
   */
  toWebviewHTML(scanResult: ScanResult): string {
    const { critical, high, medium, low, info } = scanResult.summary;
    
    return `
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>MUSUBIX Security Report</title>
  <style>
    body { font-family: var(--vscode-font-family); padding: 20px; }
    .summary { display: flex; gap: 20px; margin-bottom: 20px; }
    .stat { padding: 10px 20px; border-radius: 4px; text-align: center; }
    .critical { background: #cc0000; color: white; }
    .high { background: #ff8c00; color: white; }
    .medium { background: #ffcc00; color: black; }
    .low { background: #0066cc; color: white; }
    .info { background: #666666; color: white; }
    table { width: 100%; border-collapse: collapse; }
    th, td { padding: 8px; text-align: left; border-bottom: 1px solid var(--vscode-panel-border); }
    .severity-badge { padding: 2px 8px; border-radius: 4px; font-size: 12px; }
  </style>
</head>
<body>
  <h1>🔒 Security Scan Results</h1>
  
  <div class="summary">
    <div class="stat critical">Critical: ${critical}</div>
    <div class="stat high">High: ${high}</div>
    <div class="stat medium">Medium: ${medium}</div>
    <div class="stat low">Low: ${low}</div>
    <div class="stat info">Info: ${info}</div>
  </div>
  
  <table>
    <thead>
      <tr>
        <th>Severity</th>
        <th>Rule</th>
        <th>File</th>
        <th>Line</th>
        <th>Message</th>
      </tr>
    </thead>
    <tbody>
      ${scanResult.vulnerabilities.map(v => `
        <tr>
          <td><span class="severity-badge ${v.severity}">${v.severity.toUpperCase()}</span></td>
          <td>${v.ruleId}</td>
          <td>${v.location.file}</td>
          <td>${v.location.startLine}</td>
          <td>${v.description}</td>
        </tr>
      `).join('')}
    </tbody>
  </table>
</body>
</html>
`;
  }

  // ============================================================================
  // Private Methods
  // ============================================================================

  private locationToRange(location: Vulnerability['location']): Range {
    return {
      start: {
        line: location.startLine - 1,
        character: location.startColumn ?? 0,
      },
      end: {
        line: (location.endLine ?? location.startLine) - 1,
        character: location.endColumn ?? 100,
      },
    };
  }

  private formatDiagnosticMessage(vuln: Vulnerability): string {
    let message = vuln.description;
    
    if (vuln.owasp) {
      message += ` [OWASP: ${vuln.owasp.join(', ')}]`;
    }
    if (vuln.cwes && vuln.cwes.length > 0) {
      message += ` [CWE: ${vuln.cwes.join(', ')}]`;
    }
    
    return message;
  }

  private getRelatedInformation(vuln: Vulnerability): DiagnosticRelatedInformation[] {
    const info: DiagnosticRelatedInformation[] = [];

    if (vuln.recommendation) {
      info.push({
        location: {
          uri: vuln.location.file,
          range: this.locationToRange(vuln.location),
        },
        message: `Remediation: ${vuln.recommendation}`,
      });
    }

    return info;
  }

  private formatStatusTooltip(scanResult: ScanResult): string {
    const { critical, high, medium, low, info } = scanResult.summary;
    const lines = [
      'MUSUBIX Security Scan',
      '─────────────────────',
      `Critical: ${critical}`,
      `High: ${high}`,
      `Medium: ${medium}`,
      `Low: ${low}`,
      `Info: ${info}`,
      '',
      'Click to view full report',
    ];
    return lines.join('\n');
  }

  private getSeverityIcon(severity: Severity): string {
    const icons: Record<Severity, string> = {
      critical: '$(error)',
      high: '$(warning)',
      medium: '$(info)',
      low: '$(lightbulb)',
      info: '$(note)',
    };
    return icons[severity];
  }

  private getSeverityColor(severity: Severity): string {
    const colors: Record<Severity, string> = {
      critical: '#cc0000',
      high: '#ff8c00',
      medium: '#ffcc00',
      low: '#0066cc',
      info: '#666666',
    };
    return colors[severity];
  }

  private getSeverityBadge(severity: Severity): string {
    const emojis: Record<Severity, string> = {
      critical: '🔴 CRITICAL',
      high: '🟠 HIGH',
      medium: '🟡 MEDIUM',
      low: '🔵 LOW',
      info: '⚪ INFO',
    };
    return emojis[severity];
  }

  private vulnerabilityToTreeItem(vuln: Vulnerability): TreeItem {
    return {
      label: vuln.ruleId,
      description: `${vuln.location.file}:${vuln.location.startLine}`,
      tooltip: vuln.description,
      iconPath: this.getSeverityIcon(vuln.severity),
      collapsibleState: 'none',
      command: {
        title: 'Go to vulnerability',
        command: 'musubix-security.goToVulnerability',
        arguments: [vuln],
      },
      contextValue: 'vulnerability',
    };
  }
}

// ============================================================================
// Factory Functions
// ============================================================================

/**
 * Create VS Code integration instance
 */
export function createVSCodeIntegration(options?: VSCodeIntegrationOptions): VSCodeIntegration {
  return new VSCodeIntegration(options);
}
