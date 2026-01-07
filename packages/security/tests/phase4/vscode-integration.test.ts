/**
 * @fileoverview VS Code Integration Tests
 * @module @nahisaho/musubix-security/tests/phase4/vscode-integration
 */

import { describe, it, expect } from 'vitest';
import {
  VSCodeIntegration,
  createVSCodeIntegration,
  DiagnosticSeverity,
} from '../../src/integrations/vscode-integration.js';
import type { ScanResult, Vulnerability, Fix, SourceLocation, VulnerabilityType, FixStrategy } from '../../src/types/index.js';

describe('VSCodeIntegration', () => {
  const createMockLocation = (file: string = 'src/test.ts', startLine: number = 10): SourceLocation => ({
    file,
    startLine,
    endLine: startLine,
    startColumn: 5,
    endColumn: 50,
  });

  const createMockVulnerability = (
    severity: 'critical' | 'high' | 'medium' | 'low' | 'info',
    file: string = 'src/test.ts',
    startLine: number = 10
  ): Vulnerability => ({
    id: `VULN-${Date.now()}`,
    type: 'xss' as VulnerabilityType,
    severity,
    cwes: ['CWE-79'],
    owasp: ['A01:2021'],
    location: createMockLocation(file, startLine),
    description: `Test ${severity} vulnerability`,
    recommendation: 'Fix by sanitizing input',
    confidence: 0.9,
    ruleId: `SEC-${severity.toUpperCase()}-001`,
    detectedAt: new Date(),
  });

  const createMockScanResult = (vulns: Vulnerability[] = []): ScanResult => ({
    vulnerabilities: vulns,
    scannedFiles: 10,
    skippedFiles: 0,
    duration: 100,
    timestamp: new Date(),
    options: {},
    summary: {
      total: vulns.length,
      critical: vulns.filter(v => v.severity === 'critical').length,
      high: vulns.filter(v => v.severity === 'high').length,
      medium: vulns.filter(v => v.severity === 'medium').length,
      low: vulns.filter(v => v.severity === 'low').length,
      info: vulns.filter(v => v.severity === 'info').length,
    },
  });

  const createMockFix = (): Fix => ({
    id: 'FIX-001',
    vulnerabilityId: 'VULN-001',
    strategy: 'sanitization' as FixStrategy,
    title: 'Sanitize input',
    description: 'Sanitize user input',
    confidence: 0.9,
    breakingChange: false,
    rationale: 'Prevent XSS attacks',
    edits: [
      {
        location: createMockLocation('src/test.ts', 10),
        originalCode: 'userInput',
        newCode: 'sanitize(userInput)',
        description: 'Sanitize the input',
      },
    ],
    imports: [],
    generatedAt: new Date(),
  });

  describe('createVSCodeIntegration', () => {
    it('should create integration with default options', () => {
      const integration = createVSCodeIntegration();
      expect(integration).toBeInstanceOf(VSCodeIntegration);
    });

    it('should create integration with custom options', () => {
      const integration = createVSCodeIntegration({
        diagnosticSource: 'Custom Security',
        enableDecorations: false,
      });
      expect(integration).toBeInstanceOf(VSCodeIntegration);
    });
  });

  describe('toDiagnostic', () => {
    it('should convert vulnerability to diagnostic', () => {
      const integration = createVSCodeIntegration();
      const vuln = createMockVulnerability('high');

      const diagnostic = integration.toDiagnostic(vuln);

      expect(diagnostic.range.start.line).toBe(9); // 0-indexed
      expect(diagnostic.range.start.character).toBe(5);
      expect(diagnostic.severity).toBe(DiagnosticSeverity.Error);
      expect(diagnostic.source).toBe('MUSUBIX Security');
      expect(diagnostic.code).toBe(vuln.ruleId);
    });

    it('should map severity to diagnostic severity correctly', () => {
      const integration = createVSCodeIntegration();

      expect(integration.toDiagnostic(createMockVulnerability('critical')).severity)
        .toBe(DiagnosticSeverity.Error);
      expect(integration.toDiagnostic(createMockVulnerability('high')).severity)
        .toBe(DiagnosticSeverity.Error);
      expect(integration.toDiagnostic(createMockVulnerability('medium')).severity)
        .toBe(DiagnosticSeverity.Warning);
      expect(integration.toDiagnostic(createMockVulnerability('low')).severity)
        .toBe(DiagnosticSeverity.Information);
      expect(integration.toDiagnostic(createMockVulnerability('info')).severity)
        .toBe(DiagnosticSeverity.Hint);
    });

    it('should include OWASP and CWE in message', () => {
      const integration = createVSCodeIntegration();
      const vuln = createMockVulnerability('high');

      const diagnostic = integration.toDiagnostic(vuln);

      expect(diagnostic.message).toContain('OWASP');
      expect(diagnostic.message).toContain('CWE');
    });

    it('should include related information for remediation', () => {
      const integration = createVSCodeIntegration();
      const vuln = createMockVulnerability('high');

      const diagnostic = integration.toDiagnostic(vuln);

      expect(diagnostic.relatedInformation?.length).toBeGreaterThan(0);
      expect(diagnostic.relatedInformation?.[0].message).toContain('Remediation');
    });
  });

  describe('toDiagnostics', () => {
    it('should convert scan result to diagnostics grouped by file', () => {
      const integration = createVSCodeIntegration();
      const scanResult = createMockScanResult([
        createMockVulnerability('high', 'src/a.ts'),
        createMockVulnerability('medium', 'src/a.ts'),
        createMockVulnerability('low', 'src/b.ts'),
      ]);

      const diagnostics = integration.toDiagnostics(scanResult);

      expect(diagnostics.size).toBe(2);
      expect(diagnostics.get('src/a.ts')?.length).toBe(2);
      expect(diagnostics.get('src/b.ts')?.length).toBe(1);
    });

    it('should return empty map for clean scan', () => {
      const integration = createVSCodeIntegration();
      const scanResult = createMockScanResult([]);

      const diagnostics = integration.toDiagnostics(scanResult);

      expect(diagnostics.size).toBe(0);
    });
  });

  describe('toCodeAction', () => {
    it('should convert fix to code action', () => {
      const integration = createVSCodeIntegration();
      const vuln = createMockVulnerability('high');
      const fix = createMockFix();

      const action = integration.toCodeAction(vuln, fix);

      expect(action.title).toBe(fix.description);
      expect(action.kind).toBe('quickfix.security');
      expect(action.isPreferred).toBe(true); // confidence >= 0.8
    });

    it('should include workspace edit', () => {
      const integration = createVSCodeIntegration();
      const vuln = createMockVulnerability('high');
      const fix = createMockFix();

      const action = integration.toCodeAction(vuln, fix);

      expect(action.edit).toBeDefined();
      expect(action.edit?.changes.size).toBe(1);
    });

    it('should not mark as preferred for low confidence', () => {
      const integration = createVSCodeIntegration();
      const vuln = createMockVulnerability('high');
      const fix = { ...createMockFix(), confidence: 0.5 };

      const action = integration.toCodeAction(vuln, fix);

      expect(action.isPreferred).toBe(false);
    });
  });

  describe('toCodeActions', () => {
    it('should convert multiple fixes to code actions', () => {
      const integration = createVSCodeIntegration();
      const vuln = createMockVulnerability('high');
      const fixes = [createMockFix(), { ...createMockFix(), description: 'Alternative fix' }];

      const actions = integration.toCodeActions(vuln, fixes);

      expect(actions.length).toBe(2);
    });
  });

  describe('toFixAllAction', () => {
    it('should generate fix all action', () => {
      const integration = createVSCodeIntegration();
      const vuln1 = createMockVulnerability('high', 'src/a.ts');
      const vuln2 = createMockVulnerability('medium', 'src/b.ts');
      const scanResult = createMockScanResult([vuln1, vuln2]);
      
      const fixes = new Map<string, Fix[]>();
      fixes.set(vuln1.id, [createMockFix()]);
      fixes.set(vuln2.id, [createMockFix()]);

      const action = integration.toFixAllAction(scanResult, fixes);

      expect(action.title).toContain('Fix all');
      expect(action.kind).toBe('source.fixAll.security');
    });
  });

  describe('toStatusBarItem', () => {
    it('should show success for clean scan', () => {
      const integration = createVSCodeIntegration();
      const scanResult = createMockScanResult([]);

      const statusBar = integration.toStatusBarItem(scanResult);

      expect(statusBar.text).toContain('No Security Issues');
      expect(statusBar.color).toBe('#00cc00');
    });

    it('should show critical status for critical vulnerabilities', () => {
      const integration = createVSCodeIntegration();
      const scanResult = createMockScanResult([
        createMockVulnerability('critical'),
      ]);

      const statusBar = integration.toStatusBarItem(scanResult);

      expect(statusBar.text).toContain('Critical');
      expect(statusBar.backgroundColor).toBe('#cc0000');
    });

    it('should show high status for high vulnerabilities', () => {
      const integration = createVSCodeIntegration();
      const scanResult = createMockScanResult([
        createMockVulnerability('high'),
      ]);

      const statusBar = integration.toStatusBarItem(scanResult);

      expect(statusBar.text).toContain('High');
      expect(statusBar.backgroundColor).toBe('#ff8c00');
    });

    it('should include tooltip', () => {
      const integration = createVSCodeIntegration();
      const scanResult = createMockScanResult([
        createMockVulnerability('medium'),
      ]);

      const statusBar = integration.toStatusBarItem(scanResult);

      expect(statusBar.tooltip).toContain('MUSUBIX Security Scan');
      expect(statusBar.tooltip).toContain('Medium: 1');
    });

    it('should include command', () => {
      const integration = createVSCodeIntegration();
      const scanResult = createMockScanResult([]);

      const statusBar = integration.toStatusBarItem(scanResult);

      expect(statusBar.command).toBe('musubix-security.showReport');
    });
  });

  describe('toTreeItems', () => {
    it('should generate tree items grouped by severity', () => {
      const integration = createVSCodeIntegration();
      const scanResult = createMockScanResult([
        createMockVulnerability('critical'),
        createMockVulnerability('high'),
        createMockVulnerability('high'),
        createMockVulnerability('low'),
      ]);

      const items = integration.toTreeItems(scanResult);

      expect(items.length).toBe(3); // critical, high, low
      expect(items.find(i => i.label.includes('CRITICAL'))?.children?.length).toBe(1);
      expect(items.find(i => i.label.includes('HIGH'))?.children?.length).toBe(2);
    });

    it('should expand critical and high by default', () => {
      const integration = createVSCodeIntegration();
      const scanResult = createMockScanResult([
        createMockVulnerability('critical'),
        createMockVulnerability('low'),
      ]);

      const items = integration.toTreeItems(scanResult);

      const criticalItem = items.find(i => i.label.includes('CRITICAL'));
      const lowItem = items.find(i => i.label.includes('LOW'));

      expect(criticalItem?.collapsibleState).toBe('expanded');
      expect(lowItem?.collapsibleState).toBe('collapsed');
    });

    it('should include command for vulnerability items', () => {
      const integration = createVSCodeIntegration();
      const scanResult = createMockScanResult([
        createMockVulnerability('high'),
      ]);

      const items = integration.toTreeItems(scanResult);
      const vulnItem = items[0].children?.[0];

      expect(vulnItem?.command?.command).toBe('musubix-security.goToVulnerability');
    });
  });

  describe('toHoverContent', () => {
    it('should generate hover content', () => {
      const integration = createVSCodeIntegration();
      const vuln = createMockVulnerability('high');

      const hover = integration.toHoverContent(vuln);

      expect(hover.contents.length).toBeGreaterThan(0);
      expect(hover.contents.some(c => c.includes(vuln.ruleId))).toBe(true);
      expect(hover.contents.some(c => c.includes('Severity'))).toBe(true);
    });

    it('should include OWASP and CWE references', () => {
      const integration = createVSCodeIntegration();
      const vuln = createMockVulnerability('high');

      const hover = integration.toHoverContent(vuln);

      expect(hover.contents.some(c => c.includes('OWASP'))).toBe(true);
      expect(hover.contents.some(c => c.includes('CWE'))).toBe(true);
    });

    it('should include remediation', () => {
      const integration = createVSCodeIntegration();
      const vuln = createMockVulnerability('high');

      const hover = integration.toHoverContent(vuln);

      expect(hover.contents.some(c => c.includes('Remediation'))).toBe(true);
    });

    it('should include range', () => {
      const integration = createVSCodeIntegration();
      const vuln = createMockVulnerability('high', 'src/test.ts', 15);

      const hover = integration.toHoverContent(vuln);

      expect(hover.range).toBeDefined();
      expect(hover.range?.start.line).toBe(14); // 0-indexed
    });
  });

  describe('toDecorations', () => {
    it('should generate decorations when enabled', () => {
      const integration = createVSCodeIntegration({ enableDecorations: true });
      const vulns = [createMockVulnerability('high')];

      const decorations = integration.toDecorations(vulns);

      expect(decorations.length).toBe(1);
      expect(decorations[0].renderOptions.after?.contentText).toContain('HIGH');
    });

    it('should not generate decorations when disabled', () => {
      const integration = createVSCodeIntegration({ enableDecorations: false });
      const vulns = [createMockVulnerability('high')];

      const decorations = integration.toDecorations(vulns);

      expect(decorations.length).toBe(0);
    });

    it('should use correct colors for severity', () => {
      const integration = createVSCodeIntegration({ enableDecorations: true });

      const criticalDeco = integration.toDecorations([createMockVulnerability('critical')])[0];
      const lowDeco = integration.toDecorations([createMockVulnerability('low')])[0];

      expect(criticalDeco.renderOptions.after?.color).toBe('#cc0000');
      expect(lowDeco.renderOptions.after?.color).toBe('#0066cc');
    });
  });

  describe('toWebviewHTML', () => {
    it('should generate valid HTML', () => {
      const integration = createVSCodeIntegration();
      const scanResult = createMockScanResult([
        createMockVulnerability('high'),
      ]);

      const html = integration.toWebviewHTML(scanResult);

      expect(html).toContain('<!DOCTYPE html>');
      expect(html).toContain('<html');
      expect(html).toContain('Security Scan Results');
    });

    it('should include summary statistics', () => {
      const integration = createVSCodeIntegration();
      const scanResult = createMockScanResult([
        createMockVulnerability('critical'),
        createMockVulnerability('high'),
      ]);

      const html = integration.toWebviewHTML(scanResult);

      expect(html).toContain('Critical: 1');
      expect(html).toContain('High: 1');
    });

    it('should include vulnerability table', () => {
      const integration = createVSCodeIntegration();
      const scanResult = createMockScanResult([
        createMockVulnerability('high', 'src/api.ts', 25),
      ]);

      const html = integration.toWebviewHTML(scanResult);

      expect(html).toContain('src/api.ts');
      expect(html).toContain('25');
    });
  });
});
