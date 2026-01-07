/**
 * @fileoverview Phase 3 - Security Dashboard Tests
 * @module @nahisaho/musubix-security/tests/phase3/security-dashboard.test
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  SecurityDashboard,
  createSecurityDashboard,
  type DashboardConfig,
  type DashboardReport,
} from '../../src/analyzers/dashboard/security-dashboard.js';
import type { Vulnerability, Severity } from '../../src/types/vulnerability.js';
import type { ScanResult } from '../../src/types/scanner.js';

describe('SecurityDashboard', () => {
  let dashboard: SecurityDashboard;
  const defaultConfig: DashboardConfig = {
    projectName: 'Test Project',
  };

  const createMockVulnerability = (
    overrides: Partial<Vulnerability> = {}
  ): Vulnerability => ({
    id: `vuln-${Math.random().toString(36).slice(2)}`,
    type: 'xss',
    severity: 'medium',
    cwes: ['CWE-79'],
    owasp: ['A03:2021'],
    location: {
      file: 'src/test.ts',
      startLine: 10,
      endLine: 10,
      startColumn: 0,
      endColumn: 50,
    },
    description: 'Test vulnerability',
    recommendation: 'Fix the issue',
    confidence: 0.9,
    ruleId: 'TEST-001',
    codeSnippet: 'vulnerable code',
    detectedAt: new Date(),
    ...overrides,
  });

  const createMockScanResult = (
    vulnerabilities: Vulnerability[] = []
  ): ScanResult => ({
    scannedAt: new Date(),
    filesScanned: 10,
    vulnerabilities,
    errors: [],
    summary: {
      critical: vulnerabilities.filter(v => v.severity === 'critical').length,
      high: vulnerabilities.filter(v => v.severity === 'high').length,
      medium: vulnerabilities.filter(v => v.severity === 'medium').length,
      low: vulnerabilities.filter(v => v.severity === 'low').length,
      info: vulnerabilities.filter(v => v.severity === 'info').length,
      total: vulnerabilities.length,
    },
  });

  beforeEach(() => {
    dashboard = createSecurityDashboard(defaultConfig);
  });

  describe('constructor and factory', () => {
    it('should create dashboard with default options', () => {
      const d = new SecurityDashboard(defaultConfig);
      expect(d).toBeInstanceOf(SecurityDashboard);
    });

    it('should create dashboard with factory function', () => {
      const d = createSecurityDashboard(defaultConfig);
      expect(d).toBeInstanceOf(SecurityDashboard);
    });

    it('should accept custom format option', () => {
      const d = createSecurityDashboard({
        ...defaultConfig,
        format: 'html',
      });
      expect(d).toBeInstanceOf(SecurityDashboard);
    });

    it('should accept trends option', () => {
      const d = createSecurityDashboard({
        ...defaultConfig,
        includeTrends: true,
      });
      expect(d).toBeInstanceOf(SecurityDashboard);
    });

    it('should accept recommendations option', () => {
      const d = createSecurityDashboard({
        ...defaultConfig,
        includeRecommendations: true,
      });
      expect(d).toBeInstanceOf(SecurityDashboard);
    });

    it('should accept branding option', () => {
      const d = createSecurityDashboard({
        ...defaultConfig,
        branding: {
          title: 'Custom Dashboard',
          logo: 'logo.png',
        },
      });
      expect(d).toBeInstanceOf(SecurityDashboard);
    });
  });

  describe('addScanResult', () => {
    it('should add scan result', () => {
      const scanResult = createMockScanResult([createMockVulnerability()]);
      
      dashboard.addScanResult(scanResult);
      const report = dashboard.generateReport();
      
      expect(report.metrics.totalVulnerabilities).toBe(1);
    });

    it('should accumulate vulnerabilities from multiple scans', () => {
      dashboard.addScanResult(createMockScanResult([createMockVulnerability()]));
      dashboard.addScanResult(createMockScanResult([createMockVulnerability()]));
      
      const report = dashboard.generateReport();
      
      expect(report.metrics.totalVulnerabilities).toBe(2);
    });
  });

  describe('addVulnerabilities', () => {
    it('should add vulnerabilities directly', () => {
      dashboard.addVulnerabilities([createMockVulnerability()]);
      
      const report = dashboard.generateReport();
      
      expect(report.metrics.totalVulnerabilities).toBe(1);
    });

    it('should accumulate vulnerabilities', () => {
      dashboard.addVulnerabilities([createMockVulnerability()]);
      dashboard.addVulnerabilities([createMockVulnerability(), createMockVulnerability()]);
      
      const report = dashboard.generateReport();
      
      expect(report.metrics.totalVulnerabilities).toBe(3);
    });
  });

  describe('clear', () => {
    it('should clear all data', () => {
      dashboard.addVulnerabilities([createMockVulnerability()]);
      dashboard.clear();
      
      const report = dashboard.generateReport();
      
      expect(report.metrics.totalVulnerabilities).toBe(0);
    });
  });

  describe('generateReport', () => {
    it('should generate report with basic info', () => {
      const report = dashboard.generateReport();
      
      expect(report.generatedAt).toBeInstanceOf(Date);
      expect(report.projectName).toBe('Test Project');
    });

    it('should include executive summary', () => {
      const report = dashboard.generateReport();
      
      expect(report.summary).toBeDefined();
      expect(report.summary.status).toBeDefined();
      expect(report.summary.statusMessage).toBeDefined();
      expect(Array.isArray(report.summary.highlights)).toBe(true);
      expect(Array.isArray(report.summary.keyFindings)).toBe(true);
      expect(Array.isArray(report.summary.immediateActions)).toBe(true);
    });

    it('should include metrics', () => {
      const report = dashboard.generateReport();
      
      expect(report.metrics).toBeDefined();
      expect(typeof report.metrics.totalVulnerabilities).toBe('number');
      expect(report.metrics.bySeverity).toBeDefined();
      expect(report.metrics.byType).toBeDefined();
      expect(report.metrics.byComponent).toBeDefined();
    });

    it('should include severity breakdown', () => {
      dashboard.addVulnerabilities([
        createMockVulnerability({ severity: 'critical' }),
        createMockVulnerability({ severity: 'high' }),
        createMockVulnerability({ severity: 'medium' }),
        createMockVulnerability({ severity: 'low' }),
        createMockVulnerability({ severity: 'info' }),
      ]);
      
      const report = dashboard.generateReport();
      
      expect(report.metrics.bySeverity.critical).toBe(1);
      expect(report.metrics.bySeverity.high).toBe(1);
      expect(report.metrics.bySeverity.medium).toBe(1);
      expect(report.metrics.bySeverity.low).toBe(1);
      expect(report.metrics.bySeverity.info).toBe(1);
    });

    it('should calculate security score', () => {
      const report = dashboard.generateReport();
      
      expect(typeof report.metrics.securityScore).toBe('number');
      expect(report.metrics.securityScore).toBeGreaterThanOrEqual(0);
      expect(report.metrics.securityScore).toBeLessThanOrEqual(100);
    });

    it('should have perfect score with no vulnerabilities', () => {
      const report = dashboard.generateReport();
      
      expect(report.metrics.securityScore).toBe(100);
    });

    it('should reduce score for vulnerabilities', () => {
      dashboard.addVulnerabilities([
        createMockVulnerability({ severity: 'critical' }),
      ]);
      
      const report = dashboard.generateReport();
      
      expect(report.metrics.securityScore).toBeLessThan(100);
    });

    it('should determine risk level', () => {
      const report = dashboard.generateReport();
      
      expect(['critical', 'high', 'medium', 'low', 'minimal']).toContain(
        report.metrics.riskLevel
      );
    });

    it('should include OWASP coverage', () => {
      const report = dashboard.generateReport();
      
      expect(Array.isArray(report.metrics.owaspCoverage)).toBe(true);
    });

    it('should include CWE distribution', () => {
      const report = dashboard.generateReport();
      
      expect(Array.isArray(report.metrics.cweDistribution)).toBe(true);
    });

    it('should include top vulnerabilities', () => {
      dashboard.addVulnerabilities([
        createMockVulnerability({ type: 'xss' }),
        createMockVulnerability({ type: 'xss' }),
        createMockVulnerability({ type: 'sql-injection' }),
      ]);
      
      const report = dashboard.generateReport();
      
      expect(Array.isArray(report.topVulnerabilities)).toBe(true);
      expect(report.topVulnerabilities.length).toBeGreaterThan(0);
    });

    it('should include component risks', () => {
      dashboard.addVulnerabilities([
        createMockVulnerability({ location: { file: 'src/a.ts', startLine: 1, endLine: 1, startColumn: 0, endColumn: 0 } }),
        createMockVulnerability({ location: { file: 'src/a.ts', startLine: 2, endLine: 2, startColumn: 0, endColumn: 0 } }),
        createMockVulnerability({ location: { file: 'src/b.ts', startLine: 1, endLine: 1, startColumn: 0, endColumn: 0 } }),
      ]);
      
      const report = dashboard.generateReport();
      
      expect(Array.isArray(report.componentRisks)).toBe(true);
    });

    it('should include scan summary', () => {
      const report = dashboard.generateReport();
      
      expect(report.scanSummary).toBeDefined();
      expect(typeof report.scanSummary.totalScans).toBe('number');
      expect(typeof report.scanSummary.filesScanned).toBe('number');
    });
  });

  describe('executive summary status', () => {
    it('should return excellent status for no vulnerabilities', () => {
      const report = dashboard.generateReport();
      
      expect(report.summary.status).toBe('excellent');
    });

    it('should return critical status for critical vulnerabilities', () => {
      dashboard.addVulnerabilities([
        createMockVulnerability({ severity: 'critical' }),
      ]);
      
      const report = dashboard.generateReport();
      
      expect(report.summary.status).toBe('critical');
    });

    it('should return warning status for many high vulnerabilities', () => {
      dashboard.addVulnerabilities([
        createMockVulnerability({ severity: 'high' }),
        createMockVulnerability({ severity: 'high' }),
        createMockVulnerability({ severity: 'high' }),
      ]);
      
      const report = dashboard.generateReport();
      
      expect(report.summary.status).toBe('warning');
    });
  });

  describe('trends', () => {
    it('should include trends when enabled', () => {
      const d = createSecurityDashboard({
        ...defaultConfig,
        includeTrends: true,
      });
      
      d.addScanResult(createMockScanResult([createMockVulnerability()]));
      const report = d.generateReport();
      
      expect(report.trends).toBeDefined();
    });

    it('should calculate trend direction', () => {
      const d = createSecurityDashboard({
        ...defaultConfig,
        includeTrends: true,
      });
      
      d.addScanResult(createMockScanResult([createMockVulnerability()]));
      const report = d.generateReport();
      
      if (report.trends) {
        expect(['improving', 'degrading', 'stable']).toContain(report.trends.direction);
      }
    });
  });

  describe('recommendations', () => {
    it('should include recommendations when enabled', () => {
      const d = createSecurityDashboard({
        ...defaultConfig,
        includeRecommendations: true,
      });
      
      d.addVulnerabilities([
        createMockVulnerability({ severity: 'critical' }),
      ]);
      const report = d.generateReport();
      
      expect(report.recommendations).toBeDefined();
      expect(Array.isArray(report.recommendations)).toBe(true);
    });

    it('should prioritize critical recommendations', () => {
      const d = createSecurityDashboard({
        ...defaultConfig,
        includeRecommendations: true,
      });
      
      d.addVulnerabilities([
        createMockVulnerability({ severity: 'critical' }),
      ]);
      const report = d.generateReport();
      
      if (report.recommendations && report.recommendations.length > 0) {
        expect(report.recommendations[0].priority).toBe('critical');
      }
    });
  });

  describe('exportReport', () => {
    it('should export as JSON by default', () => {
      const output = dashboard.exportReport();
      
      expect(() => JSON.parse(output)).not.toThrow();
    });

    it('should export as JSON when specified', () => {
      const output = dashboard.exportReport('json');
      
      const parsed = JSON.parse(output);
      expect(parsed.projectName).toBe('Test Project');
    });

    it('should export as HTML when specified', () => {
      const output = dashboard.exportReport('html');
      
      expect(output).toContain('<!DOCTYPE html>');
      expect(output).toContain('Test Project');
    });

    it('should export as Markdown when specified', () => {
      const output = dashboard.exportReport('markdown');
      
      expect(output).toContain('# Security Dashboard');
      expect(output).toContain('Test Project');
    });

    it('should include vulnerability data in HTML export', () => {
      dashboard.addVulnerabilities([createMockVulnerability()]);
      const output = dashboard.exportReport('html');
      
      expect(output).toContain('Vulnerabilities');
    });

    it('should include metrics in Markdown export', () => {
      const output = dashboard.exportReport('markdown');
      
      expect(output).toContain('Security Score');
      expect(output).toContain('Total Vulnerabilities');
    });
  });

  describe('branding', () => {
    it('should use custom title in HTML export', () => {
      const d = createSecurityDashboard({
        ...defaultConfig,
        branding: {
          title: 'Custom Security Report',
        },
      });
      
      const output = d.exportReport('html');
      
      expect(output).toContain('Custom Security Report');
    });

    it('should use custom colors in HTML export', () => {
      const d = createSecurityDashboard({
        ...defaultConfig,
        branding: {
          colors: {
            critical: '#ff0000',
          },
        },
      });
      
      const output = d.exportReport('html');
      
      expect(output).toContain('#ff0000');
    });
  });
});
