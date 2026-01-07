/**
 * @fileoverview Report Aggregator Tests
 * @module @nahisaho/musubix-security/tests/phase4/report-aggregator
 */

import { describe, it, expect } from 'vitest';
import {
  ReportAggregator,
  createReportAggregator,
  type ScanType,
} from '../../src/integrations/report-aggregator.js';
import type { ScanResult, Vulnerability, SourceLocation, VulnerabilityType } from '../../src/types/index.js';

describe('ReportAggregator', () => {
  const createMockLocation = (file: string, startLine: number): SourceLocation => ({
    file,
    startLine,
    endLine: startLine,
    startColumn: 1,
    endColumn: 50,
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

  const createMockVulnerability = (
    ruleId: string,
    severity: 'critical' | 'high' | 'medium' | 'low' | 'info',
    file: string = 'src/test.ts',
    startLine: number = 10
  ): Vulnerability => ({
    id: `VULN-${Date.now()}-${Math.random()}`,
    type: 'xss' as VulnerabilityType,
    ruleId,
    severity,
    description: `Test ${severity} vulnerability in ${file}`,
    recommendation: 'Fix the issue',
    confidence: 0.9,
    cwes: ['CWE-79'],
    owasp: ['A01:2021'],
    detectedAt: new Date(),
    location: createMockLocation(file, startLine),
  });

  describe('createReportAggregator', () => {
    it('should create aggregator with default options', () => {
      const aggregator = createReportAggregator();
      expect(aggregator).toBeInstanceOf(ReportAggregator);
    });

    it('should create aggregator with custom options', () => {
      const aggregator = createReportAggregator({
        deduplicate: false,
        groupBy: 'file',
      });
      expect(aggregator).toBeInstanceOf(ReportAggregator);
    });
  });

  describe('addScan', () => {
    it('should add scan and return ID', () => {
      const aggregator = createReportAggregator();
      const result = createMockScanResult();
      
      const id = aggregator.addScan('test-scan', result, 'vulnerability');
      
      expect(id).toMatch(/^scan-\d+-\d+$/);
      expect(aggregator.getScanCount()).toBe(1);
    });

    it('should support multiple scans', () => {
      const aggregator = createReportAggregator();
      
      aggregator.addScan('scan1', createMockScanResult(), 'vulnerability');
      aggregator.addScan('scan2', createMockScanResult(), 'secret');
      aggregator.addScan('scan3', createMockScanResult(), 'dependency');
      
      expect(aggregator.getScanCount()).toBe(3);
    });

    it('should accept metadata', () => {
      const aggregator = createReportAggregator();
      const result = createMockScanResult();
      
      const id = aggregator.addScan('test-scan', result, 'full', { branch: 'main' });
      
      expect(id).toBeDefined();
    });
  });

  describe('removeScan', () => {
    it('should remove scan by ID', () => {
      const aggregator = createReportAggregator();
      const result = createMockScanResult();
      
      const id = aggregator.addScan('test-scan', result);
      expect(aggregator.getScanCount()).toBe(1);
      
      const removed = aggregator.removeScan(id);
      
      expect(removed).toBe(true);
      expect(aggregator.getScanCount()).toBe(0);
    });

    it('should return false for non-existent ID', () => {
      const aggregator = createReportAggregator();
      
      const removed = aggregator.removeScan('non-existent');
      
      expect(removed).toBe(false);
    });
  });

  describe('clear', () => {
    it('should clear all scans', () => {
      const aggregator = createReportAggregator();
      
      aggregator.addScan('scan1', createMockScanResult());
      aggregator.addScan('scan2', createMockScanResult());
      expect(aggregator.getScanCount()).toBe(2);
      
      aggregator.clear();
      
      expect(aggregator.getScanCount()).toBe(0);
    });
  });

  describe('generateReport', () => {
    it('should generate report with basic structure', () => {
      const aggregator = createReportAggregator();
      const vulns = [createMockVulnerability('SEC-001', 'high')];
      
      aggregator.addScan('test', createMockScanResult(vulns), 'vulnerability');
      const report = aggregator.generateReport();
      
      expect(report.reportId).toBeDefined();
      expect(report.generatedAt).toBeInstanceOf(Date);
      expect(report.summary).toBeDefined();
      expect(report.findings.length).toBe(1);
      expect(report.sources.length).toBe(1);
    });

    it('should aggregate findings from multiple scans', () => {
      const aggregator = createReportAggregator({ deduplicate: false });
      
      aggregator.addScan('scan1', createMockScanResult([
        createMockVulnerability('SEC-001', 'high'),
      ]));
      aggregator.addScan('scan2', createMockScanResult([
        createMockVulnerability('SEC-002', 'medium'),
      ]));
      
      const report = aggregator.generateReport();
      
      expect(report.summary.totalScans).toBe(2);
      expect(report.summary.totalFindings).toBe(2);
    });

    it('should deduplicate similar findings', () => {
      const aggregator = createReportAggregator({ deduplicate: true });
      
      // Add same vulnerability twice
      aggregator.addScan('scan1', createMockScanResult([
        createMockVulnerability('SEC-001', 'high', 'src/test.ts', 10),
      ]));
      aggregator.addScan('scan2', createMockScanResult([
        createMockVulnerability('SEC-001', 'high', 'src/test.ts', 10),
      ]));
      
      const report = aggregator.generateReport();
      
      expect(report.findings.length).toBe(1);
      expect(report.findings[0].occurrences).toBe(2);
    });

    it('should calculate security score correctly', () => {
      const aggregator = createReportAggregator();
      
      aggregator.addScan('test', createMockScanResult([
        createMockVulnerability('SEC-001', 'critical'), // -25
        createMockVulnerability('SEC-002', 'high'),     // -10
      ]));
      
      const report = aggregator.generateReport();
      
      expect(report.summary.securityScore).toBe(65);
    });

    it('should determine risk level correctly', () => {
      const aggregator = createReportAggregator();
      
      aggregator.addScan('test', createMockScanResult([
        createMockVulnerability('SEC-001', 'critical'),
      ]));
      
      const report = aggregator.generateReport();
      
      expect(report.summary.riskLevel).toBe('critical');
    });

    it('should group findings by file', () => {
      const aggregator = createReportAggregator();
      
      aggregator.addScan('test', createMockScanResult([
        createMockVulnerability('SEC-001', 'high', 'src/a.ts'),
        createMockVulnerability('SEC-002', 'high', 'src/a.ts'),
        createMockVulnerability('SEC-003', 'high', 'src/b.ts'),
      ]));
      
      const report = aggregator.generateReport();
      
      expect(report.groupedFindings.byFile.get('src/a.ts')?.length).toBe(2);
      expect(report.groupedFindings.byFile.get('src/b.ts')?.length).toBe(1);
    });

    it('should group findings by severity', () => {
      const aggregator = createReportAggregator();
      
      aggregator.addScan('test', createMockScanResult([
        createMockVulnerability('SEC-001', 'high'),
        createMockVulnerability('SEC-002', 'high'),
        createMockVulnerability('SEC-003', 'low'),
      ]));
      
      const report = aggregator.generateReport();
      
      expect(report.groupedFindings.bySeverity.get('high')?.length).toBe(2);
      expect(report.groupedFindings.bySeverity.get('low')?.length).toBe(1);
    });

    it('should generate scan sources', () => {
      const aggregator = createReportAggregator();
      
      aggregator.addScan('vuln-scan', createMockScanResult(), 'vulnerability');
      aggregator.addScan('secret-scan', createMockScanResult(), 'secret');
      
      const report = aggregator.generateReport();
      
      expect(report.sources.length).toBe(2);
      expect(report.sources[0].type).toBe('vulnerability');
      expect(report.sources[1].type).toBe('secret');
    });

    it('should generate trend data', () => {
      const aggregator = createReportAggregator({ includeHistory: true });
      
      aggregator.addScan('test', createMockScanResult());
      const report = aggregator.generateReport();
      
      expect(report.trends).toBeDefined();
      expect(report.trends.dataPoints.length).toBeGreaterThan(0);
      expect(['improving', 'stable', 'degrading']).toContain(report.trends.direction);
    });
  });

  describe('history and comparison', () => {
    it('should save reports to history', () => {
      const aggregator = createReportAggregator({ includeHistory: true });
      
      aggregator.addScan('test1', createMockScanResult());
      aggregator.generateReport();
      
      aggregator.clear();
      aggregator.addScan('test2', createMockScanResult());
      aggregator.generateReport();
      
      expect(aggregator.getHistory().length).toBe(2);
    });

    it('should limit history size', () => {
      const aggregator = createReportAggregator({
        includeHistory: true,
        maxHistoryEntries: 2,
      });
      
      for (let i = 0; i < 5; i++) {
        aggregator.clear();
        aggregator.addScan(`test${i}`, createMockScanResult());
        aggregator.generateReport();
      }
      
      expect(aggregator.getHistory().length).toBe(2);
    });

    it('should compare with previous report', () => {
      const aggregator = createReportAggregator({ includeHistory: true });
      
      // First report with one vulnerability
      aggregator.addScan('test1', createMockScanResult([
        createMockVulnerability('SEC-001', 'high'),
      ]));
      aggregator.generateReport();
      
      // Second report with different vulnerability
      aggregator.clear();
      aggregator.addScan('test2', createMockScanResult([
        createMockVulnerability('SEC-002', 'medium'),
      ]));
      const report = aggregator.generateReport();
      
      expect(report.comparison).toBeDefined();
      expect(report.comparison!.newFindings.length).toBe(1);
      expect(report.comparison!.fixedFindings.length).toBe(1);
    });
  });

  describe('exportJSON', () => {
    it('should export report as JSON', () => {
      const aggregator = createReportAggregator();
      
      aggregator.addScan('test', createMockScanResult([
        createMockVulnerability('SEC-001', 'high'),
      ]));
      const report = aggregator.generateReport();
      
      const json = aggregator.exportJSON(report);
      const parsed = JSON.parse(json);
      
      expect(parsed.reportId).toBe(report.reportId);
      expect(parsed.summary.totalFindings).toBe(1);
    });

    it('should handle dates in JSON export', () => {
      const aggregator = createReportAggregator();
      
      aggregator.addScan('test', createMockScanResult());
      const report = aggregator.generateReport();
      
      const json = aggregator.exportJSON(report);
      const parsed = JSON.parse(json);
      
      expect(parsed.generatedAt).toMatch(/^\d{4}-\d{2}-\d{2}T/);
    });
  });

  describe('exportMarkdown', () => {
    it('should export report as Markdown', () => {
      const aggregator = createReportAggregator();
      
      aggregator.addScan('test', createMockScanResult([
        createMockVulnerability('SEC-001', 'high'),
      ]));
      const report = aggregator.generateReport();
      
      const markdown = aggregator.exportMarkdown(report);
      
      expect(markdown).toContain('# Security Scan Aggregated Report');
      expect(markdown).toContain('## Summary');
      expect(markdown).toContain('| Severity | Count |');
    });

    it('should include comparison in markdown when available', () => {
      const aggregator = createReportAggregator({ includeHistory: true });
      
      // Generate two reports
      aggregator.addScan('test1', createMockScanResult());
      aggregator.generateReport();
      
      aggregator.clear();
      aggregator.addScan('test2', createMockScanResult([
        createMockVulnerability('SEC-001', 'high'),
      ]));
      const report = aggregator.generateReport();
      
      const markdown = aggregator.exportMarkdown(report);
      
      expect(markdown).toContain('## Changes from Previous');
    });

    it('should include top findings', () => {
      const aggregator = createReportAggregator();
      
      aggregator.addScan('test', createMockScanResult([
        createMockVulnerability('CRITICAL-RULE', 'critical'),
      ]));
      const report = aggregator.generateReport();
      
      const markdown = aggregator.exportMarkdown(report);
      
      expect(markdown).toContain('## Top Findings');
      expect(markdown).toContain('CRITICAL-RULE');
    });
  });
});
