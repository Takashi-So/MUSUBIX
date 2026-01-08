/**
 * @fileoverview Report Generator Unit Tests
 * @module @nahisaho/musubix-security/cve/report-generator.test
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import * as fs from 'node:fs';
import * as path from 'node:path';
import * as os from 'node:os';
import {
  ReportGenerator,
  generateReport,
  generateReportToFile,
  getFormatFromExtension,
} from './report-generator.js';
import type { ScanResult, DetectedVulnerability } from './vulnerability-scanner.js';

/**
 * Create a mock scan result
 */
function createMockScanResult(vulns: Partial<DetectedVulnerability>[] = []): ScanResult {
  const vulnerabilities: DetectedVulnerability[] = vulns.map((v, i) => ({
    cveId: v.cveId ?? `CVE-2024-${String(i + 1).padStart(5, '0')}`,
    packageName: v.packageName ?? 'test-package',
    installedVersion: v.installedVersion ?? '1.0.0',
    description: v.description ?? `Test vulnerability ${i + 1}`,
    cvssScore: v.cvssScore ?? 7.5,
    severity: v.severity ?? 'HIGH',
    cvssVector: v.cvssVector ?? 'CVSS:3.1/AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:N/A:N',
    cwes: v.cwes ?? ['CWE-79'],
    references: v.references ?? ['https://example.com/ref'],
    isDirect: v.isDirect ?? true,
    dependencyType: v.dependencyType ?? 'dependencies',
    confidence: v.confidence ?? 0.95,
    fixedVersion: v.fixedVersion,
    affectedVersions: v.affectedVersions,
  }));

  // Calculate summary
  const summary = {
    total: vulnerabilities.length,
    critical: vulnerabilities.filter(v => v.severity === 'CRITICAL').length,
    high: vulnerabilities.filter(v => v.severity === 'HIGH').length,
    medium: vulnerabilities.filter(v => v.severity === 'MEDIUM').length,
    low: vulnerabilities.filter(v => v.severity === 'LOW').length,
    none: vulnerabilities.filter(v => v.severity === 'NONE').length,
  };

  return {
    projectName: 'test-project',
    projectVersion: '1.0.0',
    scanTimestamp: new Date().toISOString(),
    totalPackages: 10,
    directDependencies: 5,
    transitiveDependencies: 5,
    vulnerabilities,
    summary,
    durationMs: 1000,
    errors: [],
    warnings: [],
  };
}

describe('ReportGenerator', () => {
  describe('constructor', () => {
    it('should create generator with default options', () => {
      const generator = new ReportGenerator();
      expect(generator).toBeInstanceOf(ReportGenerator);
    });

    it('should accept custom options', () => {
      const generator = new ReportGenerator({
        title: 'Custom Report',
        includeDetails: false,
        minSeverity: 'HIGH',
      });
      expect(generator).toBeInstanceOf(ReportGenerator);
    });
  });

  describe('Markdown generation', () => {
    it('should generate markdown report with no vulnerabilities', () => {
      const generator = new ReportGenerator();
      const result = createMockScanResult([]);
      const report = generator.generate(result, 'markdown');

      expect(report).toContain('# Vulnerability Scan Report');
      expect(report).toContain('No Vulnerabilities Found');
    });

    it('should generate markdown report with vulnerabilities', () => {
      const generator = new ReportGenerator();
      const result = createMockScanResult([
        { cveId: 'CVE-2024-12345', severity: 'HIGH', cvssScore: 8.0 },
        { cveId: 'CVE-2024-12346', severity: 'CRITICAL', cvssScore: 9.5 },
      ]);
      const report = generator.generate(result, 'markdown');

      expect(report).toContain('CVE-2024-12345');
      expect(report).toContain('CVE-2024-12346');
      expect(report).toContain('HIGH');
      expect(report).toContain('CRITICAL');
    });

    it('should group vulnerabilities by severity', () => {
      const generator = new ReportGenerator({ groupBySeverity: true });
      const result = createMockScanResult([
        { cveId: 'CVE-2024-0001', severity: 'CRITICAL' },
        { cveId: 'CVE-2024-0002', severity: 'HIGH' },
        { cveId: 'CVE-2024-0003', severity: 'MEDIUM' },
      ]);
      const report = generator.generate(result, 'markdown');

      expect(report).toContain('### 🔴 CRITICAL');
      expect(report).toContain('### 🟠 HIGH');
      expect(report).toContain('### 🟡 MEDIUM');
    });

    it('should include metadata when configured', () => {
      const generator = new ReportGenerator({ includeMetadata: true });
      const result = createMockScanResult([]);
      const report = generator.generate(result, 'markdown');

      expect(report).toContain('Scan Summary');
      expect(report).toContain('test-project');
    });

    it('should include remediation suggestions', () => {
      const generator = new ReportGenerator({ includeRemediation: true });
      const result = createMockScanResult([
        { cveId: 'CVE-2024-12345', fixedVersion: '2.0.0' },
      ]);
      const report = generator.generate(result, 'markdown');

      expect(report).toContain('Fix Available');
      expect(report).toContain('2.0.0');
    });

    it('should include CWEs and references', () => {
      const generator = new ReportGenerator({ includeDetails: true });
      const result = createMockScanResult([
        { 
          cveId: 'CVE-2024-12345',
          cwes: ['CWE-79', 'CWE-89'],
          references: ['https://example.com/advisory'],
        },
      ]);
      const report = generator.generate(result, 'markdown');

      expect(report).toContain('CWE-79');
      expect(report).toContain('CWE-89');
      expect(report).toContain('References');
    });
  });

  describe('JSON generation', () => {
    it('should generate valid JSON', () => {
      const generator = new ReportGenerator();
      const result = createMockScanResult([]);
      const report = generator.generate(result, 'json');

      expect(() => JSON.parse(report)).not.toThrow();
    });

    it('should include meta information', () => {
      const generator = new ReportGenerator({ title: 'Custom Report' });
      const result = createMockScanResult([]);
      const report = generator.generate(result, 'json');
      const parsed = JSON.parse(report);

      expect(parsed.meta.title).toBe('Custom Report');
      expect(parsed.meta.generator).toBe('MUSUBIX Security Scanner');
    });

    it('should include vulnerability details', () => {
      const generator = new ReportGenerator();
      const result = createMockScanResult([
        { cveId: 'CVE-2024-12345', packageName: 'lodash', installedVersion: '4.17.20' },
      ]);
      const report = generator.generate(result, 'json');
      const parsed = JSON.parse(report);

      expect(parsed.vulnerabilities).toHaveLength(1);
      expect(parsed.vulnerabilities[0].id).toBe('CVE-2024-12345');
      expect(parsed.vulnerabilities[0].package.name).toBe('lodash');
      expect(parsed.vulnerabilities[0].package.version).toBe('4.17.20');
    });
  });

  describe('SARIF generation', () => {
    it('should generate valid SARIF 2.1.0', () => {
      const generator = new ReportGenerator();
      const result = createMockScanResult([]);
      const report = generator.generate(result, 'sarif');
      const sarif = JSON.parse(report);

      expect(sarif.$schema).toContain('sarif-schema-2.1.0');
      expect(sarif.version).toBe('2.1.0');
    });

    it('should include tool information', () => {
      const generator = new ReportGenerator();
      const result = createMockScanResult([]);
      const report = generator.generate(result, 'sarif');
      const sarif = JSON.parse(report);

      expect(sarif.runs[0].tool.driver.name).toBe('MUSUBIX Security Scanner');
    });

    it('should create rules for vulnerabilities', () => {
      const generator = new ReportGenerator();
      const result = createMockScanResult([
        { cveId: 'CVE-2024-12345', severity: 'HIGH', cvssScore: 8.0 },
      ]);
      const report = generator.generate(result, 'sarif');
      const sarif = JSON.parse(report);

      expect(sarif.runs[0].tool.driver.rules).toHaveLength(1);
      expect(sarif.runs[0].tool.driver.rules[0].id).toBe('CVE-2024-12345');
    });

    it('should create results for vulnerabilities', () => {
      const generator = new ReportGenerator();
      const result = createMockScanResult([
        { cveId: 'CVE-2024-12345', packageName: 'express' },
      ]);
      const report = generator.generate(result, 'sarif');
      const sarif = JSON.parse(report);

      expect(sarif.runs[0].results).toHaveLength(1);
      expect(sarif.runs[0].results[0].ruleId).toBe('CVE-2024-12345');
      expect(sarif.runs[0].results[0].properties.packageName).toBe('express');
    });

    it('should map severity to SARIF level', () => {
      const generator = new ReportGenerator();
      const result = createMockScanResult([
        { cveId: 'CVE-2024-0001', severity: 'CRITICAL' },
        { cveId: 'CVE-2024-0002', severity: 'MEDIUM' },
        { cveId: 'CVE-2024-0003', severity: 'LOW' },
      ]);
      const report = generator.generate(result, 'sarif');
      const sarif = JSON.parse(report);

      const levels = sarif.runs[0].results.map((r: { level: string }) => r.level);
      expect(levels).toContain('error');    // CRITICAL
      expect(levels).toContain('warning');  // MEDIUM
      expect(levels).toContain('note');     // LOW
    });
  });

  describe('severity filtering', () => {
    it('should filter by minimum severity', () => {
      const generator = new ReportGenerator({ minSeverity: 'HIGH' });
      const result = createMockScanResult([
        { cveId: 'CVE-2024-0001', severity: 'CRITICAL' },
        { cveId: 'CVE-2024-0002', severity: 'HIGH' },
        { cveId: 'CVE-2024-0003', severity: 'MEDIUM' },
        { cveId: 'CVE-2024-0004', severity: 'LOW' },
      ]);
      const report = generator.generate(result, 'json');
      const parsed = JSON.parse(report);

      // Should only include CRITICAL and HIGH
      expect(parsed.vulnerabilities).toHaveLength(2);
      expect(parsed.vulnerabilities.some((v: { severity: string }) => v.severity === 'MEDIUM')).toBe(false);
      expect(parsed.vulnerabilities.some((v: { severity: string }) => v.severity === 'LOW')).toBe(false);
    });
  });
});

describe('generateReport', () => {
  it('should generate report with quick function', () => {
    const result = createMockScanResult([]);
    const report = generateReport(result, 'markdown');

    expect(report).toContain('Vulnerability Scan Report');
  });

  it('should accept options', () => {
    const result = createMockScanResult([]);
    const report = generateReport(result, 'markdown', {
      title: 'Custom Title',
    });

    expect(report).toContain('Custom Title');
  });
});

describe('generateReportToFile', () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'report-gen-test-'));
  });

  afterEach(() => {
    fs.rmSync(tempDir, { recursive: true, force: true });
  });

  it('should write report to file', async () => {
    const result = createMockScanResult([]);
    const filePath = path.join(tempDir, 'report.md');

    await generateReportToFile(result, filePath, 'markdown');

    expect(fs.existsSync(filePath)).toBe(true);
    const content = fs.readFileSync(filePath, 'utf-8');
    expect(content).toContain('Vulnerability Scan Report');
  });
});

describe('getFormatFromExtension', () => {
  it('should detect markdown format', () => {
    expect(getFormatFromExtension('report.md')).toBe('markdown');
    expect(getFormatFromExtension('report.markdown')).toBe('markdown');
  });

  it('should detect SARIF format', () => {
    expect(getFormatFromExtension('report.sarif')).toBe('sarif');
  });

  it('should detect JSON format', () => {
    expect(getFormatFromExtension('report.json')).toBe('json');
  });

  it('should default to JSON for unknown extensions', () => {
    expect(getFormatFromExtension('report.txt')).toBe('json');
  });
});
