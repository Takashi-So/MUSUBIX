/**
 * @fileoverview Result Aggregator unit tests
 * @trace TST-SEC2-ORCH-003
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  ResultAggregator,
  createResultAggregator,
  mergeSimilarByLocation,
} from '../src/core/result-aggregator.js';
import type { Vulnerability, Severity, SourceLocation } from '../src/types/vulnerability.js';
import type { AnalysisResult, DetectionSource, AggregatedResult } from '../src/types/result.js';

// Helper to create test vulnerabilities
function createVulnerability(overrides: Partial<Vulnerability> = {}): Vulnerability {
  return {
    id: `VULN-${Date.now()}-${Math.random().toString(36).substr(2, 3)}`,
    type: 'injection',
    severity: 'high' as Severity,
    cwes: ['CWE-89'],
    owasp: ['A03:2021'],
    location: {
      file: 'test.ts',
      startLine: 10,
      endLine: 15,
      startColumn: 0,
      endColumn: 50,
    },
    description: 'Test vulnerability',
    recommendation: 'Fix the vulnerability',
    confidence: 0.85,
    ruleId: 'SEC-001',
    codeSnippet: 'const result = query(`SELECT * FROM users WHERE id = ${userId}`);',
    detectedAt: new Date(),
    ...overrides,
  };
}

// Helper to create test analysis results
function createAnalysisResult(
  type: DetectionSource,
  vulnerabilities: Vulnerability[]
): AnalysisResult {
  return {
    type,
    vulnerabilities,
    duration: 100,
    timestamp: new Date(),
  };
}

describe('ResultAggregator', () => {
  let aggregator: ResultAggregator;

  beforeEach(() => {
    aggregator = createResultAggregator();
  });

  describe('aggregate', () => {
    it('should aggregate results from multiple analyzers', () => {
      const vuln1 = createVulnerability({ 
        id: 'VULN-001',
        location: { file: 'file1.ts', startLine: 10, endLine: 15, startColumn: 0, endColumn: 50 }
      });
      const vuln2 = createVulnerability({ 
        id: 'VULN-002', 
        severity: 'critical' as Severity,
        location: { file: 'file2.ts', startLine: 20, endLine: 25, startColumn: 0, endColumn: 50 }
      });

      const results: AnalysisResult[] = [
        createAnalysisResult('sast', [vuln1]),
        createAnalysisResult('taint', [vuln2]),
      ];

      const aggregated = aggregator.aggregate(results);

      expect(aggregated.vulnerabilities.length).toBe(2);
      expect(aggregated.sources).toContain('sast');
      expect(aggregated.sources).toContain('taint');
    });

    it('should calculate risk score', () => {
      const criticalVuln = createVulnerability({ severity: 'critical' as Severity, confidence: 0.95 });
      const results: AnalysisResult[] = [
        createAnalysisResult('sast', [criticalVuln]),
      ];

      const aggregated = aggregator.aggregate(results);

      expect(aggregated.riskScore).toBeGreaterThan(0);
      expect(aggregated.riskScore).toBeLessThanOrEqual(100);
    });

    it('should count vulnerabilities by severity', () => {
      const vuln1 = createVulnerability({ 
        severity: 'critical' as Severity,
        location: { file: 'file1.ts', startLine: 10, endLine: 15, startColumn: 0, endColumn: 50 }
      });
      const vuln2 = createVulnerability({ 
        severity: 'high' as Severity,
        location: { file: 'file2.ts', startLine: 20, endLine: 25, startColumn: 0, endColumn: 50 }
      });
      const vuln3 = createVulnerability({ 
        severity: 'medium' as Severity,
        location: { file: 'file3.ts', startLine: 30, endLine: 35, startColumn: 0, endColumn: 50 }
      });

      const results: AnalysisResult[] = [
        createAnalysisResult('sast', [vuln1, vuln2, vuln3]),
      ];

      const aggregated = aggregator.aggregate(results);

      expect(aggregated.bySeverity.critical).toBe(1);
      expect(aggregated.bySeverity.high).toBe(1);
      expect(aggregated.bySeverity.medium).toBe(1);
      expect(aggregated.bySeverity.low).toBe(0);
      expect(aggregated.bySeverity.info).toBe(0);
    });

    it('should count vulnerabilities by source', () => {
      const vuln1 = createVulnerability({
        location: { file: 'file1.ts', startLine: 10, endLine: 15, startColumn: 0, endColumn: 50 }
      });
      const vuln2 = createVulnerability({
        location: { file: 'file2.ts', startLine: 20, endLine: 25, startColumn: 0, endColumn: 50 }
      });
      const vuln3 = createVulnerability({
        location: { file: 'file3.ts', startLine: 30, endLine: 35, startColumn: 0, endColumn: 50 }
      });

      const results: AnalysisResult[] = [
        createAnalysisResult('sast', [vuln1, vuln2]),
        createAnalysisResult('taint', [vuln3]),
      ];

      const aggregated = aggregator.aggregate(results);

      expect(aggregated.bySource.sast).toBe(2);
      expect(aggregated.bySource.taint).toBe(1);
    });

    it('should handle empty results', () => {
      const results: AnalysisResult[] = [];

      const aggregated = aggregator.aggregate(results);

      expect(aggregated.vulnerabilities).toHaveLength(0);
      expect(aggregated.riskScore).toBe(0);
      expect(aggregated.duplicatesRemoved).toBe(0);
    });
  });

  describe('deduplicate', () => {
    it('should remove duplicate vulnerabilities with same location and CWE', () => {
      const location: SourceLocation = {
        file: 'test.ts',
        startLine: 10,
        endLine: 15,
        startColumn: 0,
        endColumn: 50,
      };

      const vuln1 = createVulnerability({
        id: 'VULN-001',
        location,
        cwes: ['CWE-89'],
        confidence: 0.8,
      });
      const vuln2 = createVulnerability({
        id: 'VULN-002',
        location,
        cwes: ['CWE-89'],
        confidence: 0.9,
      });

      const deduplicated = aggregator.deduplicate([vuln1, vuln2]);

      expect(deduplicated.length).toBe(1);
      // Should keep the one with higher confidence
      expect(deduplicated[0].confidence).toBe(0.9);
    });

    it('should keep unique vulnerabilities', () => {
      const vuln1 = createVulnerability({
        id: 'VULN-001',
        location: { file: 'a.ts', startLine: 10, endLine: 15, startColumn: 0, endColumn: 50 },
      });
      const vuln2 = createVulnerability({
        id: 'VULN-002',
        location: { file: 'b.ts', startLine: 20, endLine: 25, startColumn: 0, endColumn: 50 },
      });

      const deduplicated = aggregator.deduplicate([vuln1, vuln2]);

      expect(deduplicated.length).toBe(2);
    });

    it('should handle single vulnerability', () => {
      const vuln = createVulnerability();

      const deduplicated = aggregator.deduplicate([vuln]);

      expect(deduplicated.length).toBe(1);
    });

    it('should handle empty array', () => {
      const deduplicated = aggregator.deduplicate([]);

      expect(deduplicated).toHaveLength(0);
    });
  });

  describe('prioritize', () => {
    it('should sort vulnerabilities by priority score', () => {
      const lowVuln = createVulnerability({ severity: 'low' as Severity, confidence: 0.5 });
      const criticalVuln = createVulnerability({ severity: 'critical' as Severity, confidence: 0.95 });
      const mediumVuln = createVulnerability({ severity: 'medium' as Severity, confidence: 0.7 });

      const prioritized = aggregator.prioritize([lowVuln, criticalVuln, mediumVuln]);

      expect(prioritized[0].severity).toBe('critical');
      expect(prioritized[prioritized.length - 1].severity).toBe('low');
    });

    it('should consider confidence in prioritization', () => {
      const highConfidence = createVulnerability({ 
        severity: 'high' as Severity, 
        confidence: 0.99,
      });
      const lowConfidence = createVulnerability({ 
        severity: 'high' as Severity, 
        confidence: 0.5,
      });

      const prioritized = aggregator.prioritize([lowConfidence, highConfidence]);

      // Higher confidence should come first (same severity)
      expect(prioritized[0].confidence).toBe(0.99);
    });
  });

  describe('calculateRiskScore', () => {
    it('should return 0 for empty array', () => {
      const score = aggregator.calculateRiskScore([]);

      expect(score).toBe(0);
    });

    it('should return high score for critical vulnerabilities', () => {
      const criticalVulns = [
        createVulnerability({ severity: 'critical' as Severity, confidence: 0.95 }),
        createVulnerability({ severity: 'critical' as Severity, confidence: 0.90 }),
      ];

      const score = aggregator.calculateRiskScore(criticalVulns);

      expect(score).toBeGreaterThan(70);
    });

    it('should return lower score for only info vulnerabilities', () => {
      const infoVulns = [
        createVulnerability({ severity: 'info' as Severity, confidence: 0.5 }),
        createVulnerability({ severity: 'info' as Severity, confidence: 0.6 }),
      ];

      const score = aggregator.calculateRiskScore(infoVulns);

      expect(score).toBeLessThan(30);
    });

    it('should increase score with more vulnerabilities', () => {
      const singleVuln = [createVulnerability({ severity: 'high' as Severity })];
      const multipleVulns = [
        createVulnerability({ severity: 'high' as Severity }),
        createVulnerability({ severity: 'high' as Severity }),
        createVulnerability({ severity: 'high' as Severity }),
      ];

      const singleScore = aggregator.calculateRiskScore(singleVuln);
      const multipleScore = aggregator.calculateRiskScore(multipleVulns);

      expect(multipleScore).toBeGreaterThan(singleScore);
    });
  });

  describe('mergeVulnerabilities', () => {
    it('should merge sources from both vulnerabilities', () => {
      const vuln1 = {
        ...createVulnerability({ id: 'VULN-001' }),
        sources: ['sast' as DetectionSource],
        originalIds: ['VULN-001'],
        isDuplicate: false,
        priorityScore: 0,
        riskScore: 0,
      };
      const vuln2 = {
        ...createVulnerability({ id: 'VULN-002' }),
        sources: ['taint' as DetectionSource],
        originalIds: ['VULN-002'],
        isDuplicate: false,
        priorityScore: 0,
        riskScore: 0,
      };

      const merged = aggregator.mergeVulnerabilities(vuln1, vuln2, 'merge');

      expect(merged.sources).toContain('sast');
      expect(merged.sources).toContain('taint');
      expect(merged.originalIds).toContain('VULN-001');
      expect(merged.originalIds).toContain('VULN-002');
    });
  });
});

describe('mergeSimilarByLocation', () => {
  it('should merge vulnerabilities with overlapping locations', () => {
    const vuln1 = createVulnerability({
      location: { file: 'test.ts', startLine: 10, endLine: 15, startColumn: 0, endColumn: 50 },
      severity: 'high' as Severity,
    });
    const vuln2 = createVulnerability({
      location: { file: 'test.ts', startLine: 12, endLine: 18, startColumn: 0, endColumn: 50 },
      severity: 'critical' as Severity,
    });

    const merged = mergeSimilarByLocation([vuln1, vuln2], 0.3);

    expect(merged.length).toBe(1);
    expect(merged[0].severity).toBe('critical'); // Higher severity preserved
  });

  it('should not merge vulnerabilities in different files', () => {
    const vuln1 = createVulnerability({
      location: { file: 'a.ts', startLine: 10, endLine: 15, startColumn: 0, endColumn: 50 },
    });
    const vuln2 = createVulnerability({
      location: { file: 'b.ts', startLine: 10, endLine: 15, startColumn: 0, endColumn: 50 },
    });

    const merged = mergeSimilarByLocation([vuln1, vuln2]);

    expect(merged.length).toBe(2);
  });

  it('should not merge non-overlapping vulnerabilities', () => {
    const vuln1 = createVulnerability({
      location: { file: 'test.ts', startLine: 10, endLine: 15, startColumn: 0, endColumn: 50 },
    });
    const vuln2 = createVulnerability({
      location: { file: 'test.ts', startLine: 100, endLine: 105, startColumn: 0, endColumn: 50 },
    });

    const merged = mergeSimilarByLocation([vuln1, vuln2]);

    expect(merged.length).toBe(2);
  });

  it('should combine CWEs when merging', () => {
    const vuln1 = createVulnerability({
      location: { file: 'test.ts', startLine: 10, endLine: 20, startColumn: 0, endColumn: 50 },
      cwes: ['CWE-89'],
    });
    const vuln2 = createVulnerability({
      location: { file: 'test.ts', startLine: 10, endLine: 20, startColumn: 0, endColumn: 50 },
      cwes: ['CWE-79'],
    });

    const merged = mergeSimilarByLocation([vuln1, vuln2], 0.9);

    expect(merged.length).toBe(1);
    expect(merged[0].cwes).toContain('CWE-89');
    expect(merged[0].cwes).toContain('CWE-79');
  });
});

describe('AggregatedResult', () => {
  it('should track aggregation duration', () => {
    const aggregator = createResultAggregator();
    const results: AnalysisResult[] = [
      createAnalysisResult('sast', [createVulnerability()]),
    ];

    const aggregated = aggregator.aggregate(results);

    expect(aggregated.aggregationDuration).toBeGreaterThanOrEqual(0);
    expect(aggregated.aggregatedAt).toBeInstanceOf(Date);
  });

  it('should track duplicates removed count', () => {
    const aggregator = createResultAggregator();
    const location: SourceLocation = {
      file: 'test.ts',
      startLine: 10,
      endLine: 15,
      startColumn: 0,
      endColumn: 50,
    };

    const results: AnalysisResult[] = [
      createAnalysisResult('sast', [
        createVulnerability({ location, cwes: ['CWE-89'] }),
        createVulnerability({ location, cwes: ['CWE-89'] }),
      ]),
    ];

    const aggregated = aggregator.aggregate(results);

    expect(aggregated.duplicatesRemoved).toBe(1);
  });
});
