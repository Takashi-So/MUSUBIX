/**
 * @fileoverview Tests for Risk Scorer component
 * @module @nahisaho/musubix-security/tests/phase6/risk-scorer
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  RiskScorer,
  createRiskScorer,
  quickRiskScore,
  type RiskScore,
  type CVSSScore,
  type CVSSMetrics,
  type BusinessImpact,
} from '../../src/intelligence/risk-scorer.js';
import type { Vulnerability } from '../../src/types/index.js';

describe('RiskScorer', () => {
  let scorer: RiskScorer;

  const createVulnerability = (
    type: Vulnerability['type'],
    severity: Vulnerability['severity']
  ): Vulnerability => ({
    id: `TEST-${Date.now()}`,
    type,
    severity,
    cwes: ['CWE-89'],
    location: {
      file: 'test.ts',
      startLine: 10,
      endLine: 10,
      startColumn: 0,
      endColumn: 50,
    },
    description: 'Test vulnerability',
    recommendation: 'Fix the issue',
    confidence: 0.9,
    ruleId: 'test-rule',
    detectedAt: new Date(),
  });

  beforeEach(() => {
    scorer = new RiskScorer();
  });

  describe('CVSS Calculation', () => {
    it('should calculate CVSS score for injection', () => {
      const vuln = createVulnerability('injection', 'critical');
      const cvss = scorer.calculateCVSS(vuln);

      expect(cvss).toBeDefined();
      expect(cvss.baseScore).toBeGreaterThanOrEqual(0);
      expect(cvss.baseScore).toBeLessThanOrEqual(10);
      expect(cvss.severity).toBeDefined();
    });

    it('should calculate CVSS score for XSS', () => {
      const vuln = createVulnerability('xss', 'high');
      const cvss = scorer.calculateCVSS(vuln);

      expect(cvss.baseScore).toBeGreaterThan(0);
      expect(['low', 'medium', 'high', 'critical']).toContain(cvss.severity);
    });

    it('should generate CVSS vector string', () => {
      const vuln = createVulnerability('injection', 'high');
      const cvss = scorer.calculateCVSS(vuln);

      expect(cvss.vectorString).toMatch(/^CVSS:3\.1\//);
      expect(cvss.vectorString).toContain('AV:');
      expect(cvss.vectorString).toContain('AC:');
    });

    it('should include component scores', () => {
      const vuln = createVulnerability('command-injection', 'critical');
      const cvss = scorer.calculateCVSS(vuln);

      expect(cvss.components).toBeDefined();
      expect(cvss.components.exploitability).toBeGreaterThanOrEqual(0);
      expect(cvss.components.impact).toBeGreaterThanOrEqual(0);
    });

    it('should include metrics', () => {
      const vuln = createVulnerability('xss', 'medium');
      const cvss = scorer.calculateCVSS(vuln);

      expect(cvss.metrics).toBeDefined();
      expect(cvss.metrics.attackVector).toBeDefined();
      expect(cvss.metrics.attackComplexity).toBeDefined();
    });
  });

  describe('Business Impact Assessment', () => {
    it('should assess business impact', () => {
      const vuln = createVulnerability('injection', 'critical');
      const impacts = scorer.assessBusinessImpact(vuln);

      expect(Array.isArray(impacts)).toBe(true);
      expect(impacts.length).toBeGreaterThan(0);
    });

    it('should include financial impact', () => {
      const vuln = createVulnerability('injection', 'critical');
      const impacts = scorer.assessBusinessImpact(vuln);

      const financial = impacts.find(i => i.category === 'financial');
      expect(financial).toBeDefined();
      expect(financial?.level).toBeGreaterThanOrEqual(0);
    });

    it('should include reputation impact', () => {
      const vuln = createVulnerability('xss', 'high');
      const impacts = scorer.assessBusinessImpact(vuln);

      const reputation = impacts.find(i => i.category === 'reputation');
      expect(reputation).toBeDefined();
    });

    it('should include operational impact', () => {
      const vuln = createVulnerability('command-injection', 'critical');
      const impacts = scorer.assessBusinessImpact(vuln);

      const operational = impacts.find(i => i.category === 'operational');
      expect(operational).toBeDefined();
    });
  });

  describe('Factory Functions', () => {
    it('should create scorer with options', () => {
      const customScorer = createRiskScorer({
        riskTolerance: 30,
      });
      expect(customScorer).toBeInstanceOf(RiskScorer);
    });

    it('should perform quick risk score', () => {
      const vuln = createVulnerability('injection', 'critical');
      const score = quickRiskScore(vuln);

      expect(score).toBeDefined();
      expect(score.overallScore).toBeGreaterThanOrEqual(0);
    });
  });

  describe('Edge Cases', () => {
    it('should handle low severity vulnerabilities', () => {
      const vuln = createVulnerability('sensitive-exposure', 'low');
      const cvss = scorer.calculateCVSS(vuln);

      expect(cvss.baseScore).toBeGreaterThanOrEqual(0);
    });

    it('should handle different vulnerability types', () => {
      const types: Vulnerability['type'][] = ['xss', 'injection', 'path-traversal', 'ssrf'];
      
      for (const type of types) {
        const vuln = createVulnerability(type, 'high');
        const cvss = scorer.calculateCVSS(vuln);
        expect(cvss.baseScore).toBeGreaterThanOrEqual(0);
        expect(cvss.baseScore).toBeLessThanOrEqual(10);
      }
    });
  });
});
