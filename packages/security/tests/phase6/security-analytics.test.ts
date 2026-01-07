/**
 * @fileoverview Tests for Security Analytics component
 * @module @nahisaho/musubix-security/tests/phase6/security-analytics
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  SecurityAnalytics,
  createSecurityAnalytics,
  type SecurityMetric,
  type SecurityTrend,
  type SecurityDashboard,
} from '../../src/intelligence/security-analytics.js';
import type { Vulnerability } from '../../src/types/index.js';

describe('SecurityAnalytics', () => {
  let analytics: SecurityAnalytics;

  const createVulnerability = (
    type: Vulnerability['type'],
    severity: Vulnerability['severity']
  ): Vulnerability => ({
    id: `TEST-${Date.now()}-${Math.random()}`,
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
    analytics = new SecurityAnalytics();
  });

  describe('Event Recording', () => {
    it('should record vulnerability discovery', () => {
      const vuln = createVulnerability('injection', 'critical');
      analytics.recordVulnerability(vuln);

      const events = analytics.getEventsByType('vulnerability');
      expect(events.length).toBeGreaterThan(0);
    });

    it('should record fix events', () => {
      const vuln = createVulnerability('xss', 'high');
      analytics.recordVulnerability(vuln);
      analytics.recordFix(vuln.id);

      const events = analytics.getEventsByType('fix');
      expect(events.length).toBeGreaterThan(0);
    });

    it('should record scan events', () => {
      analytics.recordScan({
        filesScanned: 100,
        vulnerabilitiesFound: 5,
        duration: 1500,
      });

      const events = analytics.getEventsByType('scan');
      expect(events.length).toBe(1);
    });
  });

  describe('Metric Calculation', () => {
    beforeEach(() => {
      // Record some vulnerabilities
      analytics.recordVulnerability(createVulnerability('injection', 'critical'));
      analytics.recordVulnerability(createVulnerability('xss', 'high'));
      analytics.recordVulnerability(createVulnerability('path-traversal', 'medium'));
    });

    it('should calculate vulnerability count metric', () => {
      const metric = analytics.calculateMetric('vulnerability-count', 'day');

      expect(metric).toBeDefined();
      expect(metric.value).toBe(3);
      expect(metric.type).toBe('vulnerability-count');
    });

    it('should calculate average risk score', () => {
      const metric = analytics.calculateMetric('average-risk-score', 'day');

      expect(metric).toBeDefined();
      expect(metric.type).toBe('average-risk-score');
    });

    it('should include period information', () => {
      const metric = analytics.calculateMetric('vulnerability-count', 'week');

      expect(metric.period).toBe('week');
      expect(metric.timestamp).toBeInstanceOf(Date);
    });

    it('should include change information', () => {
      const metric = analytics.calculateMetric('vulnerability-count', 'day');

      expect(metric.change).toBeDefined();
      expect(metric.change.direction).toBeDefined();
    });
  });

  describe('Dashboard Generation', () => {
    beforeEach(() => {
      analytics.recordVulnerability(createVulnerability('injection', 'critical'));
      analytics.recordVulnerability(createVulnerability('xss', 'high'));
    });

    it('should generate security dashboard', () => {
      const dashboard = analytics.generateDashboard();

      expect(dashboard).toBeDefined();
      expect(dashboard.metrics).toBeDefined();
    });

    it('should include summary in dashboard', () => {
      const dashboard = analytics.generateDashboard();

      expect(dashboard.summary).toBeDefined();
    });

    it('should include trends in dashboard', () => {
      const dashboard = analytics.generateDashboard();

      expect(dashboard.trends).toBeDefined();
    });
  });

  describe('Trend Analysis', () => {
    beforeEach(() => {
      analytics.recordVulnerability(createVulnerability('injection', 'high'));
      analytics.recordVulnerability(createVulnerability('xss', 'medium'));
    });

    it('should calculate metrics over time', () => {
      const metric1 = analytics.calculateMetric('vulnerability-count', 'day');
      analytics.recordVulnerability(createVulnerability('path-traversal', 'low'));
      const metric2 = analytics.calculateMetric('vulnerability-count', 'day');

      expect(metric2.value).toBeGreaterThanOrEqual(metric1.value);
    });
  });

  describe('Factory Functions', () => {
    it('should create analytics with options', () => {
      const customAnalytics = createSecurityAnalytics({
        retentionDays: 30,
      });
      expect(customAnalytics).toBeInstanceOf(SecurityAnalytics);
    });

    it('should create analytics with alert thresholds', () => {
      const customAnalytics = createSecurityAnalytics({
        alertThresholds: {
          criticalVulnerabilities: 0,
          highVulnerabilities: 5,
          riskScoreIncrease: 10,
        },
      });
      expect(customAnalytics).toBeInstanceOf(SecurityAnalytics);
    });
  });

  describe('Edge Cases', () => {
    it('should handle no events', () => {
      const metric = analytics.calculateMetric('vulnerability-count', 'day');

      expect(metric.value).toBe(0);
    });

    it('should handle empty dashboard', () => {
      const dashboard = analytics.generateDashboard();

      expect(dashboard).toBeDefined();
    });

    it('should filter events by date', () => {
      analytics.recordVulnerability(createVulnerability('xss', 'high'));

      const since = new Date();
      since.setDate(since.getDate() - 1);

      const events = analytics.getEventsByType('vulnerability', since);
      expect(events.length).toBe(1);
    });
  });
});
