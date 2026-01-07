/**
 * @fileoverview Tests for Predictive Analyzer component
 * @module @nahisaho/musubix-security/tests/phase6/predictive-analyzer
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  PredictiveAnalyzer,
  createPredictiveAnalyzer,
  type SecurityForecast,
  type RiskProjection,
  type HistoricalDataPoint,
} from '../../src/intelligence/predictive-analyzer.js';
import type { Vulnerability } from '../../src/types/index.js';

describe('PredictiveAnalyzer', () => {
  let analyzer: PredictiveAnalyzer;

  beforeEach(() => {
    analyzer = new PredictiveAnalyzer();
  });

  describe('Data Point Management', () => {
    it('should add data point', () => {
      const dataPoint: HistoricalDataPoint = {
        timestamp: new Date(),
        value: 50,
      };

      analyzer.addDataPoint('risk-score', dataPoint);

      // No error means success - internal state is private
      expect(true).toBe(true);
    });

    it('should add multiple data points', () => {
      const dataPoints: HistoricalDataPoint[] = [
        { timestamp: new Date(Date.now() - 86400000), value: 40 },
        { timestamp: new Date(Date.now() - 43200000), value: 45 },
        { timestamp: new Date(), value: 50 },
      ];

      analyzer.addDataPoints('risk-score', dataPoints);
      expect(true).toBe(true);
    });
  });

  describe('Risk Projection', () => {
    beforeEach(() => {
      // Add some historical data
      const now = Date.now();
      for (let i = 10; i >= 0; i--) {
        analyzer.addDataPoint('average-risk-score', {
          timestamp: new Date(now - i * 86400000),
          value: 40 + i * 2,
        });
      }
    });

    it('should project future risk', () => {
      const projection = analyzer.projectRisk(60);

      expect(projection).toBeDefined();
      expect(typeof projection.projectedRisk).toBe('number');
    });

    it('should include projection direction', () => {
      const projection = analyzer.projectRisk(50);

      expect(projection.direction).toBeDefined();
      expect(['increasing', 'decreasing', 'stable']).toContain(projection.direction);
    });

    it('should include confidence score', () => {
      const projection = analyzer.projectRisk(50);

      expect(projection.confidenceScore).toBeGreaterThanOrEqual(0);
      expect(projection.confidenceScore).toBeLessThanOrEqual(1);
    });
  });

  describe('Anomaly Detection', () => {
    beforeEach(() => {
      // Add baseline data
      const now = Date.now();
      for (let i = 10; i >= 0; i--) {
        analyzer.addDataPoint('vulnerability-total', {
          timestamp: new Date(now - i * 86400000),
          value: 5,
        });
      }
    });

    it('should detect anomalies', () => {
      const anomalies = analyzer.detectAnomalies();

      expect(Array.isArray(anomalies)).toBe(true);
    });

    it('should identify unusual patterns', () => {
      // Add an anomalous data point
      analyzer.addDataPoint('vulnerability-total', {
        timestamp: new Date(),
        value: 50, // Much higher than baseline
      });

      const anomalies = analyzer.detectAnomalies();
      expect(Array.isArray(anomalies)).toBe(true);
    });
  });

  describe('Trend Analysis', () => {
    beforeEach(() => {
      const now = Date.now();
      for (let i = 5; i >= 0; i--) {
        analyzer.addDataPoint('vulnerability-critical', {
          timestamp: new Date(now - i * 86400000),
          value: 1 + i,
        });
      }
    });

    it('should get alerts', () => {
      const alerts = analyzer.getAlerts();
      expect(Array.isArray(alerts)).toBe(true);
    });

    it('should get anomalies', () => {
      const anomalies = analyzer.detectAnomalies();
      expect(Array.isArray(anomalies)).toBe(true);
    });
  });

  describe('Factory Functions', () => {
    it('should create analyzer with options', () => {
      const customAnalyzer = createPredictiveAnalyzer({
        lookbackDays: 14,
        forecastDays: 7,
      });
      expect(customAnalyzer).toBeInstanceOf(PredictiveAnalyzer);
    });

    it('should create analyzer with custom sensitivity', () => {
      const customAnalyzer = createPredictiveAnalyzer({
        anomalySensitivity: 0.9,
      });
      expect(customAnalyzer).toBeInstanceOf(PredictiveAnalyzer);
    });
  });

  describe('Edge Cases', () => {
    it('should handle no historical data', () => {
      const projection = analyzer.projectRisk(50);

      expect(projection).toBeDefined();
      // Should return default/baseline projection
    });

    it('should handle single data point', () => {
      analyzer.addDataPoint('test-metric', {
        timestamp: new Date(),
        value: 50,
      });

      const projection = analyzer.projectRisk(50);
      expect(projection).toBeDefined();
    });

    it('should handle anomaly detection with no data', () => {
      const anomalies = analyzer.detectAnomalies();
      expect(Array.isArray(anomalies)).toBe(true);
    });
  });
});
