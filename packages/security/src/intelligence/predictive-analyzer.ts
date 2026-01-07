/**
 * @fileoverview Predictive Security Analyzer
 * @module @nahisaho/musubix-security/intelligence/predictive-analyzer
 * 
 * Provides security prediction, anomaly forecasting, risk projection,
 * and proactive security recommendations.
 */

import type { VulnerabilityStats, SecurityMetric } from './security-analytics.js';
import type { ThreatContext } from './threat-intelligence.js';

// ============================================================================
// Types
// ============================================================================

/**
 * Prediction confidence level
 */
export type PredictionConfidence = 'high' | 'medium' | 'low' | 'uncertain';

/**
 * Risk projection
 */
export interface RiskProjection {
  /** Projection ID */
  id: string;
  /** Current risk score */
  currentRisk: number;
  /** Projected risk score */
  projectedRisk: number;
  /** Projection period (days) */
  periodDays: number;
  /** Change direction */
  direction: 'increasing' | 'decreasing' | 'stable';
  /** Change magnitude */
  magnitude: number;
  /** Confidence level */
  confidence: PredictionConfidence;
  /** Confidence score (0-1) */
  confidenceScore: number;
  /** Contributing factors */
  factors: {
    name: string;
    impact: number;
    description: string;
  }[];
  /** Recommendations */
  recommendations: string[];
  /** Projected at */
  projectedAt: Date;
}

/**
 * Vulnerability prediction
 */
export interface VulnerabilityPrediction {
  /** Prediction ID */
  id: string;
  /** Vulnerability type */
  type: string;
  /** Predicted count */
  predictedCount: number;
  /** Current count */
  currentCount: number;
  /** Change */
  change: number;
  /** Likelihood (0-1) */
  likelihood: number;
  /** Confidence */
  confidence: PredictionConfidence;
  /** Time frame (days) */
  timeFrame: number;
  /** Risk level if materialized */
  riskLevel: 'critical' | 'high' | 'medium' | 'low';
  /** Prevention strategies */
  preventionStrategies: string[];
}

/**
 * Security anomaly
 */
export interface SecurityAnomaly {
  /** Anomaly ID */
  id: string;
  /** Anomaly type */
  type: 'spike' | 'drop' | 'pattern-break' | 'unusual-activity';
  /** Metric affected */
  metric: string;
  /** Expected value */
  expectedValue: number;
  /** Actual value */
  actualValue: number;
  /** Deviation */
  deviation: number;
  /** Severity */
  severity: 'critical' | 'high' | 'medium' | 'low';
  /** Detection confidence */
  confidence: number;
  /** Detected at */
  detectedAt: Date;
  /** Possible causes */
  possibleCauses: string[];
  /** Recommended actions */
  recommendedActions: string[];
}

/**
 * Proactive alert
 */
export interface ProactiveAlert {
  /** Alert ID */
  id: string;
  /** Alert type */
  type: 'risk-increase' | 'vulnerability-surge' | 'pattern-detected' | 'threshold-breach';
  /** Alert title */
  title: string;
  /** Alert message */
  message: string;
  /** Severity */
  severity: 'critical' | 'high' | 'medium' | 'low';
  /** Confidence */
  confidence: PredictionConfidence;
  /** Time to impact (hours) */
  timeToImpact?: number;
  /** Recommended actions */
  actions: string[];
  /** Related predictions */
  relatedPredictions: string[];
  /** Created at */
  createdAt: Date;
}

/**
 * Security forecast
 */
export interface SecurityForecast {
  /** Forecast ID */
  id: string;
  /** Forecast period */
  period: {
    start: Date;
    end: Date;
  };
  /** Risk projections */
  riskProjections: RiskProjection[];
  /** Vulnerability predictions */
  vulnerabilityPredictions: VulnerabilityPrediction[];
  /** Expected trends */
  expectedTrends: {
    metric: string;
    direction: 'up' | 'down' | 'stable';
    magnitude: number;
    confidence: number;
  }[];
  /** Key risks */
  keyRisks: string[];
  /** Opportunities */
  opportunities: string[];
  /** Recommendations */
  recommendations: string[];
  /** Generated at */
  generatedAt: Date;
}

/**
 * Historical data point
 */
export interface HistoricalDataPoint {
  timestamp: Date;
  value: number;
  metadata?: Record<string, unknown>;
}

/**
 * Predictive Analyzer options
 */
export interface PredictiveAnalyzerOptions {
  /** Historical data lookback (days) */
  lookbackDays?: number;
  /** Forecast horizon (days) */
  forecastDays?: number;
  /** Anomaly detection sensitivity (0-1) */
  anomalySensitivity?: number;
  /** Alert thresholds */
  alertThresholds?: {
    riskIncrease: number;
    vulnerabilitySurge: number;
    deviationPercent: number;
  };
  /** Enable proactive alerts */
  enableProactiveAlerts?: boolean;
}

// ============================================================================
// PredictiveAnalyzer Class
// ============================================================================

/**
 * Predictive Security Analyzer
 */
export class PredictiveAnalyzer {
  private options: Required<PredictiveAnalyzerOptions>;
  private historicalData: Map<string, HistoricalDataPoint[]> = new Map();
  private alerts: ProactiveAlert[] = [];
  private anomalies: SecurityAnomaly[] = [];

  constructor(options: PredictiveAnalyzerOptions = {}) {
    this.options = {
      lookbackDays: options.lookbackDays ?? 30,
      forecastDays: options.forecastDays ?? 14,
      anomalySensitivity: options.anomalySensitivity ?? 0.7,
      alertThresholds: options.alertThresholds ?? {
        riskIncrease: 20,
        vulnerabilitySurge: 50,
        deviationPercent: 30,
      },
      enableProactiveAlerts: options.enableProactiveAlerts ?? true,
    };
  }

  /**
   * Add historical data point
   */
  addDataPoint(metric: string, dataPoint: HistoricalDataPoint): void {
    if (!this.historicalData.has(metric)) {
      this.historicalData.set(metric, []);
    }
    this.historicalData.get(metric)!.push(dataPoint);

    // Keep only data within lookback period
    this.pruneOldData(metric);
  }

  /**
   * Add multiple historical data points
   */
  addDataPoints(metric: string, dataPoints: HistoricalDataPoint[]): void {
    for (const point of dataPoints) {
      this.addDataPoint(metric, point);
    }
  }

  /**
   * Prune old data
   */
  private pruneOldData(metric: string): void {
    const cutoff = new Date();
    cutoff.setDate(cutoff.getDate() - this.options.lookbackDays);

    const data = this.historicalData.get(metric);
    if (data) {
      this.historicalData.set(
        metric,
        data.filter(d => d.timestamp >= cutoff)
      );
    }
  }

  /**
   * Import data from metrics
   */
  importFromMetrics(metrics: SecurityMetric[]): void {
    for (const metric of metrics) {
      this.addDataPoint(metric.type, {
        timestamp: metric.timestamp,
        value: metric.value,
        metadata: { breakdown: metric.breakdown },
      });
    }
  }

  /**
   * Import data from vulnerability stats
   */
  importFromVulnStats(stats: VulnerabilityStats, timestamp: Date = new Date()): void {
    this.addDataPoint('vulnerability-total', { timestamp, value: stats.total });
    this.addDataPoint('vulnerability-critical', { timestamp, value: stats.bySeverity.critical });
    this.addDataPoint('vulnerability-high', { timestamp, value: stats.bySeverity.high });
    this.addDataPoint('vulnerability-medium', { timestamp, value: stats.bySeverity.medium });
    this.addDataPoint('vulnerability-low', { timestamp, value: stats.bySeverity.low });
    this.addDataPoint('vulnerability-new', { timestamp, value: stats.newInPeriod });
    this.addDataPoint('vulnerability-fixed', { timestamp, value: stats.fixedInPeriod });
  }

  /**
   * Project future risk
   */
  projectRisk(
    currentRiskScore: number,
    threatContext?: ThreatContext
  ): RiskProjection {
    const riskData = this.historicalData.get('average-risk-score') ?? [];
    const projection = this.forecastValue(riskData, this.options.forecastDays);

    let projectedRisk = projection.value;
    const factors: RiskProjection['factors'] = [];

    // Adjust based on trend
    if (projection.trend === 'increasing') {
      factors.push({
        name: 'Historical Trend',
        impact: projection.magnitude * 10,
        description: 'Risk has been increasing based on historical data',
      });
    } else if (projection.trend === 'decreasing') {
      factors.push({
        name: 'Historical Trend',
        impact: -projection.magnitude * 10,
        description: 'Risk has been decreasing based on historical data',
      });
    }

    // Adjust based on threat context
    if (threatContext?.activelyExploited) {
      projectedRisk *= 1.5;
      factors.push({
        name: 'Active Exploitation',
        impact: 50,
        description: 'Vulnerabilities are actively being exploited in the wild',
      });
    }

    if (threatContext?.urgency === 'immediate') {
      projectedRisk *= 1.25;
      factors.push({
        name: 'Urgent Threat',
        impact: 25,
        description: 'Immediate remediation urgency indicated',
      });
    }

    // Adjust based on vulnerability trends
    const vulnData = this.historicalData.get('vulnerability-total') ?? [];
    const vulnProjection = this.forecastValue(vulnData, this.options.forecastDays);
    if (vulnProjection.trend === 'increasing') {
      projectedRisk += vulnProjection.magnitude * 5;
      factors.push({
        name: 'Vulnerability Growth',
        impact: vulnProjection.magnitude * 5,
        description: 'Vulnerabilities are expected to increase',
      });
    }

    // Cap risk at 100
    projectedRisk = Math.min(100, Math.max(0, projectedRisk));

    const change = projectedRisk - currentRiskScore;
    const direction: RiskProjection['direction'] = 
      change > 5 ? 'increasing' : change < -5 ? 'decreasing' : 'stable';

    const confidence = this.calculateConfidence(riskData.length, projection.confidence);
    const recommendations = this.generateRiskRecommendations(projectedRisk, factors);

    // Create proactive alert if risk is increasing significantly
    if (this.options.enableProactiveAlerts && change > this.options.alertThresholds.riskIncrease) {
      this.createAlert({
        type: 'risk-increase',
        title: 'Risk Increase Projected',
        message: `Risk is projected to increase from ${currentRiskScore} to ${Math.round(projectedRisk)} over the next ${this.options.forecastDays} days`,
        severity: projectedRisk > 80 ? 'critical' : projectedRisk > 60 ? 'high' : 'medium',
        actions: recommendations,
      });
    }

    return {
      id: `PROJ-${Date.now()}`,
      currentRisk: currentRiskScore,
      projectedRisk: Math.round(projectedRisk),
      periodDays: this.options.forecastDays,
      direction,
      magnitude: Math.abs(change),
      confidence,
      confidenceScore: projection.confidence,
      factors,
      recommendations,
      projectedAt: new Date(),
    };
  }

  /**
   * Forecast a value using simple linear regression
   */
  private forecastValue(
    data: HistoricalDataPoint[],
    daysAhead: number
  ): {
    value: number;
    trend: 'increasing' | 'decreasing' | 'stable';
    magnitude: number;
    confidence: number;
  } {
    if (data.length < 2) {
      return {
        value: data[0]?.value ?? 0,
        trend: 'stable',
        magnitude: 0,
        confidence: 0.3,
      };
    }

    // Sort by timestamp
    const sorted = [...data].sort((a, b) => a.timestamp.getTime() - b.timestamp.getTime());

    // Calculate linear regression
    const n = sorted.length;
    let sumX = 0, sumY = 0, sumXY = 0, sumX2 = 0;

    for (let i = 0; i < n; i++) {
      sumX += i;
      sumY += sorted[i].value;
      sumXY += i * sorted[i].value;
      sumX2 += i * i;
    }

    const slope = (n * sumXY - sumX * sumY) / (n * sumX2 - sumX * sumX) || 0;
    const intercept = (sumY - slope * sumX) / n;

    // Forecast
    const forecastIndex = n + daysAhead;
    const forecastValue = intercept + slope * forecastIndex;

    // Determine trend
    let trend: 'increasing' | 'decreasing' | 'stable';
    if (Math.abs(slope) < 0.5) {
      trend = 'stable';
    } else if (slope > 0) {
      trend = 'increasing';
    } else {
      trend = 'decreasing';
    }

    // Calculate R-squared for confidence
    const yMean = sumY / n;
    let ssTotal = 0, ssResidual = 0;
    
    for (let i = 0; i < n; i++) {
      const predicted = intercept + slope * i;
      ssTotal += Math.pow(sorted[i].value - yMean, 2);
      ssResidual += Math.pow(sorted[i].value - predicted, 2);
    }

    const rSquared = ssTotal > 0 ? 1 - (ssResidual / ssTotal) : 0;

    return {
      value: forecastValue,
      trend,
      magnitude: Math.abs(slope) * daysAhead,
      confidence: Math.max(0.3, Math.min(0.95, rSquared)),
    };
  }

  /**
   * Calculate confidence level
   */
  private calculateConfidence(
    dataPoints: number,
    statisticalConfidence: number
  ): PredictionConfidence {
    // Adjust for data availability
    const dataFactor = Math.min(1, dataPoints / 20);
    const overallConfidence = statisticalConfidence * dataFactor;

    if (overallConfidence >= 0.8) return 'high';
    if (overallConfidence >= 0.6) return 'medium';
    if (overallConfidence >= 0.4) return 'low';
    return 'uncertain';
  }

  /**
   * Generate risk recommendations
   */
  private generateRiskRecommendations(
    projectedRisk: number,
    factors: RiskProjection['factors']
  ): string[] {
    const recommendations: string[] = [];

    if (projectedRisk >= 80) {
      recommendations.push('URGENT: Implement immediate risk mitigation measures');
      recommendations.push('Prioritize critical and high severity vulnerabilities');
      recommendations.push('Consider emergency patching procedures');
    } else if (projectedRisk >= 60) {
      recommendations.push('Accelerate vulnerability remediation efforts');
      recommendations.push('Review and update security controls');
      recommendations.push('Increase monitoring frequency');
    } else if (projectedRisk >= 40) {
      recommendations.push('Continue regular vulnerability management');
      recommendations.push('Monitor for emerging threats');
    }

    // Factor-specific recommendations
    for (const factor of factors) {
      if (factor.name === 'Active Exploitation') {
        recommendations.push('Deploy available patches immediately');
        recommendations.push('Implement compensating controls if patches unavailable');
      }
      if (factor.name === 'Vulnerability Growth') {
        recommendations.push('Investigate root cause of vulnerability increase');
        recommendations.push('Review development security practices');
      }
    }

    return recommendations;
  }

  /**
   * Predict vulnerabilities
   */
  predictVulnerabilities(): VulnerabilityPrediction[] {
    const predictions: VulnerabilityPrediction[] = [];

    // Get current counts
    const totalData = this.historicalData.get('vulnerability-total') ?? [];
    const criticalData = this.historicalData.get('vulnerability-critical') ?? [];
    const highData = this.historicalData.get('vulnerability-high') ?? [];
    const newData = this.historicalData.get('vulnerability-new') ?? [];

    // Predict total vulnerabilities
    const totalForecast = this.forecastValue(totalData, this.options.forecastDays);
    const currentTotal = totalData[totalData.length - 1]?.value ?? 0;
    const predictedTotal = Math.max(0, Math.round(totalForecast.value));

    predictions.push({
      id: `PRED-TOTAL-${Date.now()}`,
      type: 'all',
      predictedCount: predictedTotal,
      currentCount: currentTotal,
      change: predictedTotal - currentTotal,
      likelihood: totalForecast.confidence,
      confidence: this.calculateConfidence(totalData.length, totalForecast.confidence),
      timeFrame: this.options.forecastDays,
      riskLevel: predictedTotal > currentTotal * 1.5 ? 'high' : 'medium',
      preventionStrategies: this.getPreventionStrategies('all', totalForecast.trend),
    });

    // Predict critical vulnerabilities
    const criticalForecast = this.forecastValue(criticalData, this.options.forecastDays);
    const currentCritical = criticalData[criticalData.length - 1]?.value ?? 0;
    const predictedCritical = Math.max(0, Math.round(criticalForecast.value));

    if (predictedCritical > currentCritical) {
      predictions.push({
        id: `PRED-CRITICAL-${Date.now()}`,
        type: 'critical',
        predictedCount: predictedCritical,
        currentCount: currentCritical,
        change: predictedCritical - currentCritical,
        likelihood: criticalForecast.confidence,
        confidence: this.calculateConfidence(criticalData.length, criticalForecast.confidence),
        timeFrame: this.options.forecastDays,
        riskLevel: 'critical',
        preventionStrategies: this.getPreventionStrategies('critical', criticalForecast.trend),
      });

      // Create alert for critical vulnerability surge
      if (this.options.enableProactiveAlerts && predictedCritical > currentCritical * 1.5) {
        this.createAlert({
          type: 'vulnerability-surge',
          title: 'Critical Vulnerability Surge Predicted',
          message: `Critical vulnerabilities are expected to increase from ${currentCritical} to ${predictedCritical}`,
          severity: 'critical',
          actions: this.getPreventionStrategies('critical', 'increasing'),
        });
      }
    }

    // Predict high vulnerabilities
    const highForecast = this.forecastValue(highData, this.options.forecastDays);
    const currentHigh = highData[highData.length - 1]?.value ?? 0;
    const predictedHigh = Math.max(0, Math.round(highForecast.value));

    predictions.push({
      id: `PRED-HIGH-${Date.now()}`,
      type: 'high',
      predictedCount: predictedHigh,
      currentCount: currentHigh,
      change: predictedHigh - currentHigh,
      likelihood: highForecast.confidence,
      confidence: this.calculateConfidence(highData.length, highForecast.confidence),
      timeFrame: this.options.forecastDays,
      riskLevel: 'high',
      preventionStrategies: this.getPreventionStrategies('high', highForecast.trend),
    });

    // Predict new vulnerabilities per day
    const newForecast = this.forecastValue(newData, this.options.forecastDays);
    const currentNew = newData[newData.length - 1]?.value ?? 0;
    const predictedNew = Math.max(0, Math.round(newForecast.value));

    predictions.push({
      id: `PRED-NEW-${Date.now()}`,
      type: 'new-per-period',
      predictedCount: predictedNew,
      currentCount: currentNew,
      change: predictedNew - currentNew,
      likelihood: newForecast.confidence,
      confidence: this.calculateConfidence(newData.length, newForecast.confidence),
      timeFrame: this.options.forecastDays,
      riskLevel: predictedNew > currentNew * 2 ? 'high' : 'medium',
      preventionStrategies: this.getPreventionStrategies('new', newForecast.trend),
    });

    return predictions;
  }

  /**
   * Get prevention strategies
   */
  private getPreventionStrategies(
    type: string,
    trend: 'increasing' | 'decreasing' | 'stable'
  ): string[] {
    const strategies: string[] = [];

    if (trend === 'increasing') {
      strategies.push('Increase security code reviews');
      strategies.push('Implement additional security testing');
      strategies.push('Review and strengthen security training');
    }

    switch (type) {
      case 'critical':
        strategies.push('Prioritize critical vulnerability remediation');
        strategies.push('Implement emergency patching procedures');
        strategies.push('Deploy additional security monitoring');
        break;
      case 'high':
        strategies.push('Accelerate high-severity fix deployment');
        strategies.push('Review security architecture');
        break;
      case 'new':
        strategies.push('Strengthen input validation practices');
        strategies.push('Implement security linting in CI/CD');
        strategies.push('Conduct security awareness training');
        break;
      default:
        strategies.push('Continue regular security assessments');
        strategies.push('Maintain vulnerability management processes');
    }

    return strategies;
  }

  /**
   * Detect anomalies
   */
  detectAnomalies(): SecurityAnomaly[] {
    const detected: SecurityAnomaly[] = [];

    for (const [metric, data] of this.historicalData) {
      if (data.length < 5) continue; // Need minimum data

      const anomaly = this.detectMetricAnomaly(metric, data);
      if (anomaly) {
        detected.push(anomaly);
        this.anomalies.push(anomaly);
      }
    }

    return detected;
  }

  /**
   * Detect anomaly in a metric
   */
  private detectMetricAnomaly(
    metric: string,
    data: HistoricalDataPoint[]
  ): SecurityAnomaly | null {
    const sorted = [...data].sort((a, b) => a.timestamp.getTime() - b.timestamp.getTime());
    const values = sorted.map(d => d.value);

    // Calculate mean and standard deviation
    const mean = values.reduce((sum, v) => sum + v, 0) / values.length;
    const stdDev = Math.sqrt(
      values.reduce((sum, v) => sum + Math.pow(v - mean, 2), 0) / values.length
    );

    // Check latest value
    const latestValue = values[values.length - 1];
    const deviation = Math.abs(latestValue - mean);
    const zScore = stdDev > 0 ? deviation / stdDev : 0;

    // Anomaly threshold based on sensitivity
    const threshold = 2 + (1 - this.options.anomalySensitivity) * 2;

    if (zScore > threshold) {
      const type: SecurityAnomaly['type'] = latestValue > mean ? 'spike' : 'drop';
      const deviationPercent = (deviation / mean) * 100;

      // Determine severity
      let severity: SecurityAnomaly['severity'];
      if (zScore > 4) severity = 'critical';
      else if (zScore > 3) severity = 'high';
      else if (zScore > 2.5) severity = 'medium';
      else severity = 'low';

      // Create alert
      if (this.options.enableProactiveAlerts && deviationPercent > this.options.alertThresholds.deviationPercent) {
        this.createAlert({
          type: 'pattern-detected',
          title: `Anomaly Detected in ${metric}`,
          message: `${type === 'spike' ? 'Spike' : 'Drop'} of ${Math.round(deviationPercent)}% detected`,
          severity,
          actions: this.getAnomalyActions(type, metric),
        });
      }

      return {
        id: `ANOM-${Date.now()}`,
        type,
        metric,
        expectedValue: mean,
        actualValue: latestValue,
        deviation,
        severity,
        confidence: Math.min(0.95, zScore / 5),
        detectedAt: new Date(),
        possibleCauses: this.getPossibleCauses(type, metric),
        recommendedActions: this.getAnomalyActions(type, metric),
      };
    }

    return null;
  }

  /**
   * Get possible causes for anomaly
   */
  private getPossibleCauses(
    type: SecurityAnomaly['type'],
    metric: string
  ): string[] {
    const causes: string[] = [];

    if (type === 'spike') {
      causes.push('New vulnerability scanner rules');
      causes.push('Code deployment with security issues');
      causes.push('New dependencies with vulnerabilities');
      causes.push('Previously unreported issues discovered');
    } else if (type === 'drop') {
      causes.push('Successful remediation campaign');
      causes.push('False positives removed');
      causes.push('Code refactoring');
      causes.push('Data collection issues');
    }

    if (metric.includes('critical')) {
      causes.push('Zero-day vulnerability discovered');
      causes.push('Major security incident');
    }

    return causes;
  }

  /**
   * Get recommended actions for anomaly
   */
  private getAnomalyActions(
    type: SecurityAnomaly['type'],
    metric: string
  ): string[] {
    const actions: string[] = [];

    actions.push('Investigate the root cause');

    if (type === 'spike') {
      actions.push('Review recent changes and deployments');
      actions.push('Verify scanner accuracy');
      actions.push('Prioritize triage of new findings');
    } else if (type === 'drop') {
      actions.push('Verify data collection is functioning');
      actions.push('Confirm remediation activities');
      actions.push('Review for configuration issues');
    }

    if (metric.includes('critical') || metric.includes('high')) {
      actions.push('Escalate to security team');
      actions.push('Conduct emergency review');
    }

    return actions;
  }

  /**
   * Create proactive alert
   */
  private createAlert(params: {
    type: ProactiveAlert['type'];
    title: string;
    message: string;
    severity: ProactiveAlert['severity'];
    actions: string[];
    timeToImpact?: number;
  }): ProactiveAlert {
    const alert: ProactiveAlert = {
      id: `ALERT-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`,
      type: params.type,
      title: params.title,
      message: params.message,
      severity: params.severity,
      confidence: 'medium',
      timeToImpact: params.timeToImpact,
      actions: params.actions,
      relatedPredictions: [],
      createdAt: new Date(),
    };

    this.alerts.push(alert);
    return alert;
  }

  /**
   * Get all alerts
   */
  getAlerts(): ProactiveAlert[] {
    return [...this.alerts];
  }

  /**
   * Get alerts by severity
   */
  getAlertsBySeverity(severity: ProactiveAlert['severity']): ProactiveAlert[] {
    return this.alerts.filter(a => a.severity === severity);
  }

  /**
   * Clear old alerts
   */
  clearOldAlerts(maxAgeDays: number = 7): number {
    const cutoff = new Date();
    cutoff.setDate(cutoff.getDate() - maxAgeDays);

    const before = this.alerts.length;
    this.alerts = this.alerts.filter(a => a.createdAt >= cutoff);

    return before - this.alerts.length;
  }

  /**
   * Generate security forecast
   */
  generateForecast(): SecurityForecast {
    const now = new Date();
    const endDate = new Date(now);
    endDate.setDate(endDate.getDate() + this.options.forecastDays);

    // Get projections
    const currentRisk = this.historicalData.get('average-risk-score');
    const latestRisk = currentRisk?.[currentRisk.length - 1]?.value ?? 50;
    const riskProjection = this.projectRisk(latestRisk);

    // Get vulnerability predictions
    const vulnPredictions = this.predictVulnerabilities();

    // Detect anomalies
    this.detectAnomalies();

    // Calculate expected trends
    const expectedTrends: SecurityForecast['expectedTrends'] = [];

    for (const [metric, data] of this.historicalData) {
      const forecast = this.forecastValue(data, this.options.forecastDays);
      expectedTrends.push({
        metric,
        direction: forecast.trend === 'stable' ? 'stable' : forecast.trend === 'increasing' ? 'up' : 'down',
        magnitude: forecast.magnitude,
        confidence: forecast.confidence,
      });
    }

    // Identify key risks
    const keyRisks: string[] = [];
    if (riskProjection.direction === 'increasing') {
      keyRisks.push(`Risk projected to increase by ${Math.round(riskProjection.magnitude)} points`);
    }
    for (const pred of vulnPredictions.filter(p => p.riskLevel === 'critical' && p.change > 0)) {
      keyRisks.push(`${pred.type} vulnerabilities expected to increase`);
    }

    // Identify opportunities
    const opportunities: string[] = [];
    if (riskProjection.direction === 'decreasing') {
      opportunities.push('Risk is trending downward - maintain momentum');
    }
    const fixData = this.historicalData.get('vulnerability-fixed');
    if (fixData && fixData.length > 0) {
      const avgFixes = fixData.reduce((sum, d) => sum + d.value, 0) / fixData.length;
      if (avgFixes > 5) {
        opportunities.push(`Strong remediation velocity (${Math.round(avgFixes)} fixes/period)`);
      }
    }

    // Aggregate recommendations
    const recommendations = [
      ...riskProjection.recommendations.slice(0, 3),
      ...vulnPredictions.flatMap(p => p.preventionStrategies.slice(0, 2)),
    ].filter((rec, i, arr) => arr.indexOf(rec) === i).slice(0, 10);

    return {
      id: `FORECAST-${Date.now()}`,
      period: {
        start: now,
        end: endDate,
      },
      riskProjections: [riskProjection],
      vulnerabilityPredictions: vulnPredictions,
      expectedTrends,
      keyRisks,
      opportunities,
      recommendations,
      generatedAt: now,
    };
  }

  /**
   * Get statistics
   */
  getStatistics(): {
    dataPointsCount: number;
    metricsTracked: number;
    alertsCount: number;
    anomaliesCount: number;
    oldestData: Date | null;
    latestData: Date | null;
  } {
    let dataPointsCount = 0;
    let oldestData: Date | null = null;
    let latestData: Date | null = null;

    for (const data of this.historicalData.values()) {
      dataPointsCount += data.length;
      for (const point of data) {
        if (!oldestData || point.timestamp < oldestData) {
          oldestData = point.timestamp;
        }
        if (!latestData || point.timestamp > latestData) {
          latestData = point.timestamp;
        }
      }
    }

    return {
      dataPointsCount,
      metricsTracked: this.historicalData.size,
      alertsCount: this.alerts.length,
      anomaliesCount: this.anomalies.length,
      oldestData,
      latestData,
    };
  }

  /**
   * Get anomalies
   */
  getAnomalies(): SecurityAnomaly[] {
    return [...this.anomalies];
  }

  /**
   * Export data
   */
  exportData(): {
    historicalData: Record<string, HistoricalDataPoint[]>;
    alerts: ProactiveAlert[];
    anomalies: SecurityAnomaly[];
  } {
    return {
      historicalData: Object.fromEntries(this.historicalData),
      alerts: [...this.alerts],
      anomalies: [...this.anomalies],
    };
  }

  /**
   * Import data
   */
  importData(data: {
    historicalData?: Record<string, HistoricalDataPoint[]>;
    alerts?: ProactiveAlert[];
    anomalies?: SecurityAnomaly[];
  }): void {
    if (data.historicalData) {
      for (const [metric, points] of Object.entries(data.historicalData)) {
        this.historicalData.set(metric, points.map(p => ({
          ...p,
          timestamp: new Date(p.timestamp),
        })));
      }
    }

    if (data.alerts) {
      this.alerts = data.alerts.map(a => ({
        ...a,
        createdAt: new Date(a.createdAt),
      }));
    }

    if (data.anomalies) {
      this.anomalies = data.anomalies.map(a => ({
        ...a,
        detectedAt: new Date(a.detectedAt),
      }));
    }
  }
}

// ============================================================================
// Factory Functions
// ============================================================================

/**
 * Create a PredictiveAnalyzer instance
 */
export function createPredictiveAnalyzer(
  options?: PredictiveAnalyzerOptions
): PredictiveAnalyzer {
  return new PredictiveAnalyzer(options);
}

/**
 * Quick risk projection
 */
export function projectRisk(
  currentRisk: number,
  historicalData: HistoricalDataPoint[]
): RiskProjection {
  const analyzer = createPredictiveAnalyzer();
  analyzer.addDataPoints('average-risk-score', historicalData);
  return analyzer.projectRisk(currentRisk);
}

/**
 * Quick vulnerability prediction
 */
export function predictVulnerabilities(
  vulnStats: VulnerabilityStats[]
): VulnerabilityPrediction[] {
  const analyzer = createPredictiveAnalyzer();
  for (const stats of vulnStats) {
    analyzer.importFromVulnStats(stats);
  }
  return analyzer.predictVulnerabilities();
}

/**
 * Quick anomaly detection
 */
export function detectAnomalies(
  metrics: SecurityMetric[]
): SecurityAnomaly[] {
  const analyzer = createPredictiveAnalyzer();
  analyzer.importFromMetrics(metrics);
  return analyzer.detectAnomalies();
}
