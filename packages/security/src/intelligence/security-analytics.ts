/**
 * @fileoverview Security Analytics Engine
 * @module @nahisaho/musubix-security/intelligence/security-analytics
 *
 * Provides trend analysis, metrics collection, statistical reporting,
 * and security insights for comprehensive security management.
 *
 * NOTE: This analytics engine consumes vulnerability data from the security package's
 * scanners. Its severity-to-score mapping (critical=100, high=75, medium=50, low=25,
 * info=10) is specific to risk analytics and differs from the security score deduction
 * weights in core's SecurityScanner (which starts from 100 and deducts per finding).
 * These are distinct calculation models serving different purposes: this engine tracks
 * trends over time, while core's scanner produces a point-in-time quality score.
 */

import type { Vulnerability } from '../types/index.js';
import type { RiskSummary } from './risk-scorer.js';

// ============================================================================
// Types
// ============================================================================

/**
 * Time period for analytics
 */
export type TimePeriod = 'hour' | 'day' | 'week' | 'month' | 'quarter' | 'year';

/**
 * Security metric type
 */
export type MetricType =
  | 'vulnerability-count'
  | 'average-risk-score'
  | 'mean-time-to-remediate'
  | 'security-debt'
  | 'fix-rate'
  | 'detection-rate'
  | 'false-positive-rate'
  | 'coverage';

/**
 * Security metric
 */
export interface SecurityMetric {
  /** Metric type */
  type: MetricType;
  /** Metric value */
  value: number;
  /** Unit */
  unit: string;
  /** Timestamp */
  timestamp: Date;
  /** Period */
  period: TimePeriod;
  /** Change from previous period */
  change?: {
    value: number;
    percentage: number;
    direction: 'up' | 'down' | 'stable';
  };
  /** Breakdown by category */
  breakdown?: Record<string, number>;
}

/**
 * Security trend
 */
export interface SecurityTrend {
  /** Trend name */
  name: string;
  /** Metric type */
  metricType: MetricType;
  /** Data points */
  dataPoints: {
    timestamp: Date;
    value: number;
  }[];
  /** Trend direction */
  direction: 'improving' | 'declining' | 'stable';
  /** Trend strength (0-1) */
  strength: number;
  /** Forecast for next period */
  forecast?: number;
  /** Insights */
  insights: string[];
}

/**
 * Vulnerability statistics
 */
export interface VulnerabilityStats {
  /** Total count */
  total: number;
  /** By severity */
  bySeverity: {
    critical: number;
    high: number;
    medium: number;
    low: number;
    info: number;
  };
  /** By type */
  byType: Record<string, number>;
  /** By file */
  byFile: Record<string, number>;
  /** New vulnerabilities in period */
  newInPeriod: number;
  /** Fixed vulnerabilities in period */
  fixedInPeriod: number;
  /** Average age (days) */
  averageAge: number;
  /** Oldest vulnerability age (days) */
  oldestAge: number;
}

/**
 * Security score card
 */
export interface SecurityScorecard {
  /** Overall score (0-100) */
  overallScore: number;
  /** Grade (A-F) */
  grade: 'A' | 'B' | 'C' | 'D' | 'F';
  /** Category scores */
  categoryScores: {
    category: string;
    score: number;
    weight: number;
  }[];
  /** Key findings */
  keyFindings: string[];
  /** Improvement suggestions */
  improvements: string[];
  /** Comparison with industry */
  industryComparison?: {
    percentile: number;
    average: number;
  };
  /** Historical scores */
  history: {
    period: string;
    score: number;
  }[];
}

/**
 * Security dashboard data
 */
export interface SecurityDashboard {
  /** Summary */
  summary: {
    totalVulnerabilities: number;
    criticalCount: number;
    overallRisk: number;
    securityScore: number;
    trend: 'improving' | 'declining' | 'stable';
  };
  /** Recent activity */
  recentActivity: {
    timestamp: Date;
    type: 'vulnerability-found' | 'vulnerability-fixed' | 'scan-completed';
    description: string;
  }[];
  /** Top risks */
  topRisks: {
    vulnerability: Vulnerability;
    riskScore: number;
    daysOpen: number;
  }[];
  /** Metrics */
  metrics: SecurityMetric[];
  /** Trends */
  trends: SecurityTrend[];
  /** Scorecard */
  scorecard: SecurityScorecard;
  /** Generated at */
  generatedAt: Date;
}

/**
 * Analytics report
 */
export interface AnalyticsReport {
  /** Report ID */
  id: string;
  /** Report title */
  title: string;
  /** Period covered */
  period: {
    start: Date;
    end: Date;
  };
  /** Executive summary */
  executiveSummary: string;
  /** Key metrics */
  keyMetrics: SecurityMetric[];
  /** Trends */
  trends: SecurityTrend[];
  /** Vulnerability stats */
  vulnerabilityStats: VulnerabilityStats;
  /** Risk summary */
  riskSummary: RiskSummary;
  /** Recommendations */
  recommendations: {
    priority: 'high' | 'medium' | 'low';
    description: string;
    impact: string;
  }[];
  /** Generated at */
  generatedAt: Date;
}

/**
 * Analytics event
 */
export interface AnalyticsEvent {
  /** Event ID */
  id: string;
  /** Event type */
  type: 'scan' | 'vulnerability' | 'fix' | 'alert' | 'report';
  /** Timestamp */
  timestamp: Date;
  /** Data */
  data: Record<string, unknown>;
  /** Tags */
  tags: string[];
}

/**
 * Security Analytics options
 */
export interface SecurityAnalyticsOptions {
  /** Data retention period in days */
  retentionDays?: number;
  /** Enable real-time metrics */
  enableRealtime?: boolean;
  /** Industry benchmark data */
  industryBenchmark?: Record<MetricType, number>;
  /** Custom metric calculators */
  customMetrics?: Map<string, (events: AnalyticsEvent[]) => number>;
}

// ============================================================================
// SecurityAnalytics Class
// ============================================================================

/**
 * Security Analytics Engine
 */
export class SecurityAnalytics {
  private options: Required<SecurityAnalyticsOptions>;
  private events: AnalyticsEvent[] = [];
  private metricsHistory: Map<MetricType, SecurityMetric[]> = new Map();
  private vulnerabilityHistory: Map<string, { found: Date; fixed?: Date }> = new Map();

  constructor(options: SecurityAnalyticsOptions = {}) {
    this.options = {
      retentionDays: options.retentionDays ?? 90,
      enableRealtime: options.enableRealtime ?? true,
      industryBenchmark: options.industryBenchmark ?? {
        'vulnerability-count': 50,
        'average-risk-score': 45,
        'mean-time-to-remediate': 30,
        'security-debt': 100,
        'fix-rate': 70,
        'detection-rate': 85,
        'false-positive-rate': 15,
        'coverage': 80,
      },
      customMetrics: options.customMetrics ?? new Map(),
    };

    // Initialize metrics history
    const metricTypes: MetricType[] = [
      'vulnerability-count',
      'average-risk-score',
      'mean-time-to-remediate',
      'security-debt',
      'fix-rate',
      'detection-rate',
      'false-positive-rate',
      'coverage',
    ];
    for (const type of metricTypes) {
      this.metricsHistory.set(type, []);
    }
  }

  /**
   * Record an analytics event
   */
  recordEvent(event: Omit<AnalyticsEvent, 'id'>): void {
    const fullEvent: AnalyticsEvent = {
      id: `EVT-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`,
      ...event,
    };
    this.events.push(fullEvent);

    // Prune old events
    this.pruneOldEvents();
  }

  /**
   * Record vulnerability discovery
   */
  recordVulnerability(vulnerability: Vulnerability): void {
    this.vulnerabilityHistory.set(vulnerability.id, {
      found: new Date(),
    });

    this.recordEvent({
      type: 'vulnerability',
      timestamp: new Date(),
      data: {
        vulnerabilityId: vulnerability.id,
        type: vulnerability.type,
        severity: vulnerability.severity,
        file: vulnerability.location.file,
      },
      tags: ['discovery', vulnerability.severity, vulnerability.type],
    });
  }

  /**
   * Record vulnerability fix
   */
  recordFix(vulnerabilityId: string): void {
    const record = this.vulnerabilityHistory.get(vulnerabilityId);
    if (record) {
      record.fixed = new Date();
    }

    this.recordEvent({
      type: 'fix',
      timestamp: new Date(),
      data: { vulnerabilityId },
      tags: ['remediation'],
    });
  }

  /**
   * Record scan completion
   */
  recordScan(scanResults: {
    filesScanned: number;
    vulnerabilitiesFound: number;
    duration: number;
  }): void {
    this.recordEvent({
      type: 'scan',
      timestamp: new Date(),
      data: scanResults,
      tags: ['scan'],
    });
  }

  /**
   * Prune old events
   */
  private pruneOldEvents(): void {
    const cutoff = new Date();
    cutoff.setDate(cutoff.getDate() - this.options.retentionDays);
    
    this.events = this.events.filter(e => e.timestamp >= cutoff);
  }

  /**
   * Get events by type
   */
  getEventsByType(type: AnalyticsEvent['type'], since?: Date): AnalyticsEvent[] {
    return this.events.filter(e => 
      e.type === type && (!since || e.timestamp >= since)
    );
  }

  /**
   * Calculate metric for a period
   */
  calculateMetric(
    type: MetricType,
    period: TimePeriod = 'day'
  ): SecurityMetric {
    const now = new Date();
    const periodStart = this.getPeriodStart(now, period);
    const prevPeriodStart = this.getPreviousPeriodStart(periodStart, period);

    let value: number;
    let unit = '';
    const breakdown: Record<string, number> = {};

    const periodEvents = this.events.filter(e => e.timestamp >= periodStart);
    const prevPeriodEvents = this.events.filter(
      e => e.timestamp >= prevPeriodStart && e.timestamp < periodStart
    );

    switch (type) {
      case 'vulnerability-count': {
        value = periodEvents.filter(e => e.type === 'vulnerability').length;
        unit = 'count';
        // Breakdown by severity
        for (const event of periodEvents.filter(e => e.type === 'vulnerability')) {
          const severity = event.data.severity as string;
          breakdown[severity] = (breakdown[severity] || 0) + 1;
        }
        break;
      }

      case 'average-risk-score': {
        const vulnEvents = periodEvents.filter(e => e.type === 'vulnerability');
        value = vulnEvents.length > 0
          ? this.calculateAverageRisk(vulnEvents)
          : 0;
        unit = 'score';
        break;
      }

      case 'mean-time-to-remediate': {
        value = this.calculateMTTR();
        unit = 'days';
        break;
      }

      case 'security-debt': {
        value = this.calculateSecurityDebt();
        unit = 'hours';
        break;
      }

      case 'fix-rate': {
        const fixed = periodEvents.filter(e => e.type === 'fix').length;
        const found = periodEvents.filter(e => e.type === 'vulnerability').length;
        value = found > 0 ? Math.round((fixed / found) * 100) : 100;
        unit = '%';
        break;
      }

      case 'detection-rate': {
        // Simulated - would need baseline for real implementation
        value = 85;
        unit = '%';
        break;
      }

      case 'false-positive-rate': {
        // Simulated - would need feedback data
        value = 10;
        unit = '%';
        break;
      }

      case 'coverage': {
        const scans = periodEvents.filter(e => e.type === 'scan');
        value = scans.length > 0
          ? Math.round(scans.reduce((sum, e) => 
              sum + (e.data.filesScanned as number || 0), 0) / scans.length)
          : 0;
        unit = 'files';
        break;
      }

      default:
        value = 0;
        unit = '';
    }

    // Calculate change
    const prevValue = this.calculatePreviousPeriodValue(type, prevPeriodEvents);
    const changeValue = value - prevValue;
    const changePercentage = prevValue !== 0 
      ? Math.round((changeValue / prevValue) * 100) 
      : 0;

    const metric: SecurityMetric = {
      type,
      value,
      unit,
      timestamp: now,
      period,
      change: {
        value: changeValue,
        percentage: changePercentage,
        direction: changeValue > 0 ? 'up' : changeValue < 0 ? 'down' : 'stable',
      },
      breakdown: Object.keys(breakdown).length > 0 ? breakdown : undefined,
    };

    // Store in history
    this.metricsHistory.get(type)?.push(metric);

    return metric;
  }

  /**
   * Get period start date
   */
  private getPeriodStart(date: Date, period: TimePeriod): Date {
    const start = new Date(date);
    switch (period) {
      case 'hour':
        start.setMinutes(0, 0, 0);
        break;
      case 'day':
        start.setHours(0, 0, 0, 0);
        break;
      case 'week':
        start.setDate(start.getDate() - start.getDay());
        start.setHours(0, 0, 0, 0);
        break;
      case 'month':
        start.setDate(1);
        start.setHours(0, 0, 0, 0);
        break;
      case 'quarter':
        start.setMonth(Math.floor(start.getMonth() / 3) * 3, 1);
        start.setHours(0, 0, 0, 0);
        break;
      case 'year':
        start.setMonth(0, 1);
        start.setHours(0, 0, 0, 0);
        break;
    }
    return start;
  }

  /**
   * Get previous period start date
   */
  private getPreviousPeriodStart(currentStart: Date, period: TimePeriod): Date {
    const prev = new Date(currentStart);
    switch (period) {
      case 'hour':
        prev.setHours(prev.getHours() - 1);
        break;
      case 'day':
        prev.setDate(prev.getDate() - 1);
        break;
      case 'week':
        prev.setDate(prev.getDate() - 7);
        break;
      case 'month':
        prev.setMonth(prev.getMonth() - 1);
        break;
      case 'quarter':
        prev.setMonth(prev.getMonth() - 3);
        break;
      case 'year':
        prev.setFullYear(prev.getFullYear() - 1);
        break;
    }
    return prev;
  }

  /**
   * Calculate average risk from events
   */
  private calculateAverageRisk(events: AnalyticsEvent[]): number {
    const severityScores: Record<string, number> = {
      critical: 100,
      high: 75,
      medium: 50,
      low: 25,
      info: 10,
    };

    const total = events.reduce((sum, e) => {
      const severity = e.data.severity as string;
      return sum + (severityScores[severity] || 0);
    }, 0);

    return Math.round(total / events.length);
  }

  /**
   * Calculate previous period value
   */
  private calculatePreviousPeriodValue(
    type: MetricType,
    events: AnalyticsEvent[]
  ): number {
    switch (type) {
      case 'vulnerability-count':
        return events.filter(e => e.type === 'vulnerability').length;
      case 'average-risk-score':
        return this.calculateAverageRisk(events.filter(e => e.type === 'vulnerability'));
      case 'fix-rate': {
        const fixed = events.filter(e => e.type === 'fix').length;
        const found = events.filter(e => e.type === 'vulnerability').length;
        return found > 0 ? Math.round((fixed / found) * 100) : 100;
      }
      default:
        return 0;
    }
  }

  /**
   * Calculate mean time to remediate
   */
  private calculateMTTR(): number {
    const fixedVulns = Array.from(this.vulnerabilityHistory.entries())
      .filter(([, record]) => record.fixed);

    if (fixedVulns.length === 0) return 0;

    const totalDays = fixedVulns.reduce((sum, [, record]) => {
      const diffTime = (record.fixed!.getTime() - record.found.getTime());
      return sum + (diffTime / (1000 * 60 * 60 * 24));
    }, 0);

    return Math.round(totalDays / fixedVulns.length);
  }

  /**
   * Calculate security debt
   */
  private calculateSecurityDebt(): number {
    const openVulns = Array.from(this.vulnerabilityHistory.entries())
      .filter(([, record]) => !record.fixed);

    // Estimate hours to fix based on count (simplified)
    return openVulns.length * 4; // 4 hours per vulnerability average
  }

  /**
   * Calculate trend
   */
  calculateTrend(
    metricType: MetricType,
    dataPoints: number = 10
  ): SecurityTrend {
    const history = this.metricsHistory.get(metricType) || [];
    const recentHistory = history.slice(-dataPoints);

    const points = recentHistory.map(m => ({
      timestamp: m.timestamp,
      value: m.value,
    }));

    // Calculate trend direction using linear regression
    let direction: SecurityTrend['direction'] = 'stable';
    let strength = 0;
    let forecast: number | undefined;

    if (points.length >= 2) {
      const regression = this.linearRegression(points.map((p, i) => [i, p.value]));
      const slope = regression.slope;

      if (Math.abs(slope) < 0.5) {
        direction = 'stable';
      } else if (metricType === 'vulnerability-count' || metricType === 'average-risk-score') {
        // Lower is better for these metrics
        direction = slope < 0 ? 'improving' : 'declining';
      } else {
        // Higher is better for fix-rate, coverage, etc.
        direction = slope > 0 ? 'improving' : 'declining';
      }

      strength = Math.min(1, Math.abs(slope) / 10);
      forecast = Math.round(regression.intercept + regression.slope * points.length);
    }

    // Generate insights
    const insights = this.generateTrendInsights(metricType, direction, points);

    return {
      name: `${metricType} trend`,
      metricType,
      dataPoints: points,
      direction,
      strength,
      forecast,
      insights,
    };
  }

  /**
   * Simple linear regression
   */
  private linearRegression(points: number[][]): { slope: number; intercept: number } {
    const n = points.length;
    if (n === 0) return { slope: 0, intercept: 0 };

    let sumX = 0, sumY = 0, sumXY = 0, sumX2 = 0;

    for (const [x, y] of points) {
      sumX += x;
      sumY += y;
      sumXY += x * y;
      sumX2 += x * x;
    }

    const slope = (n * sumXY - sumX * sumY) / (n * sumX2 - sumX * sumX) || 0;
    const intercept = (sumY - slope * sumX) / n;

    return { slope, intercept };
  }

  /**
   * Generate trend insights
   */
  private generateTrendInsights(
    metricType: MetricType,
    direction: SecurityTrend['direction'],
    points: { timestamp: Date; value: number }[]
  ): string[] {
    const insights: string[] = [];
    const latest = points[points.length - 1]?.value ?? 0;
    const benchmark = this.options.industryBenchmark[metricType];

    // Direction insight
    if (direction === 'improving') {
      insights.push(`${metricType} is showing positive improvement`);
    } else if (direction === 'declining') {
      insights.push(`${metricType} trend is concerning and needs attention`);
    } else {
      insights.push(`${metricType} has remained stable`);
    }

    // Benchmark comparison
    if (benchmark) {
      if (metricType === 'vulnerability-count' || metricType === 'average-risk-score') {
        if (latest < benchmark) {
          insights.push(`Performance is better than industry average (${benchmark})`);
        } else if (latest > benchmark * 1.5) {
          insights.push(`Significantly above industry average of ${benchmark}`);
        }
      } else {
        if (latest > benchmark) {
          insights.push(`Exceeding industry benchmark of ${benchmark}`);
        } else if (latest < benchmark * 0.7) {
          insights.push(`Below industry benchmark of ${benchmark}`);
        }
      }
    }

    return insights;
  }

  /**
   * Get vulnerability statistics
   */
  getVulnerabilityStats(since?: Date): VulnerabilityStats {
    const vulnEvents = this.getEventsByType('vulnerability', since);
    const fixEvents = this.getEventsByType('fix', since);

    const bySeverity = {
      critical: 0,
      high: 0,
      medium: 0,
      low: 0,
      info: 0,
    };

    const byType: Record<string, number> = {};
    const byFile: Record<string, number> = {};

    for (const event of vulnEvents) {
      const severity = event.data.severity as string;
      const type = event.data.type as string;
      const file = event.data.file as string;

      if (severity in bySeverity) {
        bySeverity[severity as keyof typeof bySeverity]++;
      }
      byType[type] = (byType[type] || 0) + 1;
      byFile[file] = (byFile[file] || 0) + 1;
    }

    // Calculate ages
    const now = new Date();
    const openVulns = Array.from(this.vulnerabilityHistory.entries())
      .filter(([, record]) => !record.fixed);
    
    let totalAge = 0;
    let oldestAge = 0;

    for (const [, record] of openVulns) {
      const age = (now.getTime() - record.found.getTime()) / (1000 * 60 * 60 * 24);
      totalAge += age;
      oldestAge = Math.max(oldestAge, age);
    }

    return {
      total: vulnEvents.length,
      bySeverity,
      byType,
      byFile,
      newInPeriod: vulnEvents.length,
      fixedInPeriod: fixEvents.length,
      averageAge: openVulns.length > 0 ? Math.round(totalAge / openVulns.length) : 0,
      oldestAge: Math.round(oldestAge),
    };
  }

  /**
   * Generate security scorecard
   */
  generateScorecard(): SecurityScorecard {
    const categoryScores: SecurityScorecard['categoryScores'] = [];

    // Vulnerability Management Score
    const vulnCount = this.calculateMetric('vulnerability-count', 'month');
    const vulnScore = Math.max(0, 100 - vulnCount.value * 2);
    categoryScores.push({
      category: 'Vulnerability Management',
      score: vulnScore,
      weight: 0.3,
    });

    // Remediation Velocity Score
    const mttr = this.calculateMetric('mean-time-to-remediate', 'month');
    const remediationScore = Math.max(0, 100 - mttr.value * 3);
    categoryScores.push({
      category: 'Remediation Velocity',
      score: remediationScore,
      weight: 0.25,
    });

    // Fix Rate Score
    const fixRate = this.calculateMetric('fix-rate', 'month');
    categoryScores.push({
      category: 'Fix Rate',
      score: fixRate.value,
      weight: 0.25,
    });

    // Detection Coverage Score
    const coverage = this.calculateMetric('coverage', 'month');
    const coverageScore = Math.min(100, coverage.value);
    categoryScores.push({
      category: 'Detection Coverage',
      score: coverageScore,
      weight: 0.2,
    });

    // Calculate overall score
    const overallScore = Math.round(
      categoryScores.reduce((sum, cat) => sum + cat.score * cat.weight, 0)
    );

    // Determine grade
    const grade = this.scoreToGrade(overallScore);

    // Key findings
    const keyFindings: string[] = [];
    if (vulnCount.value > 10) {
      keyFindings.push(`${vulnCount.value} vulnerabilities found this month`);
    }
    if (mttr.value > 7) {
      keyFindings.push(`Average remediation time is ${mttr.value} days`);
    }

    // Improvements
    const improvements: string[] = [];
    for (const cat of categoryScores) {
      if (cat.score < 50) {
        improvements.push(`Improve ${cat.category} (current score: ${cat.score})`);
      }
    }

    // Industry comparison
    const industryComparison = {
      percentile: Math.round(overallScore * 0.9), // Simplified
      average: 55,
    };

    // Get historical scores
    const history = this.getHistoricalScores();

    return {
      overallScore,
      grade,
      categoryScores,
      keyFindings,
      improvements,
      industryComparison,
      history,
    };
  }

  /**
   * Convert score to grade
   */
  private scoreToGrade(score: number): SecurityScorecard['grade'] {
    if (score >= 90) return 'A';
    if (score >= 80) return 'B';
    if (score >= 70) return 'C';
    if (score >= 60) return 'D';
    return 'F';
  }

  /**
   * Get historical scores
   */
  private getHistoricalScores(): { period: string; score: number }[] {
    // Simplified - would aggregate from metricsHistory
    const history: { period: string; score: number }[] = [];
    const months = ['Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun'];
    
    for (let i = 0; i < months.length; i++) {
      history.push({
        period: months[i],
        score: Math.round(60 + Math.random() * 30),
      });
    }

    return history;
  }

  /**
   * Generate dashboard data
   */
  generateDashboard(): SecurityDashboard {
    const vulnStats = this.getVulnerabilityStats();
    const scorecard = this.generateScorecard();

    // Calculate metrics
    const metrics = [
      this.calculateMetric('vulnerability-count', 'day'),
      this.calculateMetric('average-risk-score', 'day'),
      this.calculateMetric('fix-rate', 'week'),
      this.calculateMetric('mean-time-to-remediate', 'month'),
    ];

    // Calculate trends
    const trends = [
      this.calculateTrend('vulnerability-count'),
      this.calculateTrend('average-risk-score'),
    ];

    // Get recent activity
    const recentActivity = this.events
      .slice(-10)
      .map(e => ({
        timestamp: e.timestamp,
        type: e.type as 'vulnerability-found' | 'vulnerability-fixed' | 'scan-completed',
        description: this.formatEventDescription(e),
      }));

    // Get top risks (simulated)
    const topRisks = this.getEventsByType('vulnerability')
      .filter(e => e.data.severity === 'critical' || e.data.severity === 'high')
      .slice(-5)
      .map(e => ({
        vulnerability: {
          id: e.data.vulnerabilityId as string,
          type: e.data.type as string,
          severity: e.data.severity as 'critical' | 'high',
          description: `${e.data.type} vulnerability`,
          recommendation: 'Review and fix the vulnerability',
          confidence: 0.9,
          ruleId: 'analytics',
          detectedAt: e.timestamp,
          message: `${e.data.type} vulnerability`,
          location: {
            file: e.data.file as string,
            startLine: 1,
            endLine: 1,
            startColumn: 0,
            endColumn: 0,
          },
          cwes: [],
          fix: { description: '', code: '' },
        } as Vulnerability,
        riskScore: e.data.severity === 'critical' ? 95 : 75,
        daysOpen: Math.round((new Date().getTime() - e.timestamp.getTime()) / (1000 * 60 * 60 * 24)),
      }));

    // Determine trend
    const vulnTrend = trends.find(t => t.metricType === 'vulnerability-count');
    const trend = vulnTrend?.direction || 'stable';

    return {
      summary: {
        totalVulnerabilities: vulnStats.total,
        criticalCount: vulnStats.bySeverity.critical,
        overallRisk: metrics.find(m => m.type === 'average-risk-score')?.value || 0,
        securityScore: scorecard.overallScore,
        trend,
      },
      recentActivity,
      topRisks,
      metrics,
      trends,
      scorecard,
      generatedAt: new Date(),
    };
  }

  /**
   * Format event description
   */
  private formatEventDescription(event: AnalyticsEvent): string {
    switch (event.type) {
      case 'vulnerability':
        return `Found ${event.data.severity} severity ${event.data.type} vulnerability`;
      case 'fix':
        return `Fixed vulnerability ${event.data.vulnerabilityId}`;
      case 'scan':
        return `Scan completed: ${event.data.filesScanned} files, ${event.data.vulnerabilitiesFound} issues`;
      default:
        return `Event: ${event.type}`;
    }
  }

  /**
   * Generate analytics report
   */
  generateReport(startDate: Date, endDate: Date): AnalyticsReport {
    const vulnStats = this.getVulnerabilityStats(startDate);
    const scorecard = this.generateScorecard();

    // Calculate key metrics for period
    const keyMetrics = [
      this.calculateMetric('vulnerability-count', 'month'),
      this.calculateMetric('average-risk-score', 'month'),
      this.calculateMetric('fix-rate', 'month'),
      this.calculateMetric('mean-time-to-remediate', 'month'),
      this.calculateMetric('security-debt', 'month'),
    ];

    // Generate executive summary
    const executiveSummary = this.generateExecutiveSummary(vulnStats, scorecard);

    // Generate recommendations
    const recommendations = this.generateReportRecommendations(vulnStats, scorecard);

    return {
      id: `RPT-${Date.now()}`,
      title: 'Security Analytics Report',
      period: { start: startDate, end: endDate },
      executiveSummary,
      keyMetrics,
      trends: [
        this.calculateTrend('vulnerability-count'),
        this.calculateTrend('average-risk-score'),
        this.calculateTrend('fix-rate'),
      ],
      vulnerabilityStats: vulnStats,
      riskSummary: {
        totalVulnerabilities: vulnStats.total,
        averageRiskScore: keyMetrics.find(m => m.type === 'average-risk-score')?.value || 0,
        distribution: {
          critical: vulnStats.bySeverity.critical,
          high: vulnStats.bySeverity.high,
          medium: vulnStats.bySeverity.medium,
          low: vulnStats.bySeverity.low,
          informational: vulnStats.bySeverity.info,
        },
        topRisks: [],
        totalBusinessImpact: [],
        securityPosture: scorecard.overallScore,
        trend: 'stable',
      },
      recommendations,
      generatedAt: new Date(),
    };
  }

  /**
   * Generate executive summary
   */
  private generateExecutiveSummary(
    stats: VulnerabilityStats,
    scorecard: SecurityScorecard
  ): string {
    const parts: string[] = [];

    parts.push(`Security Score: ${scorecard.overallScore}/100 (Grade: ${scorecard.grade})`);
    parts.push(`Total vulnerabilities identified: ${stats.total}`);
    parts.push(`Critical/High severity: ${stats.bySeverity.critical + stats.bySeverity.high}`);
    
    if (stats.fixedInPeriod > 0) {
      parts.push(`Vulnerabilities fixed this period: ${stats.fixedInPeriod}`);
    }

    if (stats.averageAge > 7) {
      parts.push(`Average vulnerability age: ${stats.averageAge} days (attention needed)`);
    }

    return parts.join('. ') + '.';
  }

  /**
   * Generate report recommendations
   */
  private generateReportRecommendations(
    stats: VulnerabilityStats,
    scorecard: SecurityScorecard
  ): AnalyticsReport['recommendations'] {
    const recommendations: AnalyticsReport['recommendations'] = [];

    if (stats.bySeverity.critical > 0) {
      recommendations.push({
        priority: 'high',
        description: `Address ${stats.bySeverity.critical} critical vulnerabilities immediately`,
        impact: 'Reduces critical risk exposure',
      });
    }

    if (stats.averageAge > 14) {
      recommendations.push({
        priority: 'high',
        description: 'Improve vulnerability remediation velocity',
        impact: 'Reduces exposure window',
      });
    }

    for (const cat of scorecard.categoryScores.filter(c => c.score < 60)) {
      recommendations.push({
        priority: cat.score < 40 ? 'high' : 'medium',
        description: `Improve ${cat.category}`,
        impact: `Current score: ${cat.score}/100`,
      });
    }

    if (recommendations.length === 0) {
      recommendations.push({
        priority: 'low',
        description: 'Continue current security practices',
        impact: 'Maintain security posture',
      });
    }

    return recommendations;
  }

  /**
   * Get all metrics
   */
  getAllMetrics(period: TimePeriod = 'day'): SecurityMetric[] {
    const metricTypes: MetricType[] = [
      'vulnerability-count',
      'average-risk-score',
      'mean-time-to-remediate',
      'security-debt',
      'fix-rate',
      'detection-rate',
      'false-positive-rate',
      'coverage',
    ];

    return metricTypes.map(type => this.calculateMetric(type, period));
  }

  /**
   * Export analytics data
   */
  exportData(): {
    events: AnalyticsEvent[];
    metricsHistory: Record<MetricType, SecurityMetric[]>;
    vulnerabilityHistory: Record<string, { found: Date; fixed?: Date }>;
  } {
    return {
      events: this.events,
      metricsHistory: Object.fromEntries(this.metricsHistory) as Record<MetricType, SecurityMetric[]>,
      vulnerabilityHistory: Object.fromEntries(this.vulnerabilityHistory),
    };
  }
}

// ============================================================================
// Factory Functions
// ============================================================================

/**
 * Create a SecurityAnalytics instance
 */
export function createSecurityAnalytics(
  options?: SecurityAnalyticsOptions
): SecurityAnalytics {
  return new SecurityAnalytics(options);
}

/**
 * Quick dashboard generation
 */
export function generateDashboard(events: AnalyticsEvent[]): SecurityDashboard {
  const analytics = createSecurityAnalytics();
  for (const event of events) {
    analytics.recordEvent(event);
  }
  return analytics.generateDashboard();
}
