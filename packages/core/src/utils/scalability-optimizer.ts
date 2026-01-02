/**
 * Scalability Optimizer
 * 
 * Optimizes system for scalability
 * 
 * @packageDocumentation
 * @module utils/scalability-optimizer
 * 
 * @see REQ-PER-002 - Scalability Optimization
 * @see Article IX - Continuous Adaptation
 */

/**
 * Resource type
 */
export type ResourceType = 'cpu' | 'memory' | 'io' | 'network' | 'storage';

/**
 * Scaling strategy
 */
export type ScalingStrategy = 'horizontal' | 'vertical' | 'hybrid' | 'none';

/**
 * Resource metrics
 */
export interface ResourceMetrics {
  /** Resource type */
  type: ResourceType;
  /** Current usage (0-1) */
  usage: number;
  /** Capacity */
  capacity: number;
  /** Available */
  available: number;
  /** Peak usage */
  peakUsage: number;
  /** Average usage */
  avgUsage: number;
}

/**
 * Load pattern
 */
export interface LoadPattern {
  /** Pattern name */
  name: string;
  /** Description */
  description: string;
  /** Average load */
  avgLoad: number;
  /** Peak load */
  peakLoad: number;
  /** Variance */
  variance: number;
  /** Predictable */
  predictable: boolean;
  /** Seasonal */
  seasonal: boolean;
}

/**
 * Bottleneck info
 */
export interface Bottleneck {
  /** Resource type */
  resource: ResourceType;
  /** Severity (0-1) */
  severity: number;
  /** Description */
  description: string;
  /** Impact */
  impact: string;
  /** Recommendation */
  recommendation: string;
}

/**
 * Scaling recommendation
 */
export interface ScalingRecommendation {
  /** Recommendation ID */
  id: string;
  /** Strategy */
  strategy: ScalingStrategy;
  /** Resource type */
  resource: ResourceType;
  /** Current capacity */
  currentCapacity: number;
  /** Recommended capacity */
  recommendedCapacity: number;
  /** Scale factor */
  scaleFactor: number;
  /** Priority */
  priority: 'high' | 'medium' | 'low';
  /** Rationale */
  rationale: string;
  /** Estimated cost impact */
  costImpact?: 'increase' | 'decrease' | 'neutral';
  /** Implementation steps */
  steps: string[];
}

/**
 * Optimization result
 */
export interface OptimizationResult {
  /** Timestamp */
  timestamp: Date;
  /** Metrics analyzed */
  metrics: ResourceMetrics[];
  /** Load pattern */
  loadPattern: LoadPattern;
  /** Bottlenecks found */
  bottlenecks: Bottleneck[];
  /** Recommendations */
  recommendations: ScalingRecommendation[];
  /** Overall score (0-100) */
  scalabilityScore: number;
  /** Summary */
  summary: string;
}

/**
 * Capacity plan
 */
export interface CapacityPlan {
  /** Plan ID */
  id: string;
  /** Name */
  name: string;
  /** Target date */
  targetDate: Date;
  /** Current capacity */
  current: Record<ResourceType, number>;
  /** Planned capacity */
  planned: Record<ResourceType, number>;
  /** Expected load */
  expectedLoad: number;
  /** Safety margin */
  safetyMargin: number;
  /** Cost estimate */
  costEstimate?: number;
}

/**
 * Scalability config
 */
export interface ScalabilityConfig {
  /** Target utilization (0-1) */
  targetUtilization: number;
  /** Safety margin (0-1) */
  safetyMargin: number;
  /** Scale up threshold */
  scaleUpThreshold: number;
  /** Scale down threshold */
  scaleDownThreshold: number;
  /** Min instances */
  minInstances: number;
  /** Max instances */
  maxInstances: number;
  /** Cooldown period (ms) */
  cooldownPeriod: number;
}

/**
 * Default configuration
 */
export const DEFAULT_SCALABILITY_CONFIG: ScalabilityConfig = {
  targetUtilization: 0.7,
  safetyMargin: 0.2,
  scaleUpThreshold: 0.8,
  scaleDownThreshold: 0.3,
  minInstances: 1,
  maxInstances: 10,
  cooldownPeriod: 300000, // 5 minutes
};

/**
 * Queue metrics
 */
export interface QueueMetrics {
  /** Queue name */
  name: string;
  /** Current length */
  length: number;
  /** Max length */
  maxLength: number;
  /** Processing rate */
  processingRate: number;
  /** Arrival rate */
  arrivalRate: number;
  /** Wait time (ms) */
  avgWaitTime: number;
}

/**
 * Throughput metrics
 */
export interface ThroughputMetrics {
  /** Requests per second */
  rps: number;
  /** Peak RPS */
  peakRps: number;
  /** Success rate */
  successRate: number;
  /** Error rate */
  errorRate: number;
  /** Latency p50 */
  latencyP50: number;
  /** Latency p99 */
  latencyP99: number;
}

/**
 * Scalability Optimizer
 */
export class ScalabilityOptimizer {
  private config: ScalabilityConfig;
  private metricsHistory: ResourceMetrics[][] = [];
  private loadHistory: number[] = [];
  private recommendationCounter = 0;

  constructor(config?: Partial<ScalabilityConfig>) {
    this.config = { ...DEFAULT_SCALABILITY_CONFIG, ...config };
  }

  /**
   * Analyze current metrics
   */
  analyze(metrics: ResourceMetrics[]): OptimizationResult {
    // Store metrics history
    this.metricsHistory.push(metrics);
    if (this.metricsHistory.length > 100) {
      this.metricsHistory.shift();
    }

    // Record load
    const totalLoad = metrics.reduce((sum, m) => sum + m.usage, 0) / metrics.length;
    this.loadHistory.push(totalLoad);
    if (this.loadHistory.length > 1000) {
      this.loadHistory.shift();
    }

    // Analyze load pattern
    const loadPattern = this.analyzeLoadPattern();

    // Find bottlenecks
    const bottlenecks = this.findBottlenecks(metrics);

    // Generate recommendations
    const recommendations = this.generateRecommendations(metrics, bottlenecks, loadPattern);

    // Calculate scalability score
    const scalabilityScore = this.calculateScalabilityScore(metrics, bottlenecks);

    // Generate summary
    const summary = this.generateSummary(scalabilityScore, bottlenecks, recommendations);

    return {
      timestamp: new Date(),
      metrics,
      loadPattern,
      bottlenecks,
      recommendations,
      scalabilityScore,
      summary,
    };
  }

  /**
   * Analyze load pattern
   */
  private analyzeLoadPattern(): LoadPattern {
    if (this.loadHistory.length < 10) {
      return {
        name: 'insufficient-data',
        description: 'Not enough data to determine pattern',
        avgLoad: this.loadHistory.length > 0 
          ? this.loadHistory.reduce((a, b) => a + b, 0) / this.loadHistory.length 
          : 0,
        peakLoad: Math.max(...this.loadHistory, 0),
        variance: 0,
        predictable: false,
        seasonal: false,
      };
    }

    const avgLoad = this.loadHistory.reduce((a, b) => a + b, 0) / this.loadHistory.length;
    const peakLoad = Math.max(...this.loadHistory);
    const variance = this.calculateVariance(this.loadHistory, avgLoad);
    
    // Determine predictability
    const predictable = variance < 0.1;
    
    // Check for seasonal patterns (simplified)
    const seasonal = this.detectSeasonality();

    let name = 'variable';
    let description = 'Load varies unpredictably';

    if (variance < 0.05) {
      name = 'steady';
      description = 'Load is consistent with minimal variation';
    } else if (variance < 0.15) {
      name = 'moderate';
      description = 'Load has moderate variation';
    } else if (peakLoad > avgLoad * 2) {
      name = 'spiky';
      description = 'Load has significant spikes';
    }

    if (seasonal) {
      name = 'seasonal-' + name;
      description += ' with seasonal patterns';
    }

    return {
      name,
      description,
      avgLoad,
      peakLoad,
      variance,
      predictable,
      seasonal,
    };
  }

  /**
   * Find bottlenecks
   */
  private findBottlenecks(metrics: ResourceMetrics[]): Bottleneck[] {
    const bottlenecks: Bottleneck[] = [];

    for (const metric of metrics) {
      if (metric.usage >= this.config.scaleUpThreshold) {
        const severity = Math.min(1, (metric.usage - this.config.scaleUpThreshold) / 
          (1 - this.config.scaleUpThreshold));

        bottlenecks.push({
          resource: metric.type,
          severity,
          description: `${metric.type} utilization at ${(metric.usage * 100).toFixed(1)}%`,
          impact: this.describeImpact(metric.type, severity),
          recommendation: this.getBottleneckRecommendation(metric.type, metric.usage),
        });
      }
    }

    // Sort by severity
    bottlenecks.sort((a, b) => b.severity - a.severity);

    return bottlenecks;
  }

  /**
   * Describe bottleneck impact
   */
  private describeImpact(resource: ResourceType, severity: number): string {
    const severityText = severity > 0.7 ? 'Critical' : severity > 0.4 ? 'Moderate' : 'Minor';

    switch (resource) {
      case 'cpu':
        return `${severityText} impact on processing speed and response times`;
      case 'memory':
        return `${severityText} risk of out-of-memory errors and degraded performance`;
      case 'io':
        return `${severityText} impact on data throughput and latency`;
      case 'network':
        return `${severityText} impact on network throughput and connection handling`;
      case 'storage':
        return `${severityText} risk of storage exhaustion and write failures`;
      default:
        return `${severityText} impact on system performance`;
    }
  }

  /**
   * Get bottleneck recommendation
   */
  private getBottleneckRecommendation(resource: ResourceType, usage: number): string {
    const strategy = usage > 0.9 ? 'immediately' : 'soon';

    switch (resource) {
      case 'cpu':
        return `Scale ${strategy} by adding more CPU cores or instances`;
      case 'memory':
        return `Increase memory allocation ${strategy} or optimize memory usage`;
      case 'io':
        return `Upgrade to faster storage or implement caching ${strategy}`;
      case 'network':
        return `Scale network capacity ${strategy} or implement load balancing`;
      case 'storage':
        return `Expand storage capacity ${strategy} or implement data archival`;
      default:
        return `Address resource constraint ${strategy}`;
    }
  }

  /**
   * Generate scaling recommendations
   */
  private generateRecommendations(
    metrics: ResourceMetrics[],
    _bottlenecks: Bottleneck[],
    loadPattern: LoadPattern
  ): ScalingRecommendation[] {
    const recommendations: ScalingRecommendation[] = [];

    // Check each resource
    for (const metric of metrics) {
      const recommendation = this.recommendForResource(metric, loadPattern);
      if (recommendation) {
        recommendations.push(recommendation);
      }
    }

    // Add pattern-based recommendations
    if (loadPattern.name.includes('spiky')) {
      recommendations.push({
        id: `rec-${++this.recommendationCounter}`,
        strategy: 'horizontal',
        resource: 'cpu',
        currentCapacity: 1,
        recommendedCapacity: 1,
        scaleFactor: 1,
        priority: 'medium',
        rationale: 'Spiky load pattern detected. Consider auto-scaling for better responsiveness.',
        costImpact: 'increase',
        steps: [
          'Implement auto-scaling policies',
          'Set scale-up threshold to 70%',
          'Set scale-down threshold to 30%',
          'Configure cooldown period',
        ],
      });
    }

    // Sort by priority
    const priorityOrder = { high: 0, medium: 1, low: 2 };
    recommendations.sort((a, b) => priorityOrder[a.priority] - priorityOrder[b.priority]);

    return recommendations;
  }

  /**
   * Recommend for specific resource
   */
  private recommendForResource(
    metric: ResourceMetrics,
    loadPattern: LoadPattern
  ): ScalingRecommendation | null {
    const { usage, capacity } = metric;

    // Scale up needed
    if (usage >= this.config.scaleUpThreshold) {
      const scaleFactor = this.calculateScaleFactor(usage, loadPattern.peakLoad);
      const newCapacity = Math.ceil(capacity * scaleFactor);

      return {
        id: `rec-${++this.recommendationCounter}`,
        strategy: this.determineStrategy(metric.type, scaleFactor),
        resource: metric.type,
        currentCapacity: capacity,
        recommendedCapacity: newCapacity,
        scaleFactor,
        priority: usage > 0.9 ? 'high' : 'medium',
        rationale: `${metric.type} utilization (${(usage * 100).toFixed(1)}%) exceeds threshold`,
        costImpact: 'increase',
        steps: this.getScaleUpSteps(metric.type, scaleFactor),
      };
    }

    // Scale down possible
    if (usage < this.config.scaleDownThreshold && capacity > this.config.minInstances) {
      const scaleFactor = this.config.targetUtilization / usage;
      const newCapacity = Math.max(this.config.minInstances, Math.floor(capacity / scaleFactor));

      if (newCapacity < capacity) {
        return {
          id: `rec-${++this.recommendationCounter}`,
          strategy: 'horizontal',
          resource: metric.type,
          currentCapacity: capacity,
          recommendedCapacity: newCapacity,
          scaleFactor: newCapacity / capacity,
          priority: 'low',
          rationale: `${metric.type} utilization (${(usage * 100).toFixed(1)}%) allows scaling down`,
          costImpact: 'decrease',
          steps: this.getScaleDownSteps(metric.type),
        };
      }
    }

    return null;
  }

  /**
   * Calculate scale factor
   */
  private calculateScaleFactor(currentUsage: number, peakUsage: number): number {
    const targetUsage = this.config.targetUtilization;
    const safetyMargin = this.config.safetyMargin;
    
    // Account for peak and add safety margin
    const effectiveTarget = Math.max(currentUsage, peakUsage) * (1 + safetyMargin);
    const factor = effectiveTarget / targetUsage;

    return Math.max(1.2, Math.min(factor, 3.0)); // Cap between 1.2x and 3x
  }

  /**
   * Determine scaling strategy
   */
  private determineStrategy(resource: ResourceType, scaleFactor: number): ScalingStrategy {
    if (scaleFactor > 2) {
      return 'hybrid';
    }

    switch (resource) {
      case 'cpu':
      case 'network':
        return 'horizontal';
      case 'memory':
      case 'storage':
        return scaleFactor > 1.5 ? 'horizontal' : 'vertical';
      case 'io':
        return 'vertical';
      default:
        return 'horizontal';
    }
  }

  /**
   * Get scale up steps
   */
  private getScaleUpSteps(resource: ResourceType, scaleFactor: number): string[] {
    const steps: string[] = [];

    switch (resource) {
      case 'cpu':
        if (scaleFactor > 1.5) {
          steps.push('Add additional instances to handle load');
          steps.push('Configure load balancer to distribute traffic');
        } else {
          steps.push('Increase CPU allocation per instance');
        }
        steps.push('Monitor performance after scaling');
        break;

      case 'memory':
        steps.push('Increase memory allocation');
        steps.push('Review memory usage patterns');
        steps.push('Consider caching strategies');
        break;

      case 'io':
        steps.push('Upgrade to faster storage tier');
        steps.push('Implement read caching');
        steps.push('Optimize database queries');
        break;

      case 'network':
        steps.push('Increase network bandwidth allocation');
        steps.push('Configure network load balancing');
        steps.push('Implement connection pooling');
        break;

      case 'storage':
        steps.push('Expand storage capacity');
        steps.push('Implement data lifecycle policies');
        steps.push('Consider data archival');
        break;
    }

    return steps;
  }

  /**
   * Get scale down steps
   */
  private getScaleDownSteps(resource: ResourceType): string[] {
    return [
      'Verify sustained low utilization (>15 minutes)',
      `Reduce ${resource} allocation gradually`,
      'Monitor for performance degradation',
      'Keep minimum capacity for reliability',
    ];
  }

  /**
   * Calculate scalability score
   */
  private calculateScalabilityScore(
    metrics: ResourceMetrics[],
    bottlenecks: Bottleneck[]
  ): number {
    let score = 100;

    // Deduct for bottlenecks
    for (const bottleneck of bottlenecks) {
      score -= bottleneck.severity * 20;
    }

    // Deduct for high utilization
    for (const metric of metrics) {
      if (metric.usage > 0.7) {
        score -= (metric.usage - 0.7) * 30;
      }
    }

    // Deduct for uneven distribution
    if (metrics.length > 1) {
      const usages = metrics.map((m) => m.usage);
      const variance = this.calculateVariance(usages, 
        usages.reduce((a, b) => a + b, 0) / usages.length);
      score -= variance * 20;
    }

    return Math.max(0, Math.min(100, score));
  }

  /**
   * Generate summary
   */
  private generateSummary(
    score: number,
    bottlenecks: Bottleneck[],
    recommendations: ScalingRecommendation[]
  ): string {
    const parts: string[] = [];

    // Score assessment
    if (score >= 80) {
      parts.push('System is well-scaled with good capacity margins.');
    } else if (score >= 60) {
      parts.push('System has moderate scalability with some areas for improvement.');
    } else if (score >= 40) {
      parts.push('System has scalability concerns that should be addressed.');
    } else {
      parts.push('System has critical scalability issues requiring immediate attention.');
    }

    // Bottlenecks
    if (bottlenecks.length > 0) {
      const critical = bottlenecks.filter((b) => b.severity > 0.7);
      if (critical.length > 0) {
        parts.push(`${critical.length} critical bottleneck(s) detected.`);
      }
    }

    // Recommendations
    const highPriority = recommendations.filter((r) => r.priority === 'high');
    if (highPriority.length > 0) {
      parts.push(`${highPriority.length} high-priority recommendation(s) available.`);
    }

    return parts.join(' ');
  }

  /**
   * Create capacity plan
   */
  createCapacityPlan(
    name: string,
    expectedLoadGrowth: number,
    targetDate: Date,
    currentMetrics: ResourceMetrics[]
  ): CapacityPlan {
    const current: Record<ResourceType, number> = {
      cpu: 0, memory: 0, io: 0, network: 0, storage: 0,
    };
    const planned: Record<ResourceType, number> = {
      cpu: 0, memory: 0, io: 0, network: 0, storage: 0,
    };

    for (const metric of currentMetrics) {
      current[metric.type] = metric.capacity;
      
      // Calculate needed capacity for expected load
      const currentLoad = metric.usage * metric.capacity;
      const expectedLoad = currentLoad * (1 + expectedLoadGrowth);
      const neededCapacity = expectedLoad / this.config.targetUtilization;
      
      // Add safety margin
      planned[metric.type] = Math.ceil(neededCapacity * (1 + this.config.safetyMargin));
    }

    return {
      id: `plan-${Date.now()}`,
      name,
      targetDate,
      current,
      planned,
      expectedLoad: 1 + expectedLoadGrowth,
      safetyMargin: this.config.safetyMargin,
    };
  }

  /**
   * Analyze queue metrics
   */
  analyzeQueue(queue: QueueMetrics): {
    healthy: boolean;
    recommendation: string;
  } {
    const utilizationRatio = queue.arrivalRate / queue.processingRate;
    
    if (utilizationRatio > 1) {
      return {
        healthy: false,
        recommendation: `Queue "${queue.name}" is growing. Increase processing capacity by ${((utilizationRatio - 1) * 100).toFixed(0)}%`,
      };
    }

    if (queue.length > queue.maxLength * 0.8) {
      return {
        healthy: false,
        recommendation: `Queue "${queue.name}" is near capacity. Consider increasing max length or processing rate`,
      };
    }

    if (queue.avgWaitTime > 1000) {
      return {
        healthy: false,
        recommendation: `Queue "${queue.name}" has high wait times. Add more consumers`,
      };
    }

    return {
      healthy: true,
      recommendation: `Queue "${queue.name}" is healthy`,
    };
  }

  /**
   * Analyze throughput
   */
  analyzeThroughput(throughput: ThroughputMetrics): {
    healthy: boolean;
    bottleneck?: string;
    recommendation: string;
  } {
    if (throughput.errorRate > 0.05) {
      return {
        healthy: false,
        bottleneck: 'error-rate',
        recommendation: 'High error rate detected. Investigate errors before scaling',
      };
    }

    if (throughput.latencyP99 > throughput.latencyP50 * 10) {
      return {
        healthy: false,
        bottleneck: 'latency-variance',
        recommendation: 'High latency variance. Check for slow queries or resource contention',
      };
    }

    if (throughput.rps < throughput.peakRps * 0.5) {
      return {
        healthy: true,
        recommendation: 'Throughput is below peak. Consider scaling down if sustained',
      };
    }

    return {
      healthy: true,
      recommendation: 'Throughput metrics are healthy',
    };
  }

  /**
   * Calculate variance
   */
  private calculateVariance(values: number[], mean: number): number {
    if (values.length === 0) return 0;
    const squaredDiffs = values.map((v) => Math.pow(v - mean, 2));
    return squaredDiffs.reduce((a, b) => a + b, 0) / values.length;
  }

  /**
   * Detect seasonality (simplified)
   */
  private detectSeasonality(): boolean {
    if (this.loadHistory.length < 100) return false;

    // Check for repeating patterns (very simplified)
    const windowSize = Math.floor(this.loadHistory.length / 4);
    const windows: number[][] = [];

    for (let i = 0; i < 4; i++) {
      const start = i * windowSize;
      windows.push(this.loadHistory.slice(start, start + windowSize));
    }

    // Compare pattern similarity between windows
    let similarCount = 0;
    for (let i = 1; i < windows.length; i++) {
      const correlation = this.calculateCorrelation(windows[0], windows[i]);
      if (correlation > 0.7) similarCount++;
    }

    return similarCount >= 2;
  }

  /**
   * Calculate correlation
   */
  private calculateCorrelation(a: number[], b: number[]): number {
    if (a.length !== b.length || a.length === 0) return 0;

    const meanA = a.reduce((s, v) => s + v, 0) / a.length;
    const meanB = b.reduce((s, v) => s + v, 0) / b.length;

    let numerator = 0;
    let denomA = 0;
    let denomB = 0;

    for (let i = 0; i < a.length; i++) {
      const diffA = a[i] - meanA;
      const diffB = b[i] - meanB;
      numerator += diffA * diffB;
      denomA += diffA * diffA;
      denomB += diffB * diffB;
    }

    const denominator = Math.sqrt(denomA * denomB);
    return denominator === 0 ? 0 : numerator / denominator;
  }

  /**
   * Format result as string
   */
  formatResult(result: OptimizationResult): string {
    const lines: string[] = [];

    lines.push('# Scalability Analysis Report');
    lines.push('');
    lines.push(`**Generated:** ${result.timestamp.toISOString()}`);
    lines.push(`**Scalability Score:** ${result.scalabilityScore.toFixed(0)}/100`);
    lines.push('');
    lines.push(`**Summary:** ${result.summary}`);
    lines.push('');

    // Load Pattern
    lines.push('## Load Pattern');
    lines.push('');
    lines.push(`- **Type:** ${result.loadPattern.name}`);
    lines.push(`- **Description:** ${result.loadPattern.description}`);
    lines.push(`- **Average Load:** ${(result.loadPattern.avgLoad * 100).toFixed(1)}%`);
    lines.push(`- **Peak Load:** ${(result.loadPattern.peakLoad * 100).toFixed(1)}%`);
    lines.push('');

    // Metrics
    lines.push('## Resource Metrics');
    lines.push('');
    lines.push('| Resource | Usage | Capacity | Status |');
    lines.push('|----------|-------|----------|--------|');
    for (const metric of result.metrics) {
      const status = metric.usage > 0.8 ? '🔴' : metric.usage > 0.6 ? '🟡' : '🟢';
      lines.push(`| ${metric.type} | ${(metric.usage * 100).toFixed(1)}% | ${metric.capacity} | ${status} |`);
    }
    lines.push('');

    // Bottlenecks
    if (result.bottlenecks.length > 0) {
      lines.push('## Bottlenecks');
      lines.push('');
      for (const bottleneck of result.bottlenecks) {
        lines.push(`### ${bottleneck.resource.toUpperCase()}`);
        lines.push(`- **Severity:** ${(bottleneck.severity * 100).toFixed(0)}%`);
        lines.push(`- **Description:** ${bottleneck.description}`);
        lines.push(`- **Impact:** ${bottleneck.impact}`);
        lines.push(`- **Recommendation:** ${bottleneck.recommendation}`);
        lines.push('');
      }
    }

    // Recommendations
    if (result.recommendations.length > 0) {
      lines.push('## Recommendations');
      lines.push('');
      for (const rec of result.recommendations) {
        const priority = rec.priority === 'high' ? '🔴' : rec.priority === 'medium' ? '🟡' : '🟢';
        lines.push(`### ${priority} ${rec.resource} - ${rec.strategy}`);
        lines.push(`- **Rationale:** ${rec.rationale}`);
        lines.push(`- **Scale Factor:** ${rec.scaleFactor.toFixed(2)}x`);
        lines.push(`- **Steps:**`);
        for (const step of rec.steps) {
          lines.push(`  1. ${step}`);
        }
        lines.push('');
      }
    }

    return lines.join('\n');
  }
}

/**
 * Create scalability optimizer instance
 */
export function createScalabilityOptimizer(
  config?: Partial<ScalabilityConfig>
): ScalabilityOptimizer {
  return new ScalabilityOptimizer(config);
}
