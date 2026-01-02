/**
 * Confidence Evaluator
 * 
 * Evaluates and combines confidence scores from multiple sources
 * 
 * @packageDocumentation
 * @module reasoning/confidence
 * 
 * @see REQ-INT-001 - Symbolic Reasoning
 * @see REQ-INT-003 - Confidence Scoring
 */

/**
 * Confidence source types
 */
export type ConfidenceSource =
  | 'neural'          // LLM-generated confidence
  | 'symbolic'        // Knowledge graph validation
  | 'pattern'         // Pattern matching
  | 'historical'      // Past performance
  | 'consensus'       // Multiple agent agreement
  | 'user-feedback';  // User corrections

/**
 * Confidence score with metadata
 */
export interface ConfidenceScore {
  /** Score value (0-1) */
  value: number;
  /** Source of the score */
  source: ConfidenceSource;
  /** Weight for combining */
  weight: number;
  /** Timestamp */
  timestamp: number;
  /** Additional metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Combined confidence result
 */
export interface CombinedConfidence {
  /** Final combined score */
  score: number;
  /** Individual scores */
  components: ConfidenceScore[];
  /** Combination method used */
  method: CombinationMethod;
  /** Explanation */
  explanation: string;
}

/**
 * Combination methods
 */
export type CombinationMethod =
  | 'weighted-average'
  | 'geometric-mean'
  | 'harmonic-mean'
  | 'minimum'
  | 'maximum'
  | 'bayesian';

/**
 * Evaluator configuration
 */
export interface ConfidenceEvaluatorConfig {
  /** Default combination method */
  defaultMethod: CombinationMethod;
  /** Default weights by source */
  defaultWeights: Partial<Record<ConfidenceSource, number>>;
  /** Minimum acceptable confidence */
  minimumThreshold: number;
  /** Enable confidence decay over time */
  enableDecay: boolean;
  /** Decay half-life in milliseconds */
  decayHalfLife: number;
}

/**
 * Default evaluator configuration
 */
export const DEFAULT_EVALUATOR_CONFIG: ConfidenceEvaluatorConfig = {
  defaultMethod: 'weighted-average',
  defaultWeights: {
    neural: 0.6,
    symbolic: 0.9,
    pattern: 0.8,
    historical: 0.7,
    consensus: 0.85,
    'user-feedback': 0.95,
  },
  minimumThreshold: 0.5,
  enableDecay: false,
  decayHalfLife: 86400000, // 24 hours
};

/**
 * Confidence calibration data
 */
export interface CalibrationData {
  /** Predicted confidence */
  predicted: number;
  /** Actual outcome (0 or 1) */
  actual: number;
  /** Timestamp */
  timestamp: number;
  /** Source */
  source: ConfidenceSource;
}

/**
 * Calibration statistics
 */
export interface CalibrationStats {
  /** Source */
  source: ConfidenceSource;
  /** Number of samples */
  sampleCount: number;
  /** Mean predicted confidence */
  meanPredicted: number;
  /** Actual success rate */
  actualRate: number;
  /** Calibration error */
  calibrationError: number;
  /** Brier score */
  brierScore: number;
}

/**
 * Confidence Evaluator
 * 
 * Evaluates, combines, and calibrates confidence scores
 */
export class ConfidenceEvaluator {
  private config: ConfidenceEvaluatorConfig;
  private calibrationHistory: CalibrationData[] = [];
  private calibrationStats: Map<ConfidenceSource, CalibrationStats> = new Map();

  constructor(config?: Partial<ConfidenceEvaluatorConfig>) {
    this.config = { ...DEFAULT_EVALUATOR_CONFIG, ...config };
  }

  /**
   * Create a confidence score
   */
  createScore(
    value: number,
    source: ConfidenceSource,
    metadata?: Record<string, unknown>
  ): ConfidenceScore {
    const weight = this.config.defaultWeights[source] ?? 0.5;

    return {
      value: this.clamp(value),
      source,
      weight,
      timestamp: Date.now(),
      metadata,
    };
  }

  /**
   * Combine multiple confidence scores
   */
  combine(
    scores: ConfidenceScore[],
    method?: CombinationMethod
  ): CombinedConfidence {
    const combinationMethod = method ?? this.config.defaultMethod;

    if (scores.length === 0) {
      return {
        score: 0,
        components: [],
        method: combinationMethod,
        explanation: 'No scores to combine',
      };
    }

    // Apply time decay if enabled
    const adjustedScores = this.config.enableDecay
      ? scores.map((s) => this.applyDecay(s))
      : scores;

    let combinedScore: number;

    switch (combinationMethod) {
      case 'weighted-average':
        combinedScore = this.weightedAverage(adjustedScores);
        break;

      case 'geometric-mean':
        combinedScore = this.geometricMean(adjustedScores);
        break;

      case 'harmonic-mean':
        combinedScore = this.harmonicMean(adjustedScores);
        break;

      case 'minimum':
        combinedScore = Math.min(...adjustedScores.map((s) => s.value));
        break;

      case 'maximum':
        combinedScore = Math.max(...adjustedScores.map((s) => s.value));
        break;

      case 'bayesian':
        combinedScore = this.bayesianCombine(adjustedScores);
        break;

      default:
        combinedScore = this.weightedAverage(adjustedScores);
    }

    return {
      score: this.clamp(combinedScore),
      components: adjustedScores,
      method: combinationMethod,
      explanation: this.generateExplanation(adjustedScores, combinedScore, combinationMethod),
    };
  }

  /**
   * Evaluate if confidence meets threshold
   */
  meetsThreshold(
    score: number | ConfidenceScore | CombinedConfidence,
    threshold?: number
  ): boolean {
    const minThreshold = threshold ?? this.config.minimumThreshold;
    const value = typeof score === 'number'
      ? score
      : 'score' in score
        ? score.score
        : score.value;

    return value >= minThreshold;
  }

  /**
   * Record outcome for calibration
   */
  recordOutcome(
    predicted: number,
    actual: boolean,
    source: ConfidenceSource
  ): void {
    this.calibrationHistory.push({
      predicted,
      actual: actual ? 1 : 0,
      timestamp: Date.now(),
      source,
    });

    // Update stats periodically
    if (this.calibrationHistory.length % 100 === 0) {
      this.updateCalibrationStats();
    }
  }

  /**
   * Get calibration statistics
   */
  getCalibrationStats(source?: ConfidenceSource): CalibrationStats[] {
    if (source) {
      const stats = this.calibrationStats.get(source);
      return stats ? [stats] : [];
    }
    return Array.from(this.calibrationStats.values());
  }

  /**
   * Calibrate a score based on historical performance
   */
  calibrate(score: ConfidenceScore): ConfidenceScore {
    const stats = this.calibrationStats.get(score.source);

    if (!stats || stats.sampleCount < 10) {
      return score; // Not enough data
    }

    // Apply calibration adjustment
    const calibrationFactor = stats.actualRate / stats.meanPredicted;
    const calibratedValue = this.clamp(score.value * calibrationFactor);

    return {
      ...score,
      value: calibratedValue,
      metadata: {
        ...score.metadata,
        calibrated: true,
        originalValue: score.value,
        calibrationFactor,
      },
    };
  }

  /**
   * Apply time decay to score
   */
  private applyDecay(score: ConfidenceScore): ConfidenceScore {
    const age = Date.now() - score.timestamp;
    const decayFactor = Math.pow(0.5, age / this.config.decayHalfLife);

    return {
      ...score,
      value: score.value * decayFactor,
      metadata: {
        ...score.metadata,
        decayed: true,
        originalValue: score.value,
        decayFactor,
      },
    };
  }

  /**
   * Weighted average combination
   */
  private weightedAverage(scores: ConfidenceScore[]): number {
    const totalWeight = scores.reduce((sum, s) => sum + s.weight, 0);
    if (totalWeight === 0) return 0;

    const weightedSum = scores.reduce(
      (sum, s) => sum + s.value * s.weight,
      0
    );

    return weightedSum / totalWeight;
  }

  /**
   * Geometric mean combination
   */
  private geometricMean(scores: ConfidenceScore[]): number {
    if (scores.some((s) => s.value === 0)) return 0;

    const product = scores.reduce((prod, s) => prod * s.value, 1);
    return Math.pow(product, 1 / scores.length);
  }

  /**
   * Harmonic mean combination
   */
  private harmonicMean(scores: ConfidenceScore[]): number {
    if (scores.some((s) => s.value === 0)) return 0;

    const sumReciprocals = scores.reduce((sum, s) => sum + 1 / s.value, 0);
    return scores.length / sumReciprocals;
  }

  /**
   * Bayesian combination
   */
  private bayesianCombine(scores: ConfidenceScore[]): number {
    // Convert confidences to odds, multiply, convert back
    let combinedOdds = 1;

    for (const score of scores) {
      // Avoid division by zero and log of zero
      const clamped = Math.max(0.001, Math.min(0.999, score.value));
      const odds = clamped / (1 - clamped);
      combinedOdds *= Math.pow(odds, score.weight);
    }

    // Convert back to probability
    return combinedOdds / (1 + combinedOdds);
  }

  /**
   * Update calibration statistics
   */
  private updateCalibrationStats(): void {
    const bySource = new Map<ConfidenceSource, CalibrationData[]>();

    for (const data of this.calibrationHistory) {
      const existing = bySource.get(data.source) ?? [];
      existing.push(data);
      bySource.set(data.source, existing);
    }

    for (const [source, data] of bySource) {
      const n = data.length;
      const meanPredicted = data.reduce((s, d) => s + d.predicted, 0) / n;
      const actualRate = data.reduce((s, d) => s + d.actual, 0) / n;
      const calibrationError = Math.abs(meanPredicted - actualRate);
      const brierScore = data.reduce(
        (s, d) => s + Math.pow(d.predicted - d.actual, 2),
        0
      ) / n;

      this.calibrationStats.set(source, {
        source,
        sampleCount: n,
        meanPredicted,
        actualRate,
        calibrationError,
        brierScore,
      });
    }
  }

  /**
   * Generate explanation for combination
   */
  private generateExplanation(
    scores: ConfidenceScore[],
    combined: number,
    method: CombinationMethod
  ): string {
    const sourceDescriptions = scores.map(
      (s) => `${s.source}: ${(s.value * 100).toFixed(1)}% (weight: ${s.weight})`
    );

    return [
      `Combined ${scores.length} confidence scores using ${method}.`,
      `Sources: ${sourceDescriptions.join(', ')}.`,
      `Result: ${(combined * 100).toFixed(1)}% confidence.`,
    ].join(' ');
  }

  /**
   * Clamp value to valid range
   */
  private clamp(value: number): number {
    return Math.max(0, Math.min(1, value));
  }
}

/**
 * Create confidence evaluator instance
 */
export function createConfidenceEvaluator(
  config?: Partial<ConfidenceEvaluatorConfig>
): ConfidenceEvaluator {
  return new ConfidenceEvaluator(config);
}

/**
 * Quick confidence combination helper
 */
export function combineConfidence(
  scores: Array<{ value: number; source: ConfidenceSource }>,
  method?: CombinationMethod
): number {
  const evaluator = new ConfidenceEvaluator();
  const fullScores = scores.map((s) =>
    evaluator.createScore(s.value, s.source)
  );
  return evaluator.combine(fullScores, method).score;
}
