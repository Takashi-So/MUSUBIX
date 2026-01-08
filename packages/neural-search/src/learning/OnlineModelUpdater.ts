/**
 * OnlineModelUpdater - Online Model Updates from Feedback
 * @module @nahisaho/musubix-neural-search
 * @see TSK-NS-104
 * @see DES-NS-104
 * @see REQ-NS-104 Online model updates within 3 feedback cycles
 */

// ============================================================================
// Types
// ============================================================================

/**
 * Feedback types
 */
export type FeedbackType = 'accept' | 'reject' | 'modify';

/**
 * OnlineModelUpdater configuration
 */
export interface OnlineModelUpdaterConfig {
  /** Number of feedbacks before update (default: 3) */
  updateThreshold: number;
  /** Learning rate for weight updates (default: 0.01) */
  learningRate: number;
  /** Auto-apply updates when threshold reached */
  autoApply: boolean;
}

/**
 * Feedback record
 */
export interface FeedbackRecord {
  /** Candidate ID that received feedback */
  candidateId: string;
  /** Feedback type */
  type: FeedbackType;
  /** Candidate score at time of feedback */
  score?: number;
  /** Reason for rejection/modification */
  reason?: string;
  /** Modification details */
  modification?: string;
  /** Additional context */
  context?: Record<string, unknown>;
}

/**
 * Feedback recording result
 */
export interface FeedbackResult {
  /** Success flag */
  success: boolean;
  /** Feedback ID */
  feedbackId: string;
  /** Error message if failed */
  error?: string;
}

/**
 * Update application result
 */
export interface UpdateResult {
  /** Whether updates were applied */
  applied: boolean;
  /** Number of updates applied */
  updatesApplied: number;
  /** New model version */
  modelVersion: number;
}

/**
 * Model weights
 */
export interface ModelWeights {
  /** Semantic similarity weight */
  semanticWeight: number;
  /** Context matching weight */
  contextWeight: number;
  /** Pattern matching weight */
  patternWeight: number;
  /** Recency weight */
  recencyWeight: number;
}

/**
 * Update statistics
 */
export interface UpdateStatistics {
  /** Total feedback received */
  totalFeedback: number;
  /** Accept count */
  acceptCount: number;
  /** Reject count */
  rejectCount: number;
  /** Modify count */
  modifyCount: number;
  /** Acceptance rate */
  acceptanceRate: number;
  /** Total updates applied */
  totalUpdatesApplied: number;
}

/**
 * Internal feedback entry with timestamp
 */
interface FeedbackEntry extends FeedbackRecord {
  feedbackId: string;
  timestamp: Date;
}

/**
 * OnlineModelUpdater interface
 */
export interface OnlineModelUpdater {
  /**
   * Record feedback for a candidate
   */
  recordFeedback(feedback: FeedbackRecord): FeedbackResult;

  /**
   * Apply pending updates to model
   */
  applyUpdates(): Promise<UpdateResult>;

  /**
   * Get pending feedback count
   */
  getPendingCount(): number;

  /**
   * Get current model weights
   */
  getModelWeights(): ModelWeights;

  /**
   * Set model weights
   */
  setModelWeights(weights: Partial<ModelWeights>): void;

  /**
   * Get statistics
   */
  getStatistics(): UpdateStatistics;

  /**
   * Serialize to JSON
   */
  toJSON(): string;

  /**
   * Deserialize from JSON
   */
  fromJSON(json: string): void;
}

// ============================================================================
// Default Implementation
// ============================================================================

/**
 * Default OnlineModelUpdater implementation
 */
export class DefaultOnlineModelUpdater implements OnlineModelUpdater {
  private config: OnlineModelUpdaterConfig;
  private pendingFeedback: FeedbackEntry[];
  private weights: ModelWeights;
  private statistics: UpdateStatistics;
  private modelVersion: number;
  private feedbackCounter: number;

  constructor(config?: Partial<OnlineModelUpdaterConfig>) {
    this.config = {
      updateThreshold: config?.updateThreshold ?? 3,
      learningRate: config?.learningRate ?? 0.01,
      autoApply: config?.autoApply ?? false,
    };

    this.pendingFeedback = [];
    this.weights = {
      semanticWeight: 0.4,
      contextWeight: 0.3,
      patternWeight: 0.2,
      recencyWeight: 0.1,
    };

    this.statistics = {
      totalFeedback: 0,
      acceptCount: 0,
      rejectCount: 0,
      modifyCount: 0,
      acceptanceRate: 0,
      totalUpdatesApplied: 0,
    };

    this.modelVersion = 1;
    this.feedbackCounter = 0;
  }

  /**
   * Record feedback for a candidate
   */
  recordFeedback(feedback: FeedbackRecord): FeedbackResult {
    const feedbackId = `FB-${++this.feedbackCounter}-${Date.now()}`;

    const entry: FeedbackEntry = {
      ...feedback,
      feedbackId,
      timestamp: new Date(),
    };

    this.pendingFeedback.push(entry);
    this.updateStatistics(feedback.type);

    // Check for auto-apply
    if (
      this.config.autoApply &&
      this.pendingFeedback.length >= this.config.updateThreshold
    ) {
      void this.applyUpdates();
    }

    return {
      success: true,
      feedbackId,
    };
  }

  /**
   * Apply pending updates to model
   */
  async applyUpdates(): Promise<UpdateResult> {
    if (this.pendingFeedback.length < this.config.updateThreshold) {
      return {
        applied: false,
        updatesApplied: 0,
        modelVersion: this.modelVersion,
      };
    }

    // Analyze feedback patterns
    const analysis = this.analyzeFeedback();

    // Update weights based on feedback
    this.adjustWeights(analysis);

    // Clear pending feedback
    const updatesApplied = this.pendingFeedback.length;
    this.pendingFeedback = [];

    // Increment model version
    this.modelVersion++;
    this.statistics.totalUpdatesApplied++;

    return {
      applied: true,
      updatesApplied,
      modelVersion: this.modelVersion,
    };
  }

  /**
   * Analyze feedback patterns
   */
  private analyzeFeedback(): FeedbackAnalysis {
    const accepts = this.pendingFeedback.filter((f) => f.type === 'accept');
    const rejects = this.pendingFeedback.filter((f) => f.type === 'reject');

    // Calculate average score for accepts vs rejects
    const avgAcceptScore =
      accepts.length > 0
        ? accepts.reduce((sum, f) => sum + (f.score ?? 0.5), 0) / accepts.length
        : 0.5;

    const avgRejectScore =
      rejects.length > 0
        ? rejects.reduce((sum, f) => sum + (f.score ?? 0.5), 0) / rejects.length
        : 0.5;

    return {
      acceptRate: accepts.length / this.pendingFeedback.length,
      avgAcceptScore,
      avgRejectScore,
      scoreDelta: avgAcceptScore - avgRejectScore,
    };
  }

  /**
   * Adjust weights based on feedback analysis
   */
  private adjustWeights(analysis: FeedbackAnalysis): void {
    const lr = this.config.learningRate;

    // If high accept rate, slightly increase semantic weight
    if (analysis.acceptRate > 0.7) {
      this.weights.semanticWeight = Math.min(
        0.6,
        this.weights.semanticWeight + lr
      );
    }

    // If low accept rate, increase context weight
    if (analysis.acceptRate < 0.3) {
      this.weights.contextWeight = Math.min(
        0.5,
        this.weights.contextWeight + lr
      );
    }

    // Normalize weights to sum to 1
    this.normalizeWeights();
  }

  /**
   * Normalize weights to sum to 1
   */
  private normalizeWeights(): void {
    const total =
      this.weights.semanticWeight +
      this.weights.contextWeight +
      this.weights.patternWeight +
      this.weights.recencyWeight;

    if (total > 0) {
      this.weights.semanticWeight /= total;
      this.weights.contextWeight /= total;
      this.weights.patternWeight /= total;
      this.weights.recencyWeight /= total;
    }
  }

  /**
   * Update statistics
   */
  private updateStatistics(type: FeedbackType): void {
    this.statistics.totalFeedback++;

    switch (type) {
      case 'accept':
        this.statistics.acceptCount++;
        break;
      case 'reject':
        this.statistics.rejectCount++;
        break;
      case 'modify':
        this.statistics.modifyCount++;
        break;
    }

    // Update acceptance rate
    this.statistics.acceptanceRate =
      this.statistics.acceptCount / this.statistics.totalFeedback;
  }

  /**
   * Get pending feedback count
   */
  getPendingCount(): number {
    return this.pendingFeedback.length;
  }

  /**
   * Get current model weights
   */
  getModelWeights(): ModelWeights {
    return { ...this.weights };
  }

  /**
   * Set model weights
   */
  setModelWeights(weights: Partial<ModelWeights>): void {
    this.weights = { ...this.weights, ...weights };
    this.normalizeWeights();
  }

  /**
   * Get statistics
   */
  getStatistics(): UpdateStatistics {
    return { ...this.statistics };
  }

  /**
   * Serialize to JSON
   */
  toJSON(): string {
    return JSON.stringify({
      config: this.config,
      weights: this.weights,
      statistics: this.statistics,
      modelVersion: this.modelVersion,
    });
  }

  /**
   * Deserialize from JSON
   */
  fromJSON(json: string): void {
    const data = JSON.parse(json);

    if (data.config) {
      this.config = { ...this.config, ...data.config };
    }

    if (data.weights) {
      this.weights = { ...this.weights, ...data.weights };
    }

    if (data.statistics) {
      this.statistics = { ...this.statistics, ...data.statistics };
    }

    if (data.modelVersion) {
      this.modelVersion = data.modelVersion;
    }
  }
}

// ============================================================================
// Helper Types
// ============================================================================

interface FeedbackAnalysis {
  acceptRate: number;
  avgAcceptScore: number;
  avgRejectScore: number;
  scoreDelta: number;
}

// ============================================================================
// Factory Function
// ============================================================================

/**
 * Create an OnlineModelUpdater instance
 * @param config - Optional configuration
 * @returns OnlineModelUpdater instance
 */
export function createOnlineModelUpdater(
  config?: Partial<OnlineModelUpdaterConfig>
): OnlineModelUpdater {
  return new DefaultOnlineModelUpdater(config);
}
