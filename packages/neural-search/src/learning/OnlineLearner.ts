/**
 * Online Learner
 * @module @nahisaho/musubix-neural-search
 * @description Online learning from search trajectories
 * Traces to: REQ-NS-004 (探索履歴学習)
 */

import type {
  IOnlineLearner,
  LearningStatistics,
  LearningUpdate,
  SearchTrajectory,
} from '../types.js';

/**
 * Online learner configuration
 */
export interface OnlineLearnerConfig {
  learningRate: number;
  momentumDecay: number;
  gradientClip: number;
}

/**
 * Default configuration
 */
const DEFAULT_CONFIG: OnlineLearnerConfig = {
  learningRate: 0.01,
  momentumDecay: 0.9,
  gradientClip: 1.0,
};

/**
 * Online learner implementation
 */
export class OnlineLearner implements IOnlineLearner {
  private readonly config: OnlineLearnerConfig;
  private parameters: Map<string, number>;
  private momentum: Map<string, number>;
  private totalUpdates: number;
  private lossHistory: number[];

  constructor(config: Partial<OnlineLearnerConfig> = {}) {
    this.config = { ...DEFAULT_CONFIG, ...config };
    this.parameters = new Map();
    this.momentum = new Map();
    this.totalUpdates = 0;
    this.lossHistory = [];

    // Initialize default parameters
    this.initializeParameters();
  }

  /**
   * Learn from a trajectory
   */
  learnFromTrajectory(trajectory: SearchTrajectory): LearningUpdate {
    const gradients = this.computeGradients(trajectory);
    const loss = this.computeLoss(trajectory);

    this.lossHistory.push(loss);
    this.totalUpdates++;

    return {
      trajectoryId: trajectory.id,
      gradients,
      loss,
    };
  }

  /**
   * Get current model parameters
   */
  getParameters(): Map<string, number> {
    return new Map(this.parameters);
  }

  /**
   * Apply learning update
   */
  applyUpdate(update: LearningUpdate): void {
    for (const [key, gradient] of update.gradients) {
      // Get current values
      const param = this.parameters.get(key) ?? 0;
      const mom = this.momentum.get(key) ?? 0;

      // Clip gradient
      const clippedGrad = Math.max(
        -this.config.gradientClip,
        Math.min(this.config.gradientClip, gradient)
      );

      // Update momentum
      const newMom = this.config.momentumDecay * mom + clippedGrad;
      this.momentum.set(key, newMom);

      // Update parameter
      const newParam = param - this.config.learningRate * newMom;
      this.parameters.set(key, newParam);
    }
  }

  /**
   * Get learning statistics
   */
  getStatistics(): LearningStatistics {
    const recentLoss = this.lossHistory.slice(-100);
    const avgLoss =
      recentLoss.length > 0
        ? recentLoss.reduce((a, b) => a + b, 0) / recentLoss.length
        : 0;

    // Compute convergence metric (variance of recent losses)
    const variance =
      recentLoss.length > 1
        ? recentLoss.reduce((sum, l) => sum + Math.pow(l - avgLoss, 2), 0) /
          (recentLoss.length - 1)
        : 1;

    return {
      totalUpdates: this.totalUpdates,
      averageLoss: avgLoss,
      learningRate: this.config.learningRate,
      convergenceMetric: 1 / (1 + variance), // Higher = more converged
    };
  }

  /**
   * Reset learner
   */
  reset(): void {
    this.initializeParameters();
    this.momentum.clear();
    this.totalUpdates = 0;
    this.lossHistory = [];
  }

  /**
   * Initialize default parameters
   */
  private initializeParameters(): void {
    this.parameters = new Map([
      ['specAlignment', 0.4],
      ['codeQuality', 0.3],
      ['novelty', 0.15],
      ['feasibility', 0.15],
      ['depthPenalty', 0.05],
      ['complexityPenalty', 0.1],
    ]);
  }

  /**
   * Compute gradients from trajectory
   */
  private computeGradients(trajectory: SearchTrajectory): Map<string, number> {
    const gradients = new Map<string, number>();
    const reward = trajectory.outcome.success ? 1 : -1;

    // Compute gradients based on trajectory outcome
    for (const step of trajectory.path) {
      // Positive gradient for parameters that led to success
      const specGrad = reward * 0.1 * (1 / (step.state.depth + 1));
      const qualityGrad = reward * 0.05;
      const noveltyGrad = reward * 0.02 * (step.score > 0.5 ? 1 : -1);

      // Accumulate gradients
      gradients.set(
        'specAlignment',
        (gradients.get('specAlignment') ?? 0) + specGrad
      );
      gradients.set(
        'codeQuality',
        (gradients.get('codeQuality') ?? 0) + qualityGrad
      );
      gradients.set('novelty', (gradients.get('novelty') ?? 0) + noveltyGrad);
    }

    // Normalize by path length
    const pathLength = trajectory.path.length || 1;
    for (const [key, value] of gradients) {
      gradients.set(key, value / pathLength);
    }

    return gradients;
  }

  /**
   * Compute loss from trajectory
   */
  private computeLoss(trajectory: SearchTrajectory): number {
    // Cross-entropy style loss
    // For success, we want high predicted score → low loss
    // For failure, we want high predicted score → high loss
    const target = trajectory.outcome.success ? 1 : 0;
    const predicted = trajectory.outcome.finalScore;

    // Clamp to avoid log(0)
    const p = Math.max(0.001, Math.min(0.999, predicted));

    // Cross-entropy: -[target * log(p) + (1-target) * log(1-p)]
    // If target=1 (success): loss = -log(p), so high p → low loss
    // If target=0 (failure): loss = -log(1-p), so high p → high loss
    const loss = -(target * Math.log(p) + (1 - target) * Math.log(1 - p));
    
    return loss;
  }
}
