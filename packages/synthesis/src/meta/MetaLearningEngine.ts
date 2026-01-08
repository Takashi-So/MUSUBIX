/**
 * MetaLearningEngine
 * @module @nahisaho/musubix-synthesis
 * @description Meta-learning engine for synthesis optimization
 * Traces to: TSK-SY-103, DES-SY-103, REQ-SY-103
 */

/**
 * Task features extracted for similarity computation
 */
export interface TaskFeatures {
  inputType: string;
  outputType: string;
  complexity: number;
  domain: string;
}

/**
 * Synthesis strategy configuration
 */
export interface SynthesisStrategy {
  name: string;
  operators: string[];
  maxDepth: number;
}

/**
 * Synthesis task specification
 */
export interface SynthesisTask {
  inputs: unknown[];
  outputs: unknown[];
  domain: string;
}

/**
 * Recorded task with strategy and timing
 */
export interface RecordedTask {
  task: SynthesisTask;
  features: TaskFeatures;
  strategy: SynthesisStrategy;
  synthesisTime: number;
  timestamp: number;
}

/**
 * Similar task search result
 */
export interface SimilarTaskResult {
  task: SynthesisTask;
  similarity: number;
  strategy: SynthesisStrategy;
  synthesisTime: number;
}

/**
 * Meta-learning statistics
 */
export interface MetaLearningStatistics {
  totalTasks: number;
  averageSynthesisTime: number;
  domainDistribution: Record<string, number>;
  strategyEffectiveness: Record<string, number>;
}

/**
 * Configuration for meta-learning engine
 */
export interface MetaLearningConfig {
  similarityThreshold: number;
  maxTaskHistory: number;
  featureWeights: {
    inputType: number;
    outputType: number;
    complexity: number;
    domain: number;
  };
}

/**
 * Meta-learning engine interface
 */
export interface MetaLearningEngine {
  /**
   * Extract features from synthesis task
   */
  extractTaskFeatures(task: SynthesisTask): TaskFeatures;

  /**
   * Record completed task with strategy and timing
   */
  recordTask(
    task: SynthesisTask,
    strategy: SynthesisStrategy,
    synthesisTime: number
  ): void;

  /**
   * Find similar tasks from history
   */
  findSimilarTasks(task: SynthesisTask, maxResults?: number): SimilarTaskResult[];

  /**
   * Apply learned strategy to new task
   */
  applyStrategy(task: SynthesisTask): SynthesisStrategy | null;

  /**
   * Compute similarity between two task features
   */
  computeSimilarity(features1: TaskFeatures, features2: TaskFeatures): number;

  /**
   * Get meta-learning statistics
   */
  getStatistics(): MetaLearningStatistics;
}

/**
 * Default configuration
 */
const DEFAULT_CONFIG: MetaLearningConfig = {
  similarityThreshold: 0.6,
  maxTaskHistory: 100,
  featureWeights: {
    inputType: 0.25,
    outputType: 0.25,
    complexity: 0.2,
    domain: 0.3,
  },
};

/**
 * Default meta-learning engine implementation
 */
class DefaultMetaLearningEngine implements MetaLearningEngine {
  private readonly config: MetaLearningConfig;
  private readonly taskHistory: RecordedTask[];

  constructor(config: MetaLearningConfig = DEFAULT_CONFIG) {
    this.config = { ...DEFAULT_CONFIG, ...config };
    this.taskHistory = [];
  }

  extractTaskFeatures(task: SynthesisTask): TaskFeatures {
    const inputType = this.detectType(task.inputs[0]);
    const outputType = this.detectType(task.outputs[0]);
    const complexity = this.calculateComplexity(task);

    return {
      inputType,
      outputType,
      complexity,
      domain: task.domain,
    };
  }

  recordTask(
    task: SynthesisTask,
    strategy: SynthesisStrategy,
    synthesisTime: number
  ): void {
    const features = this.extractTaskFeatures(task);
    const recordedTask: RecordedTask = {
      task,
      features,
      strategy,
      synthesisTime,
      timestamp: Date.now(),
    };

    this.taskHistory.push(recordedTask);

    // Limit history size
    if (this.taskHistory.length > this.config.maxTaskHistory) {
      this.taskHistory.shift();
    }
  }

  findSimilarTasks(task: SynthesisTask, maxResults = 5): SimilarTaskResult[] {
    if (this.taskHistory.length === 0) {
      return [];
    }

    const taskFeatures = this.extractTaskFeatures(task);
    const similarTasks: SimilarTaskResult[] = [];

    for (const recorded of this.taskHistory) {
      const similarity = this.computeSimilarity(taskFeatures, recorded.features);

      if (similarity >= this.config.similarityThreshold) {
        similarTasks.push({
          task: recorded.task,
          similarity,
          strategy: recorded.strategy,
          synthesisTime: recorded.synthesisTime,
        });
      }
    }

    // Sort by similarity (descending)
    similarTasks.sort((a, b) => b.similarity - a.similarity);

    return similarTasks.slice(0, maxResults);
  }

  applyStrategy(task: SynthesisTask): SynthesisStrategy | null {
    const similarTasks = this.findSimilarTasks(task);

    if (similarTasks.length === 0) {
      return null;
    }

    // Merge strategies from similar tasks
    const operatorSet = new Set<string>();
    let totalDepth = 0;
    let minTime = Infinity;
    let bestStrategy = similarTasks[0].strategy;

    for (const similar of similarTasks) {
      for (const op of similar.strategy.operators) {
        operatorSet.add(op);
      }
      totalDepth += similar.strategy.maxDepth;

      // Track the fastest strategy
      if (similar.synthesisTime < minTime) {
        minTime = similar.synthesisTime;
        bestStrategy = similar.strategy;
      }
    }

    // Create optimized strategy based on fastest similar task
    return {
      name: bestStrategy.name,
      operators: Array.from(operatorSet),
      maxDepth: Math.min(bestStrategy.maxDepth, Math.ceil(totalDepth / similarTasks.length)),
    };
  }

  computeSimilarity(features1: TaskFeatures, features2: TaskFeatures): number {
    const weights = this.config.featureWeights;
    let similarity = 0;

    // Input type similarity
    if (features1.inputType === features2.inputType) {
      similarity += weights.inputType;
    }

    // Output type similarity
    if (features1.outputType === features2.outputType) {
      similarity += weights.outputType;
    }

    // Complexity similarity (inverse of difference)
    const complexityDiff = Math.abs(features1.complexity - features2.complexity);
    const complexitySim = 1 - complexityDiff;
    similarity += weights.complexity * complexitySim;

    // Domain similarity
    if (features1.domain === features2.domain) {
      similarity += weights.domain;
    }

    return similarity;
  }

  getStatistics(): MetaLearningStatistics {
    if (this.taskHistory.length === 0) {
      return {
        totalTasks: 0,
        averageSynthesisTime: 0,
        domainDistribution: {},
        strategyEffectiveness: {},
      };
    }

    // Calculate average synthesis time
    const totalTime = this.taskHistory.reduce((sum, t) => sum + t.synthesisTime, 0);
    const averageSynthesisTime = totalTime / this.taskHistory.length;

    // Calculate domain distribution
    const domainDistribution: Record<string, number> = {};
    for (const recorded of this.taskHistory) {
      const domain = recorded.features.domain;
      domainDistribution[domain] = (domainDistribution[domain] || 0) + 1;
    }

    // Calculate strategy effectiveness (average time per strategy)
    const strategyTimes: Record<string, number[]> = {};
    for (const recorded of this.taskHistory) {
      const strategyName = recorded.strategy.name;
      if (!strategyTimes[strategyName]) {
        strategyTimes[strategyName] = [];
      }
      strategyTimes[strategyName].push(recorded.synthesisTime);
    }

    const strategyEffectiveness: Record<string, number> = {};
    for (const [name, times] of Object.entries(strategyTimes)) {
      strategyEffectiveness[name] = times.reduce((a, b) => a + b, 0) / times.length;
    }

    return {
      totalTasks: this.taskHistory.length,
      averageSynthesisTime,
      domainDistribution,
      strategyEffectiveness,
    };
  }

  /**
   * Detect type of value
   */
  private detectType(value: unknown): string {
    if (value === null) return 'null';
    if (value === undefined) return 'undefined';
    if (Array.isArray(value)) return 'array';
    return typeof value;
  }

  /**
   * Calculate task complexity (0-1 scale)
   */
  private calculateComplexity(task: SynthesisTask): number {
    // Base complexity on example count and input diversity
    const exampleCount = task.inputs.length;

    // More examples = higher complexity (capped at 1.0)
    const countComplexity = Math.min(exampleCount / 10, 1.0);

    // Type diversity
    const inputTypes = new Set(task.inputs.map(i => this.detectType(i)));
    const typeComplexity = Math.min(inputTypes.size / 5, 1.0);

    return (countComplexity + typeComplexity) / 2;
  }
}

/**
 * Create meta-learning engine
 */
export function createMetaLearningEngine(
  config?: Partial<MetaLearningConfig>
): MetaLearningEngine {
  return new DefaultMetaLearningEngine(config as MetaLearningConfig);
}
