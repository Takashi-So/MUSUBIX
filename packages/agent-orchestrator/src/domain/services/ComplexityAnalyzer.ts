/**
 * ComplexityAnalyzer Domain Service
 * 
 * Analyzes task complexity and recommends decomposition
 * 
 * @see REQ-SDD-001 - Task Complexity Evaluation
 * @see DES-SDD-001 - ComplexityAnalyzer
 */

import type { Task } from '../entities/Task.js';
import {
  type ComplexityScore,
  createComplexityScore,
  shouldDecompose as checkShouldDecompose,
} from '../value-objects/ComplexityScore.js';
import {
  type ComplexityFactor,
  type ComplexityFactorName,
  DEFAULT_FACTORS,
  createComplexityFactor,
  getWeightedScore,
} from '../value-objects/ComplexityFactor.js';

/**
 * Complexity analyzer interface
 */
export interface IComplexityAnalyzer {
  /**
   * Analyze task complexity
   * @param task - Task to analyze
   * @returns Complexity score
   */
  analyze(task: Task): ComplexityScore;

  /**
   * Check if task should be decomposed
   * @param score - Complexity score
   * @returns true if decomposition recommended
   */
  shouldDecompose(score: ComplexityScore): boolean;

  /**
   * Get decomposition recommendation
   * @param task - Task to analyze
   * @returns Recommendation with reasoning
   */
  getRecommendation(task: Task): DecompositionRecommendation;
}

/**
 * Decomposition recommendation
 */
export interface DecompositionRecommendation {
  /** Should decompose */
  readonly shouldDecompose: boolean;
  /** Complexity score */
  readonly score: ComplexityScore;
  /** Reasoning */
  readonly reasoning: string;
  /** Suggested subtask count */
  readonly suggestedSubtaskCount: number;
  /** Primary factors contributing to complexity */
  readonly primaryFactors: readonly ComplexityFactor[];
}

/**
 * Analyzer configuration
 */
export interface ComplexityAnalyzerConfig {
  /** Decomposition threshold (default: 7) */
  threshold?: number;
  /** Factor weight overrides */
  factorWeights?: Partial<Record<ComplexityFactorName, number>>;
}

/**
 * Create a complexity analyzer
 * 
 * @param config - Optional configuration
 * @returns IComplexityAnalyzer implementation
 */
export function createComplexityAnalyzer(
  config: ComplexityAnalyzerConfig = {}
): IComplexityAnalyzer {
  const threshold = config.threshold ?? 7;

  /**
   * Calculate factor score based on task properties
   */
  function calculateFactorScore(
    factorName: ComplexityFactorName,
    task: Task
  ): number {
    switch (factorName) {
      case 'scope':
        // Score based on estimated scope (1-10 components → 1-10 score)
        return Math.min(10, Math.max(1, task.estimatedScope));

      case 'dependencies':
        // Score based on dependency count (0-9+ → 1-10 score)
        return Math.min(10, Math.max(1, task.dependencyCount + 1));

      case 'fileCount':
        // Score based on estimated file count (1-10+ files → 1-10 score)
        return Math.min(10, Math.max(1, task.estimatedFileCount));

      case 'testCoverage':
        // Higher test requirement = higher complexity
        // 80% → 5, 90% → 7, 100% → 10
        return Math.min(10, Math.max(1, Math.floor(task.testCoverageRequired / 10)));

      case 'uncertainty':
        // Direct mapping of uncertainty level
        return Math.min(10, Math.max(1, task.uncertaintyLevel));

      default:
        return 5; // Default middle score
    }
  }

  /**
   * Build complexity factors from task
   */
  function buildFactors(task: Task): ComplexityFactor[] {
    return DEFAULT_FACTORS.map((defaultFactor) => {
      const weight = config.factorWeights?.[defaultFactor.name] ?? defaultFactor.weight;
      const score = calculateFactorScore(defaultFactor.name, task);
      
      return createComplexityFactor(
        defaultFactor.name,
        weight,
        score,
        defaultFactor.description
      );
    });
  }

  /**
   * Calculate total weighted score
   */
  function calculateTotalScore(factors: ComplexityFactor[]): number {
    const totalWeight = factors.reduce((sum, f) => sum + f.weight, 0);
    const weightedSum = factors.reduce((sum, f) => sum + getWeightedScore(f), 0);
    
    // Normalize to 1-10 scale
    const normalized = weightedSum / totalWeight;
    return Math.round(normalized * 10) / 10;
  }

  /**
   * Get primary contributing factors
   */
  function getPrimaryFactors(factors: ComplexityFactor[]): ComplexityFactor[] {
    // Sort by weighted score and return top 3
    return [...factors]
      .sort((a, b) => getWeightedScore(b) - getWeightedScore(a))
      .slice(0, 3);
  }

  /**
   * Generate reasoning text
   */
  function generateReasoning(
    score: ComplexityScore,
    primaryFactors: ComplexityFactor[]
  ): string {
    const level = score.value >= threshold ? '高' : '低〜中';
    const factorList = primaryFactors
      .map((f) => `${f.description}(${f.score}/10)`)
      .join('、');

    if (score.value >= threshold) {
      return `複雑度は${level}（${score.value}/10）です。主な要因: ${factorList}。タスク分解を推奨します。`;
    } else {
      return `複雑度は${level}（${score.value}/10）です。主な要因: ${factorList}。単一タスクとして実行可能です。`;
    }
  }

  /**
   * Suggest subtask count based on complexity
   */
  function suggestSubtaskCount(score: ComplexityScore): number {
    if (score.value < 4) return 1;
    if (score.value < 6) return 2;
    if (score.value < 8) return 3;
    if (score.value < 9) return 4;
    return 5;
  }

  return {
    analyze(task: Task): ComplexityScore {
      const factors = buildFactors(task);
      const totalScore = calculateTotalScore(factors);
      
      return createComplexityScore(totalScore, factors, threshold);
    },

    shouldDecompose(score: ComplexityScore): boolean {
      return checkShouldDecompose(score);
    },

    getRecommendation(task: Task): DecompositionRecommendation {
      const score = this.analyze(task);
      const shouldDecomp = this.shouldDecompose(score);
      const primaryFactors = getPrimaryFactors([...score.factors]);
      const reasoning = generateReasoning(score, primaryFactors);
      const suggestedCount = shouldDecomp ? suggestSubtaskCount(score) : 1;

      return Object.freeze({
        shouldDecompose: shouldDecomp,
        score,
        reasoning,
        suggestedSubtaskCount: suggestedCount,
        primaryFactors: Object.freeze(primaryFactors),
      });
    },
  };
}

// Re-export for convenience
export { shouldDecompose } from '../value-objects/ComplexityScore.js';
