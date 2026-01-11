/**
 * ComplexityScore Value Object
 * 
 * Represents the complexity score of a task (1-10 scale)
 * 
 * @see REQ-SDD-001 - Task Complexity Evaluation
 * @see DES-SDD-001 - ComplexityAnalyzer
 */

import type { ComplexityFactor } from './ComplexityFactor.js';

/**
 * Immutable complexity score value object
 */
export interface ComplexityScore {
  /** Complexity score value (1-10) */
  readonly value: number;
  /** Breakdown of complexity factors */
  readonly factors: readonly ComplexityFactor[];
  /** Threshold for decomposition recommendation */
  readonly threshold: number;
}

/**
 * Create a ComplexityScore value object
 * 
 * @param value - Score value (1-10)
 * @param factors - Complexity factors breakdown
 * @param threshold - Decomposition threshold (default: 7)
 * @returns ComplexityScore or error
 */
export function createComplexityScore(
  value: number,
  factors: ComplexityFactor[],
  threshold: number = 7
): ComplexityScore {
  // Validate score range
  if (value < 1 || value > 10) {
    throw new Error(`Complexity score must be between 1 and 10, got: ${value}`);
  }
  
  // Validate threshold range
  if (threshold < 1 || threshold > 10) {
    throw new Error(`Threshold must be between 1 and 10, got: ${threshold}`);
  }

  return Object.freeze({
    value,
    factors: Object.freeze([...factors]),
    threshold,
  });
}

/**
 * Check if task should be decomposed based on complexity score
 * 
 * @param score - Complexity score to evaluate
 * @returns true if score >= threshold
 */
export function shouldDecompose(score: ComplexityScore): boolean {
  return score.value >= score.threshold;
}

/**
 * Get complexity level label
 * 
 * @param score - Complexity score
 * @returns Human-readable complexity level
 */
export function getComplexityLevel(score: ComplexityScore): 'low' | 'medium' | 'high' | 'critical' {
  if (score.value <= 3) return 'low';
  if (score.value <= 5) return 'medium';
  if (score.value <= 7) return 'high';
  return 'critical';
}
