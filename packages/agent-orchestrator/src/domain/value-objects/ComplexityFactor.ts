/**
 * ComplexityFactor Value Object
 * 
 * Represents a single factor contributing to task complexity
 * 
 * @see REQ-SDD-001 - Task Complexity Evaluation
 * @see DES-SDD-001 - ComplexityAnalyzer
 */

/**
 * Factor names for complexity analysis
 */
export type ComplexityFactorName = 
  | 'scope'
  | 'dependencies'
  | 'fileCount'
  | 'testCoverage'
  | 'uncertainty';

/**
 * Immutable complexity factor value object
 */
export interface ComplexityFactor {
  /** Factor name */
  readonly name: ComplexityFactorName;
  /** Weight in total score (0-1) */
  readonly weight: number;
  /** Individual factor score (1-10) */
  readonly score: number;
  /** Human-readable description */
  readonly description: string;
}

/**
 * Default factor definitions with weights
 */
export const DEFAULT_FACTORS: readonly Omit<ComplexityFactor, 'score'>[] = Object.freeze([
  { name: 'scope', weight: 0.30, description: '影響範囲（変更の広がり）' },
  { name: 'dependencies', weight: 0.25, description: '依存関係数（外部・内部）' },
  { name: 'fileCount', weight: 0.20, description: '変更ファイル数' },
  { name: 'testCoverage', weight: 0.15, description: 'テスト必要量' },
  { name: 'uncertainty', weight: 0.10, description: '不確実性（未知の要素）' },
]);

/**
 * Create a ComplexityFactor value object
 * 
 * @param name - Factor name
 * @param weight - Weight (0-1)
 * @param score - Score (1-10)
 * @param description - Description
 * @returns ComplexityFactor
 */
export function createComplexityFactor(
  name: ComplexityFactorName,
  weight: number,
  score: number,
  description: string
): ComplexityFactor {
  // Validate weight
  if (weight < 0 || weight > 1) {
    throw new Error(`Weight must be between 0 and 1, got: ${weight}`);
  }
  
  // Validate score
  if (score < 1 || score > 10) {
    throw new Error(`Score must be between 1 and 10, got: ${score}`);
  }

  return Object.freeze({
    name,
    weight,
    score,
    description,
  });
}

/**
 * Calculate weighted score contribution
 * 
 * @param factor - Complexity factor
 * @returns Weighted score contribution
 */
export function getWeightedScore(factor: ComplexityFactor): number {
  return factor.weight * factor.score;
}
