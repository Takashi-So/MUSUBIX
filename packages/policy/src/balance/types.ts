/**
 * BalanceRule Value Objects
 *
 * Defines balance rules for the 90/10 rule validation.
 * Ensures that counted changes (real functionality) maintain a high ratio.
 *
 * @see TSK-FR-028 - BalanceRuleEngine型定義
 * @see REQ-FR-001〜003 - BalanceRuleEngine
 * @trace DES-MUSUBIX-FR-001 DES-POLICY-001
 */

/**
 * Change category classification
 * - counted: Real functionality that counts toward productivity
 * - non-counted: Support/infrastructure that doesn't count
 */
export type ChangeCategory = 'counted' | 'non-counted';

/**
 * Change type for balance calculation
 */
export type BalanceChangeType =
  | 'feature'       // New feature implementation (counted)
  | 'bugfix'        // Bug fix (counted)
  | 'test'          // Test code (counted, but weighted)
  | 'refactor'      // Refactoring (counted)
  | 'config'        // Configuration changes (non-counted)
  | 'build'         // Build system changes (non-counted)
  | 'ci'            // CI/CD changes (non-counted)
  | 'docs'          // Documentation (non-counted)
  | 'style'         // Style/formatting (non-counted)
  | 'chore';        // Maintenance tasks (non-counted)

/**
 * Balance change record
 */
export interface BalanceChange {
  readonly id: string;
  readonly type: BalanceChangeType;
  readonly category: ChangeCategory;
  readonly file: string;
  readonly linesAdded: number;
  readonly linesRemoved: number;
  readonly timestamp: number;
  readonly description?: string;
}

/**
 * Balance metrics
 */
export interface BalanceMetrics {
  readonly countedChanges: number;
  readonly nonCountedChanges: number;
  readonly totalChanges: number;
  readonly countedLines: number;
  readonly nonCountedLines: number;
  readonly totalLines: number;
  readonly ratio: number;          // Counted / Total (0-1)
  readonly exceedsThreshold: boolean;
  readonly threshold: number;      // Configured threshold (e.g., 0.1 = 10%)
}

/**
 * Balance rule evaluation result
 */
export interface BalanceEvaluationResult {
  readonly passed: boolean;
  readonly message: string;
  readonly severity: 'info' | 'warning' | 'error';
  readonly metrics: BalanceMetrics;
  readonly recommendations?: readonly string[];
}

/**
 * Balance configuration
 */
export interface BalanceConfig {
  /** Maximum allowed ratio of non-counted changes (0-1) */
  readonly maxNonCountedRatio: number;
  /** Severity when threshold exceeded */
  readonly exceedSeverity: 'warning' | 'error';
  /** Weights for different change types */
  readonly typeWeights: Readonly<Record<BalanceChangeType, number>>;
  /** Whether to include test code in counted */
  readonly countTests: boolean;
  /** Test code weight (0-1) */
  readonly testWeight: number;
}

/**
 * Default balance configuration
 * 90/10 rule: At least 90% counted changes, max 10% non-counted
 */
export const DEFAULT_BALANCE_CONFIG: BalanceConfig = Object.freeze({
  maxNonCountedRatio: 0.1, // 10%
  exceedSeverity: 'warning',
  typeWeights: Object.freeze({
    feature: 1.0,
    bugfix: 1.0,
    test: 0.5,     // Tests count at 50%
    refactor: 0.8, // Refactoring counts at 80%
    config: 0,
    build: 0,
    ci: 0,
    docs: 0,
    style: 0,
    chore: 0,
  }),
  countTests: true,
  testWeight: 0.5,
});

/**
 * Mapping of change types to categories
 */
export const CHANGE_TYPE_CATEGORIES: Readonly<Record<BalanceChangeType, ChangeCategory>> = Object.freeze({
  feature: 'counted',
  bugfix: 'counted',
  test: 'counted',
  refactor: 'counted',
  config: 'non-counted',
  build: 'non-counted',
  ci: 'non-counted',
  docs: 'non-counted',
  style: 'non-counted',
  chore: 'non-counted',
});

/**
 * Get category for a change type
 */
export function getChangeCategory(type: BalanceChangeType): ChangeCategory {
  return CHANGE_TYPE_CATEGORIES[type];
}

/**
 * Check if a change type is counted
 */
export function isCounted(type: BalanceChangeType): boolean {
  return getChangeCategory(type) === 'counted';
}

/**
 * Create a balance change record
 */
export function createBalanceChange(params: {
  id?: string;
  type: BalanceChangeType;
  file: string;
  linesAdded: number;
  linesRemoved: number;
  description?: string;
}): BalanceChange {
  const id = params.id ?? `CHG-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;

  return Object.freeze({
    id,
    type: params.type,
    category: getChangeCategory(params.type),
    file: params.file,
    linesAdded: params.linesAdded,
    linesRemoved: params.linesRemoved,
    timestamp: Date.now(),
    description: params.description,
  });
}

/**
 * Calculate total lines for a change
 */
export function getTotalLines(change: BalanceChange): number {
  return change.linesAdded + change.linesRemoved;
}

/**
 * Calculate weighted lines for a change
 */
export function getWeightedLines(
  change: BalanceChange,
  config: BalanceConfig = DEFAULT_BALANCE_CONFIG
): number {
  const totalLines = getTotalLines(change);
  const weight = config.typeWeights[change.type];
  return totalLines * weight;
}
