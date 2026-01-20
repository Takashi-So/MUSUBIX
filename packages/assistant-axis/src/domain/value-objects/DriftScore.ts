/**
 * DriftScore Value Object
 *
 * Represents a normalized drift score between 0.0 (no drift) and 1.0 (maximum drift)
 *
 * @see REQ-AA-DRIFT-001 - Drift score calculation
 * @see REQ-AA-DRIFT-004 - Threshold alerts
 * @see arXiv:2601.10387 Section 4.2
 */

import type { DriftLevel, DriftThresholds } from '../../config/types.js';
import { DEFAULT_CONFIG } from '../../config/defaults.js';

/**
 * Drift Score Value Object
 */
export interface DriftScore {
  /** Score value between 0.0 and 1.0 */
  readonly value: number;
  /** Drift level based on thresholds */
  readonly level: DriftLevel;
  /** Timestamp when score was calculated */
  readonly timestamp: Date;
}

/**
 * Validation error for DriftScore
 */
export class DriftScoreValidationError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'DriftScoreValidationError';
  }
}

/**
 * Result type for DriftScore creation
 */
export type DriftScoreResult =
  | { readonly ok: true; readonly value: DriftScore }
  | { readonly ok: false; readonly error: DriftScoreValidationError };

/**
 * Get drift level based on score and thresholds
 *
 * @param value - Drift score value (0.0 - 1.0)
 * @param thresholds - Threshold configuration
 * @returns Drift level
 */
export function getDriftLevel(
  value: number,
  thresholds: DriftThresholds = DEFAULT_CONFIG.driftThresholds
): DriftLevel {
  if (value >= thresholds.high) {
    return 'HIGH';
  }
  if (value >= thresholds.medium) {
    return 'MEDIUM';
  }
  return 'LOW';
}

/**
 * Create a DriftScore value object
 *
 * @param value - Score value (must be between 0.0 and 1.0)
 * @param thresholds - Optional threshold configuration
 * @returns Result containing DriftScore or validation error
 *
 * @example
 * ```typescript
 * const result = createDriftScore(0.45);
 * if (result.ok) {
 *   console.log(result.value.level); // 'LOW' or 'MEDIUM'
 * }
 * ```
 */
export function createDriftScore(
  value: number,
  thresholds: DriftThresholds = DEFAULT_CONFIG.driftThresholds
): DriftScoreResult {
  // Validate range
  if (value < 0.0) {
    return {
      ok: false,
      error: new DriftScoreValidationError(
        `Drift score must be >= 0.0, got ${value}`
      ),
    };
  }

  if (value > 1.0) {
    return {
      ok: false,
      error: new DriftScoreValidationError(
        `Drift score must be <= 1.0, got ${value}`
      ),
    };
  }

  if (!Number.isFinite(value)) {
    return {
      ok: false,
      error: new DriftScoreValidationError(
        `Drift score must be a finite number, got ${value}`
      ),
    };
  }

  return {
    ok: true,
    value: {
      value,
      level: getDriftLevel(value, thresholds),
      timestamp: new Date(),
    },
  };
}

/**
 * Check if score exceeds HIGH threshold (intervention needed)
 */
export function isHighDrift(
  score: DriftScore,
  thresholds: DriftThresholds = DEFAULT_CONFIG.driftThresholds
): boolean {
  return score.value >= thresholds.high;
}

/**
 * Check if score exceeds MEDIUM threshold (warning needed)
 */
export function isMediumDrift(
  score: DriftScore,
  thresholds: DriftThresholds = DEFAULT_CONFIG.driftThresholds
): boolean {
  return score.value >= thresholds.medium && score.value < thresholds.high;
}

/**
 * Check if score is in LOW range (safe)
 */
export function isLowDrift(
  score: DriftScore,
  thresholds: DriftThresholds = DEFAULT_CONFIG.driftThresholds
): boolean {
  return score.value < thresholds.medium;
}

/**
 * Compare two drift scores
 * @returns negative if a < b, positive if a > b, 0 if equal
 */
export function compareDriftScores(a: DriftScore, b: DriftScore): number {
  return a.value - b.value;
}
