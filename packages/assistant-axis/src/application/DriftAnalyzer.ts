/**
 * DriftAnalyzer Service
 *
 * Analyzes messages for persona drift indicators
 *
 * @see REQ-AA-DRIFT-001 - Drift detection
 * @see REQ-AA-DRIFT-004 - Threshold alerts
 * @see arXiv:2601.10387 Section 4.2
 */

import type { IDriftAnalyzer, DriftAnalysisResult } from './interfaces.js';
import type { DriftScore } from '../domain/value-objects/DriftScore.js';
import type { ConversationDomain } from '../domain/value-objects/ConversationDomain.js';
import type { DetectedTrigger } from '../domain/value-objects/TriggerPattern.js';
import type { PersonaState } from '../domain/entities/PersonaState.js';
import type { DriftThresholds } from '../config/types.js';

import { createDriftScore } from '../domain/value-objects/DriftScore.js';
import { matchTriggers, calculateTriggerScore } from '../domain/value-objects/TriggerPattern.js';
import { getReinforcementPrompt } from '../domain/value-objects/ReinforcementPrompt.js';
import { DEFAULT_CONFIG } from '../config/defaults.js';

/**
 * DriftAnalyzer configuration
 */
export interface DriftAnalyzerConfig {
  /** Drift thresholds */
  readonly thresholds: DriftThresholds;
  /** Domain modifier for safe domains (multiplier < 1.0 reduces score) */
  readonly safeDomainModifier: number;
  /** Domain modifier for risky domains (multiplier > 1.0 increases score) */
  readonly riskyDomainModifier: number;
  /** History weight for trend analysis */
  readonly historyWeight: number;
}

/**
 * Default DriftAnalyzer configuration
 */
export const DEFAULT_DRIFT_ANALYZER_CONFIG: DriftAnalyzerConfig = {
  thresholds: DEFAULT_CONFIG.driftThresholds,
  safeDomainModifier: 0.7, // 30% reduction for safe domains
  riskyDomainModifier: 1.3, // 30% increase for risky domains
  historyWeight: 0.3, // 30% weight for historical drift
};

/**
 * Create DriftAnalyzer service
 *
 * @param config - Optional configuration
 * @returns IDriftAnalyzer implementation
 */
export function createDriftAnalyzer(
  config: DriftAnalyzerConfig = DEFAULT_DRIFT_ANALYZER_CONFIG
): IDriftAnalyzer {
  return {
    analyze(message: string, state: PersonaState): DriftAnalysisResult {
      // Detect triggers in message
      const triggers = matchTriggers(message);

      // Calculate base score from triggers
      const baseScore = this.calculateBaseScore(triggers);

      // Apply domain modifier
      const modifiedScore = this.applyDomainModifier(baseScore, state.domain);

      // Incorporate historical drift (weighted average)
      const historicalAvg = calculateHistoricalAverage(state);
      const finalScoreValue =
        modifiedScore * (1 - config.historyWeight) +
        historicalAvg * config.historyWeight;

      // Clamp to valid range
      const clampedScore = Math.max(0, Math.min(1, finalScoreValue));

      // Create drift score
      const scoreResult = createDriftScore(clampedScore, config.thresholds);
      if (!scoreResult.ok) {
        // Should not happen with clamped value, but handle gracefully
        throw new Error(`Invalid drift score: ${scoreResult.error.message}`);
      }

      const score = scoreResult.value;

      // Determine if intervention is needed
      const interventionRecommended = shouldIntervene(score, state, config);

      // Get recommended prompt if needed
      const recommendedPrompt = interventionRecommended
        ? selectReinforcementPrompt(score, state)
        : undefined;

      return {
        score,
        triggers,
        interventionRecommended,
        recommendedPrompt,
      };
    },

    calculateBaseScore(triggers: readonly DetectedTrigger[]): number {
      return calculateTriggerScore(triggers);
    },

    applyDomainModifier(baseScore: number, domain: ConversationDomain): number {
      const modifier = domain.isSafe
        ? config.safeDomainModifier
        : config.riskyDomainModifier;
      return baseScore * modifier;
    },
  };
}

/**
 * Calculate historical average drift
 */
function calculateHistoricalAverage(state: PersonaState): number {
  if (state.driftHistory.length === 0) {
    return 0;
  }

  const sum = state.driftHistory.reduce((acc, s) => acc + s.value, 0);
  return sum / state.driftHistory.length;
}

/**
 * Determine if intervention is needed
 *
 * @see REQ-AA-PROHIBIT-003 - Max 3 interventions per session
 */
function shouldIntervene(
  score: DriftScore,
  state: PersonaState,
  _config: DriftAnalyzerConfig
): boolean {
  // Check intervention limit
  const maxInterventions = DEFAULT_CONFIG.maxInterventions;
  if (state.interventionCount >= maxInterventions) {
    return false;
  }

  // HIGH drift always triggers
  if (score.level === 'HIGH') {
    return true;
  }

  // MEDIUM drift with drifting trend triggers
  if (score.level === 'MEDIUM' && state.trend === 'drifting') {
    return true;
  }

  return false;
}

/**
 * Select appropriate reinforcement prompt
 */
function selectReinforcementPrompt(score: DriftScore, state: PersonaState) {
  // HIGH drift: identity reinforcement
  if (score.level === 'HIGH') {
    return getReinforcementPrompt('identity');
  }

  // Drifting trend: recovery
  if (state.trend === 'drifting') {
    return getReinforcementPrompt('recovery');
  }

  // Default: refresh
  return getReinforcementPrompt('refresh');
}
