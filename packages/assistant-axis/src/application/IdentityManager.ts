/**
 * IdentityManager Service
 *
 * Manages identity reinforcement logic
 *
 * @see REQ-AA-STAB-001 - Identity reinforcement
 * @see REQ-AA-STAB-004 - Recovery prompts
 * @see REQ-AA-PROHIBIT-003 - Intervention limits
 * @see arXiv:2601.10387 Table 2 - Assistant traits
 */

import type {
  IIdentityManager,
  ReinforcementResult,
  DriftAnalysisResult,
} from './interfaces.js';
import type { PersonaState } from '../domain/entities/PersonaState.js';
import type { ReinforcementPrompt, ReinforcementType } from '../domain/value-objects/ReinforcementPrompt.js';

import {
  getReinforcementPrompt,
  IDENTITY_REINFORCEMENT_PROMPT,
  RECOVERY_PROMPT,
  REFRESH_PROMPT,
} from '../domain/value-objects/ReinforcementPrompt.js';
import { DEFAULT_CONFIG } from '../config/defaults.js';

/**
 * IdentityManager configuration
 */
export interface IdentityManagerConfig {
  /** Maximum interventions per session */
  readonly maxInterventionsPerSession: number;
  /** Turns between refresh prompts */
  readonly refreshIntervalTurns: number;
  /** Enable automatic refresh */
  readonly autoRefreshEnabled: boolean;
}

/**
 * Default IdentityManager configuration
 */
export const DEFAULT_IDENTITY_MANAGER_CONFIG: IdentityManagerConfig = {
  maxInterventionsPerSession: DEFAULT_CONFIG.maxInterventions,
  refreshIntervalTurns: DEFAULT_CONFIG.refreshInterval,
  autoRefreshEnabled: true,
};

/**
 * Create IdentityManager service
 *
 * @param config - Optional configuration
 * @returns IIdentityManager implementation
 */
export function createIdentityManager(
  config: IdentityManagerConfig = DEFAULT_IDENTITY_MANAGER_CONFIG
): IIdentityManager {
  return {
    determineReinforcement(
      state: PersonaState,
      analysis: DriftAnalysisResult
    ): ReinforcementResult {
      // Check if limit reached
      if (this.isLimitReached(state)) {
        return {
          prompt: REFRESH_PROMPT, // Provide a prompt even if not applying
          shouldApply: false,
          reason: `Intervention limit reached (${config.maxInterventionsPerSession} per session)`,
        };
      }

      // HIGH drift: identity reinforcement
      if (analysis.score.level === 'HIGH') {
        return {
          prompt: IDENTITY_REINFORCEMENT_PROMPT,
          shouldApply: true,
          reason: `HIGH drift detected (${analysis.score.value.toFixed(2)})`,
        };
      }

      // Drifting trend with MEDIUM: recovery
      if (state.trend === 'drifting' && analysis.score.level === 'MEDIUM') {
        return {
          prompt: RECOVERY_PROMPT,
          shouldApply: true,
          reason: `MEDIUM drift with drifting trend`,
        };
      }

      // Auto refresh check
      if (
        config.autoRefreshEnabled &&
        state.turnsSinceIntervention >= config.refreshIntervalTurns
      ) {
        return {
          prompt: REFRESH_PROMPT,
          shouldApply: true,
          reason: `Auto refresh after ${state.turnsSinceIntervention} turns`,
        };
      }

      // No reinforcement needed
      return {
        prompt: REFRESH_PROMPT,
        shouldApply: false,
        reason: `Drift level ${analysis.score.level} is acceptable`,
      };
    },

    getPrompt(type: ReinforcementType): ReinforcementPrompt {
      return getReinforcementPrompt(type);
    },

    isLimitReached(state: PersonaState): boolean {
      return state.interventionCount >= config.maxInterventionsPerSession;
    },
  };
}

/**
 * Get reinforcement reason summary
 */
export function getReinforcementSummary(result: ReinforcementResult): string {
  return `[${result.prompt.type}] ${result.shouldApply ? 'APPLY' : 'SKIP'}: ${result.reason}`;
}
