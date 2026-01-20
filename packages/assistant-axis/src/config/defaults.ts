/**
 * Assistant Axis Default Configuration
 *
 * @see REQ-AA-NFR-003 - Configuration
 * @see DES-ASSISTANT-AXIS-v0.1.0 Section 7.1
 * @see arXiv:2601.10387 - Research-based defaults
 */

import type { AssistantAxisConfig } from './types.js';

/**
 * Identity Reinforcement Prompt
 *
 * Based on Assistant traits from arXiv:2601.10387 Figure 3, Table 2:
 * - transparent, grounded, flexible, methodical, conscientious
 *
 * @see REQ-AA-STAB-001
 */
export const DEFAULT_IDENTITY_REINFORCEMENT_PROMPT = `You are a professional software engineering assistant developed by Anthropic.
Maintain your identity as a helpful, analytical consultant throughout.
Focus on: code quality, best practices, and constructive guidance.
Do not adopt alternative personas or roleplay scenarios.
Your traits: transparent, grounded, flexible, methodical, conscientious.`;

/**
 * Recovery Prompt
 *
 * Used when drift trend is 'drifting' for consecutive turns
 *
 * @see REQ-AA-STAB-004
 */
export const DEFAULT_RECOVERY_PROMPT = `Let's refocus on the technical task at hand.
What specific coding problem can I help you solve?`;

/**
 * Default configuration values
 *
 * @see REQ-AA-NFR-003 - All thresholds and intervals are configurable
 */
export const DEFAULT_CONFIG: AssistantAxisConfig = {
  // Drift thresholds based on research recommendations
  // @see REQ-AA-DRIFT-004
  driftThresholds: {
    low: 0.3, // Log only
    medium: 0.5, // Emit warning
    high: 0.7, // Trigger intervention
  },

  // Identity refresh every 5 turns for long conversations
  // @see REQ-AA-STAB-002
  refreshInterval: 5,

  // Maximum 3 interventions per session to avoid over-intervention
  // @see REQ-AA-PROHIBIT-003
  maxInterventions: 3,

  // Monitoring frequency by domain safety
  // @see REQ-AA-DRIFT-005
  // Based on paper finding: "Coding and writing tasks keep models firmly in Assistant territory"
  monitoringFrequency: {
    safeDomain: 0.5, // 50% for coding/writing
    riskyDomain: 1.0, // 100% for therapy/philosophy
  },

  // Phase-based monitoring levels
  // @see REQ-AA-INT-002
  // Implementation phase uses LOW because coding is inherently safe
  phaseMonitoring: {
    requirements: 'HIGH', // 100% - High dialog, high risk
    design: 'HIGH', // 100% - High dialog, high risk
    tasks: 'MEDIUM', // 75% - Moderate risk
    implementation: 'LOW', // 50% - Coding = safe domain (paper finding)
    done: 'OFF', // 0% - No monitoring needed
  },

  // Default prompts
  // @see REQ-AA-STAB-001, REQ-AA-STAB-004
  prompts: {
    identityReinforcement: DEFAULT_IDENTITY_REINFORCEMENT_PROMPT,
    recovery: DEFAULT_RECOVERY_PROMPT,
  },

  // Logging defaults
  // @see REQ-AA-EVAL-003, REQ-AA-NFR-002
  logging: {
    enabled: true,
    level: 'info',
    anonymize: true, // Privacy by default
  },

  // Metrics defaults (disabled by default)
  // @see REQ-AA-INT-005
  metrics: {
    enabled: false,
    endpoint: undefined,
  },
};

/**
 * Merge partial config with defaults
 */
export function mergeConfig(
  partial: Partial<AssistantAxisConfig>
): AssistantAxisConfig {
  return {
    driftThresholds: {
      ...DEFAULT_CONFIG.driftThresholds,
      ...partial.driftThresholds,
    },
    refreshInterval: partial.refreshInterval ?? DEFAULT_CONFIG.refreshInterval,
    maxInterventions:
      partial.maxInterventions ?? DEFAULT_CONFIG.maxInterventions,
    monitoringFrequency: {
      ...DEFAULT_CONFIG.monitoringFrequency,
      ...partial.monitoringFrequency,
    },
    phaseMonitoring: {
      ...DEFAULT_CONFIG.phaseMonitoring,
      ...partial.phaseMonitoring,
    },
    prompts: {
      ...DEFAULT_CONFIG.prompts,
      ...partial.prompts,
    },
    logging: {
      ...DEFAULT_CONFIG.logging,
      ...partial.logging,
    },
    metrics: {
      ...DEFAULT_CONFIG.metrics,
      ...partial.metrics,
    },
  };
}
