/**
 * PersonaState Entity
 *
 * Represents the current state of the AI persona in the Assistant Axis
 *
 * @see REQ-AA-DRIFT-001 - Drift monitoring
 * @see REQ-AA-STAB-002 - Persona state management
 * @see arXiv:2601.10387 Section 3 - Persona Space model
 */

import type { DriftScore } from '../value-objects/DriftScore.js';
import type { ConversationDomain } from '../value-objects/ConversationDomain.js';

/**
 * Drift trend direction
 */
export type DriftTrend = 'stable' | 'drifting' | 'recovering';

/**
 * Persona State Entity
 */
export interface PersonaState {
  /** Unique identifier */
  readonly id: string;
  /** Session identifier */
  readonly sessionId: string;
  /** Current drift score */
  readonly currentDrift: DriftScore;
  /** Current conversation domain */
  readonly domain: ConversationDomain;
  /** Drift trend (calculated from history) */
  readonly trend: DriftTrend;
  /** Number of turns since last intervention */
  readonly turnsSinceIntervention: number;
  /** Number of interventions in this session */
  readonly interventionCount: number;
  /** Historical drift scores (last N turns) */
  readonly driftHistory: readonly DriftScore[];
  /** Timestamp when state was created */
  readonly createdAt: Date;
  /** Timestamp when state was last updated */
  readonly updatedAt: Date;
}

/**
 * Input for creating PersonaState
 */
export interface CreatePersonaStateInput {
  sessionId: string;
  currentDrift: DriftScore;
  domain: ConversationDomain;
}

/**
 * Input for updating PersonaState
 */
export interface UpdatePersonaStateInput {
  currentDrift?: DriftScore;
  domain?: ConversationDomain;
  interventionOccurred?: boolean;
}

// ID counter for generating unique IDs
let stateIdCounter = 0;

/**
 * Reset ID counter (for testing)
 */
export function resetPersonaStateIdCounter(): void {
  stateIdCounter = 0;
}

/**
 * Generate unique PersonaState ID
 */
function generatePersonaStateId(): string {
  stateIdCounter++;
  const dateStr = new Date().toISOString().slice(0, 10).replace(/-/g, '');
  return `PST-${dateStr}-${String(stateIdCounter).padStart(3, '0')}`;
}

/**
 * Calculate drift trend from history
 *
 * @param history - Historical drift scores (newest first)
 * @param windowSize - Number of scores to analyze
 * @returns Drift trend
 */
export function calculateDriftTrend(
  history: readonly DriftScore[],
  windowSize: number = 3
): DriftTrend {
  if (history.length < 2) {
    return 'stable';
  }

  const recentScores = history.slice(0, Math.min(windowSize, history.length));
  const values = recentScores.map((s) => s.value);

  // Calculate average change
  let totalChange = 0;
  for (let i = 0; i < values.length - 1; i++) {
    totalChange += values[i] - values[i + 1]; // newest - older
  }
  const avgChange = totalChange / (values.length - 1);

  // Threshold for considering it a trend
  const THRESHOLD = 0.05;

  if (avgChange > THRESHOLD) {
    return 'drifting';
  }
  if (avgChange < -THRESHOLD) {
    return 'recovering';
  }
  return 'stable';
}

/**
 * Create initial PersonaState
 *
 * @param input - Creation input
 * @returns PersonaState entity
 */
export function createPersonaState(input: CreatePersonaStateInput): PersonaState {
  const now = new Date();
  return {
    id: generatePersonaStateId(),
    sessionId: input.sessionId,
    currentDrift: input.currentDrift,
    domain: input.domain,
    trend: 'stable',
    turnsSinceIntervention: 0,
    interventionCount: 0,
    driftHistory: [input.currentDrift],
    createdAt: now,
    updatedAt: now,
  };
}

/**
 * Update PersonaState with new drift information
 *
 * @param state - Current state
 * @param input - Update input
 * @returns Updated PersonaState
 */
export function updatePersonaState(
  state: PersonaState,
  input: UpdatePersonaStateInput
): PersonaState {
  const newDrift = input.currentDrift ?? state.currentDrift;
  const newDomain = input.domain ?? state.domain;
  const interventionOccurred = input.interventionOccurred ?? false;

  // Update drift history (keep last 10)
  const newHistory = [newDrift, ...state.driftHistory.slice(0, 9)];

  return {
    ...state,
    currentDrift: newDrift,
    domain: newDomain,
    trend: calculateDriftTrend(newHistory),
    turnsSinceIntervention: interventionOccurred
      ? 0
      : state.turnsSinceIntervention + 1,
    interventionCount: interventionOccurred
      ? state.interventionCount + 1
      : state.interventionCount,
    driftHistory: newHistory,
    updatedAt: new Date(),
  };
}

/**
 * Check if intervention is needed based on state
 *
 * @param state - Current persona state
 * @param maxInterventions - Maximum interventions per session
 * @returns Whether intervention is needed
 *
 * @see REQ-AA-PROHIBIT-003
 */
export function needsIntervention(
  state: PersonaState,
  maxInterventions: number = 3
): boolean {
  // Check intervention limit
  if (state.interventionCount >= maxInterventions) {
    return false;
  }

  // Check if drift is HIGH
  if (state.currentDrift.level === 'HIGH') {
    return true;
  }

  // Check if drifting trend continues
  if (state.trend === 'drifting' && state.currentDrift.level === 'MEDIUM') {
    return true;
  }

  return false;
}

/**
 * Get state summary for logging
 */
export function getPersonaStateSummary(state: PersonaState): string {
  return `[${state.id}] Session: ${state.sessionId}, Drift: ${state.currentDrift.value.toFixed(2)} (${state.currentDrift.level}), Domain: ${state.domain.type}, Trend: ${state.trend}, Interventions: ${state.interventionCount}`;
}
