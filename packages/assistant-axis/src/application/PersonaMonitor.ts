/**
 * PersonaMonitor Service
 *
 * Main monitoring service that orchestrates drift detection and identity management
 *
 * @see REQ-AA-DRIFT-001 - Drift monitoring
 * @see REQ-AA-STAB-001 - Identity reinforcement
 * @see REQ-AA-MON-001 - Session monitoring
 * @see arXiv:2601.10387 - Assistant Axis model
 */

import type {
  IPersonaMonitor,
  IDriftAnalyzer,
  IDomainClassifier,
  IIdentityManager,
  IEventLogger,
  MonitoringResult,
} from './interfaces.js';
import type { PersonaState } from '../domain/entities/PersonaState.js';
import type { DriftEvent } from '../domain/entities/DriftEvent.js';
import type { DomainType } from '../domain/value-objects/ConversationDomain.js';

import {
  createPersonaState,
  updatePersonaState,
} from '../domain/entities/PersonaState.js';
import {
  createSessionStartedEvent,
  createSessionEndedEvent,
  createDriftDetectedEvent,
  createInterventionTriggeredEvent,
  createDomainChangedEvent,
  createThresholdExceededEvent,
  createTrendChangedEvent,
} from '../domain/entities/DriftEvent.js';
import { createDriftScore } from '../domain/value-objects/DriftScore.js';
import { createConversationDomain } from '../domain/value-objects/ConversationDomain.js';
import { createDriftAnalyzer } from './DriftAnalyzer.js';
import { createDomainClassifier } from './DomainClassifier.js';
import { createIdentityManager } from './IdentityManager.js';

/**
 * PersonaMonitor configuration
 */
export interface PersonaMonitorConfig {
  /** Custom drift analyzer */
  readonly driftAnalyzer?: IDriftAnalyzer;
  /** Custom domain classifier */
  readonly domainClassifier?: IDomainClassifier;
  /** Custom identity manager */
  readonly identityManager?: IIdentityManager;
  /** Event logger (optional) */
  readonly eventLogger?: IEventLogger;
  /** Enable event logging */
  readonly enableLogging: boolean;
}

/**
 * Default PersonaMonitor configuration
 */
export const DEFAULT_PERSONA_MONITOR_CONFIG: PersonaMonitorConfig = {
  enableLogging: true,
};

// Session state store
const sessionStates = new Map<string, PersonaState>();
const sessionEvents = new Map<string, DriftEvent[]>();

/**
 * Reset all sessions (for testing)
 */
export function resetPersonaMonitor(): void {
  sessionStates.clear();
  sessionEvents.clear();
}

/**
 * Create PersonaMonitor service
 *
 * @param config - Optional configuration
 * @returns IPersonaMonitor implementation
 */
export function createPersonaMonitor(
  config: PersonaMonitorConfig = DEFAULT_PERSONA_MONITOR_CONFIG
): IPersonaMonitor {
  const driftAnalyzer = config.driftAnalyzer ?? createDriftAnalyzer();
  const domainClassifier = config.domainClassifier ?? createDomainClassifier();
  const identityManager = config.identityManager ?? createIdentityManager();
  const eventLogger = config.eventLogger;

  const logEvent = (event: DriftEvent) => {
    if (config.enableLogging) {
      // Store in session events
      const events = sessionEvents.get(event.sessionId) ?? [];
      events.push(event);
      sessionEvents.set(event.sessionId, events);

      // Log to external logger if provided
      eventLogger?.log(event);
    }
  };

  return {
    process(
      sessionId: string,
      message: string,
      workflowPhase?: string
    ): MonitoringResult {
      const events: DriftEvent[] = [];

      // Get or create session state
      let state = sessionStates.get(sessionId);
      if (!state) {
        // Auto-start session
        this.startSession(sessionId);
        state = sessionStates.get(sessionId)!;
      }

      // Classify domain
      const classification = domainClassifier.classify(message);

      // Log domain change if occurred
      if (classification.domainChanged) {
        const domainEvent = createDomainChangedEvent(
          sessionId,
          state.domain.type,
          classification.domain.type,
          classification.domain.confidence,
          workflowPhase
        );
        events.push(domainEvent);
        logEvent(domainEvent);
      }

      // Update state with new domain
      const previousTrend = state.trend;
      state = updatePersonaState(state, { domain: classification.domain });

      // Analyze for drift
      const analysis = driftAnalyzer.analyze(message, state);

      // Log drift detection
      const driftEvent = createDriftDetectedEvent(
        sessionId,
        analysis.score,
        analysis.triggers,
        state.driftHistory[1], // Previous score
        workflowPhase
      );
      events.push(driftEvent);
      logEvent(driftEvent);

      // Check for threshold exceeded
      if (analysis.score.level === 'HIGH' || analysis.score.level === 'MEDIUM') {
        const thresholdEvent = createThresholdExceededEvent(
          sessionId,
          analysis.score,
          analysis.score.level,
          workflowPhase
        );
        events.push(thresholdEvent);
        logEvent(thresholdEvent);
      }

      // Update state with new drift
      state = updatePersonaState(state, { currentDrift: analysis.score });

      // Check for trend change
      if (state.trend !== previousTrend) {
        const trendEvent = createTrendChangedEvent(
          sessionId,
          previousTrend,
          state.trend,
          analysis.score,
          workflowPhase
        );
        events.push(trendEvent);
        logEvent(trendEvent);
      }

      // Determine reinforcement
      const reinforcement = identityManager.determineReinforcement(
        state,
        analysis
      );

      // Apply intervention if needed
      if (reinforcement.shouldApply) {
        state = updatePersonaState(state, { interventionOccurred: true });

        const interventionEvent = createInterventionTriggeredEvent(
          sessionId,
          analysis.score,
          reinforcement.prompt,
          state.interventionCount,
          workflowPhase
        );
        events.push(interventionEvent);
        logEvent(interventionEvent);
      }

      // Save updated state
      sessionStates.set(sessionId, state);

      return {
        state,
        analysis,
        classification,
        reinforcement: reinforcement.shouldApply ? reinforcement : undefined,
        events,
      };
    },

    getState(sessionId: string): PersonaState | undefined {
      return sessionStates.get(sessionId);
    },

    startSession(sessionId: string, initialDomain: DomainType = 'coding'): void {
      // Create initial drift score
      const driftResult = createDriftScore(0.0);
      if (!driftResult.ok) {
        throw new Error('Failed to create initial drift score');
      }

      // Create initial domain
      const domainResult = createConversationDomain(initialDomain, 1.0);
      if (!domainResult.ok) {
        throw new Error('Failed to create initial domain');
      }

      // Create initial state
      const state = createPersonaState({
        sessionId,
        currentDrift: driftResult.value,
        domain: domainResult.value,
      });

      sessionStates.set(sessionId, state);
      sessionEvents.set(sessionId, []);

      // Log session start
      const startEvent = createSessionStartedEvent(sessionId, initialDomain);
      const events = sessionEvents.get(sessionId)!;
      events.push(startEvent);
      logEvent(startEvent);
    },

    endSession(sessionId: string): void {
      const state = sessionStates.get(sessionId);
      if (!state) {
        return;
      }

      // Calculate session metrics
      const totalTurns = state.driftHistory.length;
      const totalInterventions = state.interventionCount;
      const averageDrift =
        state.driftHistory.reduce((sum, s) => sum + s.value, 0) / totalTurns;

      // Log session end
      const endEvent = createSessionEndedEvent(
        sessionId,
        totalTurns,
        totalInterventions,
        averageDrift
      );
      const events = sessionEvents.get(sessionId) ?? [];
      events.push(endEvent);
      logEvent(endEvent);

      // Clean up
      sessionStates.delete(sessionId);
    },

    onPhaseChange(_sessionId: string, _newPhase: string): void {
      const state = sessionStates.get(_sessionId);
      if (!state) {
        return;
      }

      // Phase change may affect monitoring frequency
      // This is handled by WorkflowIntegration in infrastructure layer
      // Here we just log the phase context for events
    },
  };
}

/**
 * Get all session IDs
 */
export function getActiveSessions(): string[] {
  return Array.from(sessionStates.keys());
}

/**
 * Get session events
 */
export function getSessionEvents(sessionId: string): readonly DriftEvent[] {
  return sessionEvents.get(sessionId) ?? [];
}
