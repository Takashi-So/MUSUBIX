/**
 * DriftEvent Entity
 *
 * Represents drift-related events for audit and analysis
 *
 * @see REQ-AA-PROHIBIT-004 - Intervention logging
 * @see REQ-AA-MON-001 - Event tracking
 */

import type { DriftScore } from '../value-objects/DriftScore.js';
import type { DetectedTrigger } from '../value-objects/TriggerPattern.js';
import type { ReinforcementPrompt } from '../value-objects/ReinforcementPrompt.js';
import type { DriftTrend } from './PersonaState.js';

/**
 * Event types in the Assistant Axis system
 */
export type DriftEventType =
  | 'drift-detected' // Drift score exceeded threshold
  | 'intervention-triggered' // Intervention was applied
  | 'domain-changed' // Conversation domain changed
  | 'session-started' // New session started
  | 'session-ended' // Session ended
  | 'threshold-exceeded' // HIGH threshold crossed
  | 'trend-changed'; // Drift trend changed

/**
 * Base event interface
 */
export interface BaseDriftEvent {
  /** Unique event identifier */
  readonly id: string;
  /** Event type */
  readonly type: DriftEventType;
  /** Session identifier */
  readonly sessionId: string;
  /** Event timestamp */
  readonly timestamp: Date;
  /** Current workflow phase (if applicable) */
  readonly workflowPhase?: string;
}

/**
 * Drift Detection Event
 */
export interface DriftDetectedEvent extends BaseDriftEvent {
  readonly type: 'drift-detected';
  readonly driftScore: DriftScore;
  readonly triggers: readonly DetectedTrigger[];
  readonly previousScore?: DriftScore;
}

/**
 * Intervention Triggered Event
 */
export interface InterventionTriggeredEvent extends BaseDriftEvent {
  readonly type: 'intervention-triggered';
  readonly driftScore: DriftScore;
  readonly prompt: ReinforcementPrompt;
  readonly interventionNumber: number;
}

/**
 * Domain Changed Event
 */
export interface DomainChangedEvent extends BaseDriftEvent {
  readonly type: 'domain-changed';
  readonly previousDomain: string;
  readonly newDomain: string;
  readonly confidence: number;
}

/**
 * Session Started Event
 */
export interface SessionStartedEvent extends BaseDriftEvent {
  readonly type: 'session-started';
  readonly initialDomain: string;
}

/**
 * Session Ended Event
 */
export interface SessionEndedEvent extends BaseDriftEvent {
  readonly type: 'session-ended';
  readonly totalTurns: number;
  readonly totalInterventions: number;
  readonly averageDrift: number;
}

/**
 * Threshold Exceeded Event
 */
export interface ThresholdExceededEvent extends BaseDriftEvent {
  readonly type: 'threshold-exceeded';
  readonly driftScore: DriftScore;
  readonly threshold: 'MEDIUM' | 'HIGH';
}

/**
 * Trend Changed Event
 */
export interface TrendChangedEvent extends BaseDriftEvent {
  readonly type: 'trend-changed';
  readonly previousTrend: DriftTrend;
  readonly newTrend: DriftTrend;
  readonly driftScore: DriftScore;
}

/**
 * Union type for all drift events
 */
export type DriftEvent =
  | DriftDetectedEvent
  | InterventionTriggeredEvent
  | DomainChangedEvent
  | SessionStartedEvent
  | SessionEndedEvent
  | ThresholdExceededEvent
  | TrendChangedEvent;

// ID counter for generating unique IDs
let eventIdCounter = 0;

/**
 * Reset ID counter (for testing)
 */
export function resetDriftEventIdCounter(): void {
  eventIdCounter = 0;
}

/**
 * Generate unique DriftEvent ID
 */
function generateEventId(type: DriftEventType): string {
  eventIdCounter++;
  const dateStr = new Date().toISOString().slice(0, 10).replace(/-/g, '');
  const prefix = type.toUpperCase().replace(/-/g, '').slice(0, 4);
  return `EVT-${prefix}-${dateStr}-${String(eventIdCounter).padStart(4, '0')}`;
}

/**
 * Create Drift Detected Event
 */
export function createDriftDetectedEvent(
  sessionId: string,
  driftScore: DriftScore,
  triggers: readonly DetectedTrigger[],
  previousScore?: DriftScore,
  workflowPhase?: string
): DriftDetectedEvent {
  return {
    id: generateEventId('drift-detected'),
    type: 'drift-detected',
    sessionId,
    timestamp: new Date(),
    workflowPhase,
    driftScore,
    triggers,
    previousScore,
  };
}

/**
 * Create Intervention Triggered Event
 */
export function createInterventionTriggeredEvent(
  sessionId: string,
  driftScore: DriftScore,
  prompt: ReinforcementPrompt,
  interventionNumber: number,
  workflowPhase?: string
): InterventionTriggeredEvent {
  return {
    id: generateEventId('intervention-triggered'),
    type: 'intervention-triggered',
    sessionId,
    timestamp: new Date(),
    workflowPhase,
    driftScore,
    prompt,
    interventionNumber,
  };
}

/**
 * Create Domain Changed Event
 */
export function createDomainChangedEvent(
  sessionId: string,
  previousDomain: string,
  newDomain: string,
  confidence: number,
  workflowPhase?: string
): DomainChangedEvent {
  return {
    id: generateEventId('domain-changed'),
    type: 'domain-changed',
    sessionId,
    timestamp: new Date(),
    workflowPhase,
    previousDomain,
    newDomain,
    confidence,
  };
}

/**
 * Create Session Started Event
 */
export function createSessionStartedEvent(
  sessionId: string,
  initialDomain: string,
  workflowPhase?: string
): SessionStartedEvent {
  return {
    id: generateEventId('session-started'),
    type: 'session-started',
    sessionId,
    timestamp: new Date(),
    workflowPhase,
    initialDomain,
  };
}

/**
 * Create Session Ended Event
 */
export function createSessionEndedEvent(
  sessionId: string,
  totalTurns: number,
  totalInterventions: number,
  averageDrift: number,
  workflowPhase?: string
): SessionEndedEvent {
  return {
    id: generateEventId('session-ended'),
    type: 'session-ended',
    sessionId,
    timestamp: new Date(),
    workflowPhase,
    totalTurns,
    totalInterventions,
    averageDrift,
  };
}

/**
 * Create Threshold Exceeded Event
 */
export function createThresholdExceededEvent(
  sessionId: string,
  driftScore: DriftScore,
  threshold: 'MEDIUM' | 'HIGH',
  workflowPhase?: string
): ThresholdExceededEvent {
  return {
    id: generateEventId('threshold-exceeded'),
    type: 'threshold-exceeded',
    sessionId,
    timestamp: new Date(),
    workflowPhase,
    driftScore,
    threshold,
  };
}

/**
 * Create Trend Changed Event
 */
export function createTrendChangedEvent(
  sessionId: string,
  previousTrend: DriftTrend,
  newTrend: DriftTrend,
  driftScore: DriftScore,
  workflowPhase?: string
): TrendChangedEvent {
  return {
    id: generateEventId('trend-changed'),
    type: 'trend-changed',
    sessionId,
    timestamp: new Date(),
    workflowPhase,
    previousTrend,
    newTrend,
    driftScore,
  };
}

/**
 * Check if event is intervention-related
 */
export function isInterventionEvent(event: DriftEvent): boolean {
  return event.type === 'intervention-triggered';
}

/**
 * Get event summary for logging
 */
export function getEventSummary(event: DriftEvent): string {
  const base = `[${event.id}] ${event.type} @ ${event.timestamp.toISOString()}`;

  switch (event.type) {
    case 'drift-detected':
      return `${base} - Score: ${event.driftScore.value.toFixed(2)}, Triggers: ${event.triggers.length}`;
    case 'intervention-triggered':
      return `${base} - Prompt type: ${event.prompt.type}, Intervention #${event.interventionNumber}`;
    case 'domain-changed':
      return `${base} - ${event.previousDomain} → ${event.newDomain}`;
    case 'session-started':
      return `${base} - Domain: ${event.initialDomain}`;
    case 'session-ended':
      return `${base} - Turns: ${event.totalTurns}, Interventions: ${event.totalInterventions}, Avg drift: ${event.averageDrift.toFixed(2)}`;
    case 'threshold-exceeded':
      return `${base} - Threshold: ${event.threshold}, Score: ${event.driftScore.value.toFixed(2)}`;
    case 'trend-changed':
      return `${base} - ${event.previousTrend} → ${event.newTrend}`;
  }
}
