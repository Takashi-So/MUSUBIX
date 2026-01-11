/**
 * Domain Events barrel export
 * 
 * @see REQ-ORCH-001 - Phase Transition
 * @see REQ-ORCH-003 - Quality Gate Integration
 */

export {
  type PhaseTransitionedEvent,
  createPhaseTransitionedEvent,
  formatPhaseTransitionedEvent,
} from './PhaseTransitioned.js';

export {
  type QualityGatePassedEvent,
  type QualityGateFailedEvent,
  createQualityGatePassedEvent,
  createQualityGateFailedEvent,
  formatQualityGatePassedEvent,
  formatQualityGateFailedEvent,
} from './QualityGatePassed.js';

/**
 * All workflow domain events
 */
export type WorkflowDomainEvent =
  | import('./PhaseTransitioned.js').PhaseTransitionedEvent
  | import('./QualityGatePassed.js').QualityGatePassedEvent
  | import('./QualityGatePassed.js').QualityGateFailedEvent;
