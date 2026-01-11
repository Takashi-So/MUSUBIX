/**
 * PhaseTransitioned Event
 * 
 * Domain event emitted when a phase transition occurs
 * 
 * @see REQ-ORCH-001 - Phase Transition
 */

import type { PhaseType } from '../value-objects/index.js';

/**
 * Phase transitioned event
 */
export interface PhaseTransitionedEvent {
  readonly type: 'PhaseTransitioned';
  readonly workflowId: string;
  readonly fromPhase: PhaseType;
  readonly toPhase: PhaseType;
  readonly timestamp: Date;
  readonly approvedBy?: string;
}

/**
 * Create a phase transitioned event
 * 
 * @param workflowId - Workflow ID
 * @param fromPhase - Source phase
 * @param toPhase - Target phase
 * @param approvedBy - Approver (optional)
 * @returns PhaseTransitionedEvent
 */
export function createPhaseTransitionedEvent(
  workflowId: string,
  fromPhase: PhaseType,
  toPhase: PhaseType,
  approvedBy?: string
): PhaseTransitionedEvent {
  return Object.freeze({
    type: 'PhaseTransitioned',
    workflowId,
    fromPhase,
    toPhase,
    timestamp: new Date(),
    approvedBy,
  });
}

/**
 * Format event for logging
 * 
 * @param event - Event to format
 * @returns Formatted string
 */
export function formatPhaseTransitionedEvent(event: PhaseTransitionedEvent): string {
  const approver = event.approvedBy ? ` (approved by ${event.approvedBy})` : '';
  return `[${event.timestamp.toISOString()}] Workflow ${event.workflowId}: ` +
    `${event.fromPhase} → ${event.toPhase}${approver}`;
}
