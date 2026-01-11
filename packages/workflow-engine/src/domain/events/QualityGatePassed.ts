/**
 * QualityGatePassed Event
 * 
 * Domain event emitted when quality gate passes
 * 
 * @see REQ-ORCH-003 - Quality Gate Integration
 */

import type { PhaseType } from '../value-objects/index.js';
import type { QualityGateResult } from '../entities/QualityGate.js';

/**
 * Quality gate passed event
 */
export interface QualityGatePassedEvent {
  readonly type: 'QualityGatePassed';
  readonly workflowId: string;
  readonly phase: PhaseType;
  readonly gateResults: readonly QualityGateResult[];
  readonly timestamp: Date;
}

/**
 * Quality gate failed event
 */
export interface QualityGateFailedEvent {
  readonly type: 'QualityGateFailed';
  readonly workflowId: string;
  readonly phase: PhaseType;
  readonly gateResults: readonly QualityGateResult[];
  readonly failedGates: readonly string[];
  readonly timestamp: Date;
}

/**
 * Create a quality gate passed event
 * 
 * @param workflowId - Workflow ID
 * @param phase - Phase type
 * @param gateResults - Gate results
 * @returns QualityGatePassedEvent
 */
export function createQualityGatePassedEvent(
  workflowId: string,
  phase: PhaseType,
  gateResults: readonly QualityGateResult[]
): QualityGatePassedEvent {
  return Object.freeze({
    type: 'QualityGatePassed',
    workflowId,
    phase,
    gateResults,
    timestamp: new Date(),
  });
}

/**
 * Create a quality gate failed event
 * 
 * @param workflowId - Workflow ID
 * @param phase - Phase type
 * @param gateResults - Gate results
 * @returns QualityGateFailedEvent
 */
export function createQualityGateFailedEvent(
  workflowId: string,
  phase: PhaseType,
  gateResults: readonly QualityGateResult[]
): QualityGateFailedEvent {
  const failedGates = gateResults
    .filter(r => !r.passed)
    .map(r => r.gateName);
  
  return Object.freeze({
    type: 'QualityGateFailed',
    workflowId,
    phase,
    gateResults,
    failedGates,
    timestamp: new Date(),
  });
}

/**
 * Format passed event for logging
 * 
 * @param event - Event to format
 * @returns Formatted string
 */
export function formatQualityGatePassedEvent(event: QualityGatePassedEvent): string {
  const gateCount = event.gateResults.length;
  return `[${event.timestamp.toISOString()}] Workflow ${event.workflowId}: ` +
    `All ${gateCount} quality gates passed for ${event.phase}`;
}

/**
 * Format failed event for logging
 * 
 * @param event - Event to format
 * @returns Formatted string
 */
export function formatQualityGateFailedEvent(event: QualityGateFailedEvent): string {
  const failedList = event.failedGates.join(', ');
  return `[${event.timestamp.toISOString()}] Workflow ${event.workflowId}: ` +
    `Quality gates failed for ${event.phase}: ${failedList}`;
}
