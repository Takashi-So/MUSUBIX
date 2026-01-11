/**
 * Phase Entity
 * 
 * Represents a workflow phase with its state and artifacts
 * 
 * @see REQ-ORCH-001 - Phase Transition
 * @see DES-ORCH-001 - PhaseController
 */

import {
  type PhaseType,
  type Approval,
  getPhaseMetadata,
  isValidTransition,
  createApproval,
  generateApprovalId,
} from '../value-objects/index.js';

/**
 * Phase artifact types
 */
export type ArtifactType = 
  | 'requirements'     // REQ-* document
  | 'design'           // DES-* document
  | 'task-breakdown'   // TSK-* document
  | 'implementation'   // Code files
  | 'test'             // Test files
  | 'documentation';   // Documentation files

/**
 * Phase artifact
 */
export interface PhaseArtifact {
  readonly type: ArtifactType;
  readonly path: string;
  readonly content?: string;
  readonly createdAt: Date;
  readonly updatedAt: Date;
}

/**
 * Review result
 */
export interface ReviewResult {
  readonly id: string;
  readonly phase: PhaseType;
  readonly checkpoints: ReviewCheckpoint[];
  readonly overall: 'pass' | 'warning' | 'fail';
  readonly timestamp: Date;
}

/**
 * Review checkpoint
 */
export interface ReviewCheckpoint {
  readonly name: string;
  readonly status: '✅' | '⚠️' | '❌';
  readonly details: string;
}

/**
 * Phase entity
 */
export interface Phase {
  readonly type: PhaseType;
  readonly status: 'pending' | 'in-progress' | 'completed' | 'approved';
  readonly artifacts: PhaseArtifact[];
  readonly review?: ReviewResult;
  readonly approval?: Approval;
  readonly startedAt?: Date;
  readonly completedAt?: Date;
}

/**
 * Create a new phase
 * 
 * @param type - Phase type
 * @returns New phase entity
 */
export function createPhase(type: PhaseType): Phase {
  return Object.freeze({
    type,
    status: 'pending',
    artifacts: [],
  });
}

/**
 * Start a phase
 * 
 * @param phase - Phase to start
 * @returns Updated phase
 */
export function startPhase(phase: Phase): Phase {
  if (phase.status !== 'pending') {
    throw new Error(`Cannot start phase in status: ${phase.status}`);
  }
  return Object.freeze({
    ...phase,
    status: 'in-progress',
    startedAt: new Date(),
  });
}

/**
 * Add artifact to phase
 * 
 * @param phase - Phase to update
 * @param artifact - Artifact to add
 * @returns Updated phase
 */
export function addArtifact(phase: Phase, artifact: PhaseArtifact): Phase {
  return Object.freeze({
    ...phase,
    artifacts: [...phase.artifacts, artifact],
  });
}

/**
 * Set review result
 * 
 * @param phase - Phase to update
 * @param review - Review result
 * @returns Updated phase
 */
export function setReview(phase: Phase, review: ReviewResult): Phase {
  return Object.freeze({
    ...phase,
    review,
    status: review.overall === 'pass' ? 'completed' : 'in-progress',
    completedAt: review.overall === 'pass' ? new Date() : undefined,
  });
}

/**
 * Approve phase
 * 
 * @param phase - Phase to approve
 * @param approver - Approver identifier
 * @param comment - Optional comment
 * @returns Updated phase
 */
export function approvePhase(phase: Phase, approver: string, comment?: string): Phase {
  if (phase.status !== 'completed') {
    throw new Error(`Cannot approve phase in status: ${phase.status}`);
  }
  
  const approval = createApproval(
    generateApprovalId(phase.type),
    'approved',
    approver,
    comment
  );
  
  return Object.freeze({
    ...phase,
    status: 'approved',
    approval,
  });
}

/**
 * Check if phase can transition to target
 * 
 * @param phase - Current phase
 * @param targetType - Target phase type
 * @returns true if transition is allowed
 */
export function canTransitionTo(phase: Phase, targetType: PhaseType): boolean {
  // Must be approved to transition
  if (phase.status !== 'approved') {
    return false;
  }
  
  // Check valid transition
  return isValidTransition(phase.type, targetType);
}

/**
 * Get phase display name
 * 
 * @param phase - Phase entity
 * @returns Display name
 */
export function getPhaseDisplayName(phase: Phase): string {
  return getPhaseMetadata(phase.type).label;
}

/**
 * Create artifact
 * 
 * @param type - Artifact type
 * @param path - File path
 * @param content - Optional content
 * @returns PhaseArtifact
 */
export function createArtifact(
  type: ArtifactType,
  path: string,
  content?: string
): PhaseArtifact {
  const now = new Date();
  return Object.freeze({
    type,
    path,
    content,
    createdAt: now,
    updatedAt: now,
  });
}

/**
 * Create review result
 * 
 * @param phase - Phase type
 * @param checkpoints - Review checkpoints
 * @returns ReviewResult
 */
export function createReviewResult(
  phase: PhaseType,
  checkpoints: ReviewCheckpoint[]
): ReviewResult {
  const hasFailure = checkpoints.some(c => c.status === '❌');
  const hasWarning = checkpoints.some(c => c.status === '⚠️');
  
  return Object.freeze({
    id: `REV-${phase.toUpperCase()}-${Date.now().toString(36)}`,
    phase,
    checkpoints,
    overall: hasFailure ? 'fail' : (hasWarning ? 'warning' : 'pass'),
    timestamp: new Date(),
  });
}
