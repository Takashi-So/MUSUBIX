/**
 * Workflow Entity
 * 
 * Represents the complete workflow state
 * 
 * @see REQ-ORCH-001 - Phase Transition
 * @see REQ-ORCH-002 - State Tracking
 */

import type { PhaseType } from '../value-objects/index.js';
import {
  type Phase,
  createPhase,
  startPhase,
  canTransitionTo,
} from './Phase.js';
import { getAllPhases } from '../value-objects/PhaseType.js';

/**
 * Workflow status
 */
export type WorkflowStatus = 'not-started' | 'in-progress' | 'completed' | 'failed';

/**
 * Workflow entity
 */
export interface Workflow {
  readonly id: string;
  readonly name: string;
  readonly description?: string;
  readonly status: WorkflowStatus;
  readonly currentPhase: PhaseType | null;
  readonly phases: ReadonlyMap<PhaseType, Phase>;
  readonly createdAt: Date;
  readonly updatedAt: Date;
  readonly completedAt?: Date;
}

/**
 * Create a new workflow
 * 
 * @param id - Workflow ID
 * @param name - Workflow name
 * @param description - Optional description
 * @returns New workflow
 */
export function createWorkflow(
  id: string,
  name: string,
  description?: string
): Workflow {
  const phases = new Map<PhaseType, Phase>();
  
  // Initialize all phases
  for (const phaseType of getAllPhases()) {
    phases.set(phaseType, createPhase(phaseType));
  }
  
  const now = new Date();
  return Object.freeze({
    id,
    name,
    description,
    status: 'not-started',
    currentPhase: null,
    phases,
    createdAt: now,
    updatedAt: now,
  });
}

/**
 * Start workflow (begins with requirements phase)
 * 
 * @param workflow - Workflow to start
 * @returns Updated workflow
 */
export function startWorkflow(workflow: Workflow): Workflow {
  if (workflow.status !== 'not-started') {
    throw new Error(`Cannot start workflow in status: ${workflow.status}`);
  }
  
  const firstPhase: PhaseType = 'requirements';
  const phases = new Map(workflow.phases);
  const phase = phases.get(firstPhase);
  
  if (!phase) {
    throw new Error(`Phase not found: ${firstPhase}`);
  }
  
  phases.set(firstPhase, startPhase(phase));
  
  return Object.freeze({
    ...workflow,
    status: 'in-progress',
    currentPhase: firstPhase,
    phases,
    updatedAt: new Date(),
  });
}

/**
 * Update phase in workflow
 * 
 * @param workflow - Workflow to update
 * @param phase - Updated phase
 * @returns Updated workflow
 */
export function updatePhase(workflow: Workflow, phase: Phase): Workflow {
  const phases = new Map(workflow.phases);
  phases.set(phase.type, phase);
  
  return Object.freeze({
    ...workflow,
    phases,
    updatedAt: new Date(),
  });
}

/**
 * Transition to next phase
 * 
 * @param workflow - Current workflow
 * @param targetPhase - Target phase
 * @returns Updated workflow
 * @throws Error if transition is invalid
 */
export function transitionToPhase(workflow: Workflow, targetPhase: PhaseType): Workflow {
  if (!workflow.currentPhase) {
    throw new Error('Workflow has not been started');
  }
  
  const currentPhaseEntity = workflow.phases.get(workflow.currentPhase);
  if (!currentPhaseEntity) {
    throw new Error(`Current phase not found: ${workflow.currentPhase}`);
  }
  
  // Check if transition is valid
  if (!canTransitionTo(currentPhaseEntity, targetPhase)) {
    // Special error for design → implementation (forbidden direct transition)
    if (workflow.currentPhase === 'design' && targetPhase === 'implementation') {
      throw new Error(
        '⚠️ 設計から実装への直接遷移は禁止されています。' +
        '必ずPhase 3（タスク分解）を経てください。'
      );
    }
    
    throw new Error(
      `Invalid transition from ${workflow.currentPhase} to ${targetPhase}. ` +
      `Current phase must be approved first.`
    );
  }
  
  // Start target phase
  const phases = new Map(workflow.phases);
  const targetPhaseEntity = phases.get(targetPhase);
  
  if (!targetPhaseEntity) {
    throw new Error(`Target phase not found: ${targetPhase}`);
  }
  
  phases.set(targetPhase, startPhase(targetPhaseEntity));
  
  // Check if completing
  const isCompleting = targetPhase === 'completion';
  
  return Object.freeze({
    ...workflow,
    currentPhase: targetPhase,
    phases,
    updatedAt: new Date(),
    status: isCompleting ? 'completed' : 'in-progress',
    completedAt: isCompleting ? new Date() : undefined,
  });
}

/**
 * Get current phase entity
 * 
 * @param workflow - Workflow
 * @returns Current phase or null
 */
export function getCurrentPhase(workflow: Workflow): Phase | null {
  if (!workflow.currentPhase) {
    return null;
  }
  return workflow.phases.get(workflow.currentPhase) ?? null;
}

/**
 * Get workflow progress percentage
 * 
 * @param workflow - Workflow
 * @returns Progress 0-100
 */
export function getWorkflowProgress(workflow: Workflow): number {
  const allPhases = getAllPhases();
  let completedCount = 0;
  
  for (const phase of workflow.phases.values()) {
    if (phase.status === 'approved' || phase.status === 'completed') {
      completedCount++;
    }
  }
  
  return Math.round((completedCount / allPhases.length) * 100);
}

/**
 * Generate workflow ID
 * 
 * @param name - Workflow name (optional)
 * @returns Workflow ID
 */
export function generateWorkflowId(name?: string): string {
  const timestamp = Date.now().toString(36);
  const prefix = name
    ? name.substring(0, 3).toUpperCase().replace(/[^A-Z]/g, 'X')
    : 'WFL';
  return `${prefix}-${timestamp}`;
}

/**
 * Check if workflow can proceed to implementation
 * 
 * @param workflow - Workflow to check
 * @returns true if can proceed
 */
export function canProceedToImplementation(workflow: Workflow): boolean {
  // Must have completed task-breakdown phase
  const taskBreakdownPhase = workflow.phases.get('task-breakdown');
  return taskBreakdownPhase?.status === 'approved';
}

/**
 * Required artifacts for implementation phase
 */
export interface RequiredArtifacts {
  readonly requirementsDocument: boolean;
  readonly designDocument: boolean;
  readonly taskBreakdown: boolean;
}

/**
 * Implementation Prerequisites Check Result
 */
export interface PrerequisiteCheckResult {
  readonly canProceed: boolean;
  readonly missingArtifacts: string[];
  readonly message: string;
}

/**
 * Check if all prerequisites for implementation are met
 * 
 * This is a CRITICAL check that enforces:
 * - Requirements document must exist (Phase 1)
 * - Design document must exist (Phase 2)
 * - Task breakdown must exist (Phase 3)
 * - All previous phases must be approved
 * 
 * @param workflow - Workflow to check
 * @returns PrerequisiteCheckResult
 */
export function checkImplementationPrerequisites(workflow: Workflow): PrerequisiteCheckResult {
  const missingArtifacts: string[] = [];
  
  // Check Phase 1: Requirements
  const requirementsPhase = workflow.phases.get('requirements');
  if (!requirementsPhase || requirementsPhase.status !== 'approved') {
    missingArtifacts.push('要件定義書 (Phase 1が未承認)');
  } else if (requirementsPhase.artifacts.length === 0) {
    missingArtifacts.push('要件定義書 (成果物なし)');
  }
  
  // Check Phase 2: Design
  const designPhase = workflow.phases.get('design');
  if (!designPhase || designPhase.status !== 'approved') {
    missingArtifacts.push('設計書 (Phase 2が未承認)');
  } else if (designPhase.artifacts.length === 0) {
    missingArtifacts.push('設計書 (成果物なし)');
  }
  
  // Check Phase 3: Task Breakdown
  const taskPhase = workflow.phases.get('task-breakdown');
  if (!taskPhase || taskPhase.status !== 'approved') {
    missingArtifacts.push('タスク分解 (Phase 3が未承認)');
  } else if (taskPhase.artifacts.length === 0) {
    missingArtifacts.push('タスク分解 (成果物なし)');
  }
  
  const canProceed = missingArtifacts.length === 0;
  
  return {
    canProceed,
    missingArtifacts,
    message: canProceed
      ? '✅ 全ての前提条件を満たしています。実装を開始できます。'
      : `⛔ 実装を開始できません。以下が不足しています:\n${missingArtifacts.map(a => `  - ${a}`).join('\n')}`,
  };
}
