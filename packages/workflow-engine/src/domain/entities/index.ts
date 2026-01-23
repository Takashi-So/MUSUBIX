/**
 * Entities barrel export
 * 
 * @see REQ-ORCH-001 - Phase Transition
 * @see REQ-ORCH-002 - State Tracking
 * @see REQ-ORCH-003 - Quality Gate Integration
 */

export {
  type ArtifactType,
  type PhaseArtifact,
  type ReviewResult,
  type ReviewCheckpoint,
  type Phase,
  createPhase,
  startPhase,
  addArtifact,
  setReview,
  approvePhase,
  canTransitionTo,
  getPhaseDisplayName,
  createArtifact,
  createReviewResult,
} from './Phase.js';

export {
  type QualityCheckFn,
  type QualityCheckResult,
  type QualityGate,
  type QualityGateResult,
  createQualityGate,
  executeQualityGate,
  aggregateGateResults,
  PHASE_QUALITY_GATES,
  getPhaseGateChecks,
} from './QualityGate.js';

export {
  type WorkflowStatus,
  type Workflow,
  type RequiredArtifacts,
  type PrerequisiteCheckResult,
  createWorkflow,
  startWorkflow,
  updatePhase,
  transitionToPhase,
  getCurrentPhase,
  getWorkflowProgress,
  generateWorkflowId,
  canProceedToImplementation,
  checkImplementationPrerequisites,
} from './Workflow.js';

// FastRender Extended Quality Gates (v3.6.0)
export {
  type GateTiming,
  type GateExecutionContext,
  type GateServices,
  type ExtendedQualityGate,
  type ExtendedQualityCheckFn,
  type Task,
  type ITriageEngine,
  type INonNegotiablesEngine,
  type IEvidenceLevelValidator,
  type IBalanceRuleEngine,
  type ITestPlacementValidator,
  createExtendedGate,
  toStandardGate,
  isEntryGate,
  isExitGate,
  filterGatesByTiming,
  filterGatesByPhase,
} from './ExtendedQualityGate.js';
