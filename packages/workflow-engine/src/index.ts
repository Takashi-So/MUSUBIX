/**
 * @nahisaho/musubix-workflow-engine
 * 
 * Workflow Engine for MUSUBIX - Phase Transition and Quality Gate Management
 * 
 * @packageDocumentation
 * @module workflow-engine
 * 
 * @see REQ-ORCH-001 - Phase Transition
 * @see REQ-ORCH-002 - State Tracking
 * @see REQ-ORCH-003 - Quality Gate Integration
 */

// Domain Layer
export * from './domain/index.js';

// Application Layer
export * from './application/index.js';

// Re-export key types for convenience
export type {
  PhaseType,
  TaskStatus,
  ApprovalStatus,
  Phase,
  Workflow,
  QualityGate,
  QualityGateResult,
} from './domain/index.js';

export type {
  PhaseControllerConfig,
  PhaseControllerResult,
  StateSnapshot,
  StateChangeEvent,
  GateRunResult,
} from './application/index.js';
export * from './application/PhaseController.js';
export * from './application/StateTracker.js';
export * from './application/QualityGateRunner.js';
