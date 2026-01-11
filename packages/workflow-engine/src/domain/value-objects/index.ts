/**
 * Value Objects barrel export
 * 
 * @see REQ-ORCH-001 - Phase Transition
 * @see REQ-ORCH-002 - State Tracking
 * @see REQ-ORCH-003 - Quality Gate Integration
 */

export {
  type PhaseType,
  type PhaseMetadata,
  PHASES,
  VALID_TRANSITIONS,
  getPhaseMetadata,
  getValidTransitions,
  isValidTransition,
  getPhaseNumber,
  getAllPhases,
} from './PhaseType.js';

export {
  type TaskStatus,
  type StatusMetadata,
  STATUSES,
  VALID_STATUS_TRANSITIONS,
  getStatusMetadata,
  isValidStatusTransition,
  isTerminalStatus,
  getStatusDisplay,
} from './TaskStatus.js';

export {
  type ApprovalStatus,
  type Approval,
  APPROVAL_KEYWORDS,
  REJECTION_KEYWORDS,
  createApproval,
  parseApprovalFromInput,
  isApproved,
  isRejected,
  generateApprovalId,
} from './ApprovalStatus.js';
