/**
 * Status Workflow Utility
 * 
 * Defines common status workflows for entities.
 * Based on learnings from 10-project validation (2026-01-04).
 * 
 * @requirement REQ-LEARN-001 - Self-learning system pattern application
 * @pattern status-workflow - Standard status transitions
 * 
 * @packageDocumentation
 * @module utils/status-workflow
 */

/**
 * Generic status type for workflow entities
 */
export type WorkflowStatus = string;

/**
 * Status transition definition
 */
export interface StatusTransition<S extends WorkflowStatus> {
  from: S | S[];
  to: S;
  action: string;
  guard?: () => boolean;
}

/**
 * Status workflow configuration
 */
export interface WorkflowConfig<S extends WorkflowStatus> {
  initialStatus: S;
  statuses: readonly S[];
  transitions: StatusTransition<S>[];
  finalStatuses?: S[];
}

/**
 * Status Workflow Manager
 * 
 * Manages status transitions with validation and history tracking.
 * 
 * @example
 * ```typescript
 * const orderWorkflow = new StatusWorkflow({
 *   initialStatus: 'pending',
 *   statuses: ['pending', 'confirmed', 'processing', 'completed', 'cancelled'],
 *   transitions: [
 *     { from: 'pending', to: 'confirmed', action: 'confirm' },
 *     { from: 'confirmed', to: 'processing', action: 'start' },
 *     { from: 'processing', to: 'completed', action: 'complete' },
 *     { from: ['pending', 'confirmed'], to: 'cancelled', action: 'cancel' },
 *   ],
 *   finalStatuses: ['completed', 'cancelled']
 * });
 * 
 * orderWorkflow.transition('pending', 'confirm'); // 'confirmed'
 * orderWorkflow.canTransition('confirmed', 'cancel'); // true
 * ```
 */
export class StatusWorkflow<S extends WorkflowStatus> {
  private config: WorkflowConfig<S>;

  constructor(config: WorkflowConfig<S>) {
    this.config = config;
    this.validateConfig();
  }

  /**
   * Gets the initial status
   */
  getInitialStatus(): S {
    return this.config.initialStatus;
  }

  /**
   * Gets all valid statuses
   */
  getStatuses(): readonly S[] {
    return this.config.statuses;
  }

  /**
   * Gets final (terminal) statuses
   */
  getFinalStatuses(): S[] {
    return this.config.finalStatuses || [];
  }

  /**
   * Checks if a status is final
   */
  isFinalStatus(status: S): boolean {
    return this.getFinalStatuses().includes(status);
  }

  /**
   * Checks if a transition is valid
   */
  canTransition(currentStatus: S, action: string): boolean {
    const transition = this.findTransition(currentStatus, action);
    if (!transition) return false;
    if (transition.guard && !transition.guard()) return false;
    return true;
  }

  /**
   * Gets the next status for an action
   * @throws Error if transition is not valid
   */
  transition(currentStatus: S, action: string): S {
    if (!this.canTransition(currentStatus, action)) {
      throw new Error(
        `Invalid transition: cannot perform '${action}' from status '${currentStatus}'`
      );
    }

    const transition = this.findTransition(currentStatus, action)!;
    return transition.to;
  }

  /**
   * Gets available actions from current status
   */
  getAvailableActions(currentStatus: S): string[] {
    return this.config.transitions
      .filter((t) => {
        const fromStatuses = Array.isArray(t.from) ? t.from : [t.from];
        return fromStatuses.includes(currentStatus);
      })
      .filter((t) => !t.guard || t.guard())
      .map((t) => t.action);
  }

  /**
   * Gets possible next statuses from current status
   */
  getPossibleNextStatuses(currentStatus: S): S[] {
    const actions = this.getAvailableActions(currentStatus);
    return [...new Set(actions.map((action) => {
      const transition = this.findTransition(currentStatus, action)!;
      return transition.to;
    }))];
  }

  private findTransition(currentStatus: S, action: string): StatusTransition<S> | undefined {
    return this.config.transitions.find((t) => {
      const fromStatuses = Array.isArray(t.from) ? t.from : [t.from];
      return fromStatuses.includes(currentStatus) && t.action === action;
    });
  }

  private validateConfig(): void {
    // Validate initial status is in statuses
    if (!this.config.statuses.includes(this.config.initialStatus)) {
      throw new Error(`Initial status '${this.config.initialStatus}' is not in statuses list`);
    }

    // Validate all transition statuses are in statuses list
    for (const transition of this.config.transitions) {
      const fromStatuses = Array.isArray(transition.from) ? transition.from : [transition.from];
      for (const from of fromStatuses) {
        if (!this.config.statuses.includes(from)) {
          throw new Error(`Transition 'from' status '${from}' is not in statuses list`);
        }
      }
      if (!this.config.statuses.includes(transition.to)) {
        throw new Error(`Transition 'to' status '${transition.to}' is not in statuses list`);
      }
    }

    // Validate final statuses are in statuses list
    for (const final of this.config.finalStatuses || []) {
      if (!this.config.statuses.includes(final)) {
        throw new Error(`Final status '${final}' is not in statuses list`);
      }
    }
  }
}

// ============================================
// Pre-defined Common Workflows
// ============================================

/**
 * Standard approval statuses
 */
export const ApprovalStatuses = ['draft', 'pending', 'approved', 'rejected'] as const;
export type ApprovalStatus = typeof ApprovalStatuses[number];

/**
 * Standard approval workflow
 */
export const approvalWorkflow = new StatusWorkflow<ApprovalStatus>({
  initialStatus: 'draft',
  statuses: ApprovalStatuses,
  transitions: [
    { from: 'draft', to: 'pending', action: 'submit' },
    { from: 'pending', to: 'approved', action: 'approve' },
    { from: 'pending', to: 'rejected', action: 'reject' },
    { from: 'rejected', to: 'draft', action: 'revise' },
  ],
  finalStatuses: ['approved'],
});

/**
 * Standard order/task statuses
 */
export const TaskStatuses = ['pending', 'confirmed', 'in_progress', 'completed', 'cancelled'] as const;
export type TaskStatus = typeof TaskStatuses[number];

/**
 * Standard task workflow
 */
export const taskWorkflow = new StatusWorkflow<TaskStatus>({
  initialStatus: 'pending',
  statuses: TaskStatuses,
  transitions: [
    { from: 'pending', to: 'confirmed', action: 'confirm' },
    { from: 'confirmed', to: 'in_progress', action: 'start' },
    { from: 'in_progress', to: 'completed', action: 'complete' },
    { from: ['pending', 'confirmed'], to: 'cancelled', action: 'cancel' },
  ],
  finalStatuses: ['completed', 'cancelled'],
});

/**
 * Reservation statuses
 */
export const ReservationStatuses = ['tentative', 'confirmed', 'active', 'completed', 'cancelled', 'no_show'] as const;
export type ReservationStatus = typeof ReservationStatuses[number];

/**
 * Reservation workflow
 */
export const reservationWorkflow = new StatusWorkflow<ReservationStatus>({
  initialStatus: 'tentative',
  statuses: ReservationStatuses,
  transitions: [
    { from: 'tentative', to: 'confirmed', action: 'confirm' },
    { from: 'confirmed', to: 'active', action: 'check_in' },
    { from: 'active', to: 'completed', action: 'check_out' },
    { from: ['tentative', 'confirmed'], to: 'cancelled', action: 'cancel' },
    { from: 'confirmed', to: 'no_show', action: 'mark_no_show' },
  ],
  finalStatuses: ['completed', 'cancelled', 'no_show'],
});
