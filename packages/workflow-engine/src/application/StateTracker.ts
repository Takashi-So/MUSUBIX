/**
 * StateTracker - Application Service
 * 
 * Tracks and persists workflow state
 * 
 * @see TSK-WORKFLOW-002 - StateTracker
 * @see REQ-ORCH-002 - State Tracking
 * @see DES-ORCH-002 - StateTracker Component
 */

import type {
  Workflow,
  WorkflowStatus,
  PhaseType,
} from '../domain/index.js';
import { getWorkflowProgress } from '../domain/entities/Workflow.js';

/**
 * State snapshot
 */
export interface StateSnapshot {
  readonly workflowId: string;
  readonly status: WorkflowStatus;
  readonly currentPhase: PhaseType | null;
  readonly progress: number;
  readonly phaseStatuses: Record<PhaseType, string>;
  readonly timestamp: Date;
}

/**
 * State change event
 */
export interface StateChangeEvent {
  readonly type: 'state-change';
  readonly workflowId: string;
  readonly previousState: StateSnapshot;
  readonly currentState: StateSnapshot;
  readonly timestamp: Date;
}

/**
 * State listener function
 */
export type StateListener = (event: StateChangeEvent) => void;

/**
 * State Tracker
 * 
 * Tracks workflow state and emits change events
 */
export class StateTracker {
  private snapshots: Map<string, StateSnapshot[]> = new Map();
  private listeners: Set<StateListener> = new Set();

  /**
   * Take a snapshot of workflow state
   * 
   * @param workflow - Workflow to snapshot
   * @returns State snapshot
   */
  snapshot(workflow: Workflow): StateSnapshot {
    const phaseStatuses: Record<PhaseType, string> = {} as Record<PhaseType, string>;
    
    for (const [phaseType, phase] of workflow.phases) {
      phaseStatuses[phaseType] = phase.status;
    }
    
    const snapshot: StateSnapshot = Object.freeze({
      workflowId: workflow.id,
      status: workflow.status,
      currentPhase: workflow.currentPhase,
      progress: getWorkflowProgress(workflow),
      phaseStatuses,
      timestamp: new Date(),
    });
    
    // Store snapshot
    const history = this.snapshots.get(workflow.id) ?? [];
    
    // Check for state change
    const lastSnapshot = history[history.length - 1];
    if (lastSnapshot && this.hasStateChanged(lastSnapshot, snapshot)) {
      this.emitStateChange(workflow.id, lastSnapshot, snapshot);
    }
    
    history.push(snapshot);
    this.snapshots.set(workflow.id, history);
    
    return snapshot;
  }

  /**
   * Get latest snapshot for a workflow
   * 
   * @param workflowId - Workflow ID
   * @returns Latest snapshot or undefined
   */
  getLatestSnapshot(workflowId: string): StateSnapshot | undefined {
    const history = this.snapshots.get(workflowId);
    return history?.[history.length - 1];
  }

  /**
   * Get snapshot history for a workflow
   * 
   * @param workflowId - Workflow ID
   * @returns Snapshot history
   */
  getHistory(workflowId: string): readonly StateSnapshot[] {
    return this.snapshots.get(workflowId) ?? [];
  }

  /**
   * Subscribe to state changes
   * 
   * @param listener - State listener
   * @returns Unsubscribe function
   */
  subscribe(listener: StateListener): () => void {
    this.listeners.add(listener);
    return () => this.listeners.delete(listener);
  }

  /**
   * Check if state has changed
   * 
   * @param previous - Previous snapshot
   * @param current - Current snapshot
   * @returns true if changed
   */
  private hasStateChanged(previous: StateSnapshot, current: StateSnapshot): boolean {
    if (previous.status !== current.status) return true;
    if (previous.currentPhase !== current.currentPhase) return true;
    if (previous.progress !== current.progress) return true;
    
    for (const phase of Object.keys(previous.phaseStatuses) as PhaseType[]) {
      if (previous.phaseStatuses[phase] !== current.phaseStatuses[phase]) {
        return true;
      }
    }
    
    return false;
  }

  /**
   * Emit state change event
   * 
   * @param workflowId - Workflow ID
   * @param previous - Previous state
   * @param current - Current state
   */
  private emitStateChange(
    workflowId: string,
    previous: StateSnapshot,
    current: StateSnapshot
  ): void {
    const event: StateChangeEvent = {
      type: 'state-change',
      workflowId,
      previousState: previous,
      currentState: current,
      timestamp: new Date(),
    };
    
    for (const listener of this.listeners) {
      try {
        listener(event);
      } catch (error) {
        console.error('State listener error:', error);
      }
    }
  }

  /**
   * Format state as display string
   * 
   * @param snapshot - State snapshot
   * @returns Formatted string
   */
  formatState(snapshot: StateSnapshot): string {
    const lines = [
      `📊 **Workflow State**: ${snapshot.workflowId}`,
      '',
      `- Status: ${snapshot.status}`,
      `- Current Phase: ${snapshot.currentPhase ?? 'N/A'}`,
      `- Progress: ${snapshot.progress}%`,
      '',
      '**Phase Status:**',
    ];
    
    const phaseOrder: PhaseType[] = [
      'requirements',
      'design',
      'task-breakdown',
      'implementation',
      'completion',
    ];
    
    for (const phase of phaseOrder) {
      const status = snapshot.phaseStatuses[phase];
      const emoji = this.getStatusEmoji(status);
      lines.push(`- ${phase}: ${emoji} ${status}`);
    }
    
    return lines.join('\n');
  }

  /**
   * Get emoji for status
   * 
   * @param status - Phase status
   * @returns Emoji
   */
  private getStatusEmoji(status: string): string {
    switch (status) {
      case 'pending': return '⬜';
      case 'in-progress': return '🔄';
      case 'completed': return '✅';
      case 'approved': return '✅✅';
      default: return '❓';
    }
  }

  /**
   * Clear history for a workflow
   * 
   * @param workflowId - Workflow ID
   */
  clearHistory(workflowId: string): void {
    this.snapshots.delete(workflowId);
  }

  /**
   * Clear all tracking data
   */
  clearAll(): void {
    this.snapshots.clear();
    this.listeners.clear();
  }
}

/**
 * Create a state tracker instance
 * 
 * @returns StateTracker instance
 */
export function createStateTracker(): StateTracker {
  return new StateTracker();
}
