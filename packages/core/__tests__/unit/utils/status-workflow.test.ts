/**
 * Status Workflow Tests
 * 
 * @description Tests for the status workflow utility discovered from 10-project validation
 */
import { describe, it, expect } from 'vitest';
import { 
  StatusWorkflow,
  approvalWorkflow,
  taskWorkflow,
  reservationWorkflow,
  type TaskStatus,
} from '../../../src/utils/status-workflow.js';

describe('StatusWorkflow', () => {
  describe('constructor', () => {
    it('should create workflow with valid config', () => {
      const workflow = new StatusWorkflow({
        initialStatus: 'draft',
        statuses: ['draft', 'published'] as const,
        transitions: [{ from: 'draft', to: 'published', action: 'publish' }],
      });

      expect(workflow.getInitialStatus()).toBe('draft');
    });

    it('should throw error if initial status not in statuses', () => {
      expect(() => {
        new StatusWorkflow({
          initialStatus: 'invalid' as any,
          statuses: ['draft', 'published'] as const,
          transitions: [],
        });
      }).toThrow("Initial status 'invalid' is not in statuses list");
    });

    it('should throw error if transition from status not in statuses', () => {
      expect(() => {
        new StatusWorkflow({
          initialStatus: 'draft',
          statuses: ['draft', 'published'] as const,
          transitions: [{ from: 'invalid' as any, to: 'published', action: 'publish' }],
        });
      }).toThrow("Transition 'from' status 'invalid' is not in statuses list");
    });

    it('should throw error if transition to status not in statuses', () => {
      expect(() => {
        new StatusWorkflow({
          initialStatus: 'draft',
          statuses: ['draft', 'published'] as const,
          transitions: [{ from: 'draft', to: 'invalid' as any, action: 'publish' }],
        });
      }).toThrow("Transition 'to' status 'invalid' is not in statuses list");
    });
  });

  describe('transition()', () => {
    const workflow = new StatusWorkflow<TaskStatus>({
      initialStatus: 'pending',
      statuses: ['pending', 'confirmed', 'in_progress', 'completed', 'cancelled'],
      transitions: [
        { from: 'pending', to: 'confirmed', action: 'confirm' },
        { from: 'confirmed', to: 'in_progress', action: 'start' },
        { from: 'in_progress', to: 'completed', action: 'complete' },
        { from: ['pending', 'confirmed'], to: 'cancelled', action: 'cancel' },
      ],
      finalStatuses: ['completed', 'cancelled'],
    });

    it('should transition to next status', () => {
      expect(workflow.transition('pending', 'confirm')).toBe('confirmed');
      expect(workflow.transition('confirmed', 'start')).toBe('in_progress');
      expect(workflow.transition('in_progress', 'complete')).toBe('completed');
    });

    it('should allow transitions from multiple statuses', () => {
      expect(workflow.transition('pending', 'cancel')).toBe('cancelled');
      expect(workflow.transition('confirmed', 'cancel')).toBe('cancelled');
    });

    it('should throw error for invalid transition', () => {
      expect(() => workflow.transition('pending', 'complete'))
        .toThrow("Invalid transition: cannot perform 'complete' from status 'pending'");
    });

    it('should throw error for non-existent action', () => {
      expect(() => workflow.transition('pending', 'invalid'))
        .toThrow("Invalid transition: cannot perform 'invalid' from status 'pending'");
    });
  });

  describe('canTransition()', () => {
    const workflow = taskWorkflow;

    it('should return true for valid transitions', () => {
      expect(workflow.canTransition('pending', 'confirm')).toBe(true);
      expect(workflow.canTransition('pending', 'cancel')).toBe(true);
    });

    it('should return false for invalid transitions', () => {
      expect(workflow.canTransition('pending', 'complete')).toBe(false);
      expect(workflow.canTransition('completed', 'start')).toBe(false);
    });
  });

  describe('getAvailableActions()', () => {
    it('should return available actions from current status', () => {
      const actions = taskWorkflow.getAvailableActions('pending');
      expect(actions).toContain('confirm');
      expect(actions).toContain('cancel');
      expect(actions).not.toContain('complete');
    });

    it('should return empty array for final status', () => {
      const actions = taskWorkflow.getAvailableActions('completed');
      expect(actions).toHaveLength(0);
    });
  });

  describe('getPossibleNextStatuses()', () => {
    it('should return possible next statuses', () => {
      const next = taskWorkflow.getPossibleNextStatuses('pending');
      expect(next).toContain('confirmed');
      expect(next).toContain('cancelled');
    });
  });

  describe('isFinalStatus()', () => {
    it('should identify final statuses', () => {
      expect(taskWorkflow.isFinalStatus('completed')).toBe(true);
      expect(taskWorkflow.isFinalStatus('cancelled')).toBe(true);
      expect(taskWorkflow.isFinalStatus('pending')).toBe(false);
    });
  });

  describe('guard conditions', () => {
    it('should respect guard conditions', () => {
      let canPublish = false;

      const workflow = new StatusWorkflow({
        initialStatus: 'draft',
        statuses: ['draft', 'published'] as const,
        transitions: [
          { from: 'draft', to: 'published', action: 'publish', guard: () => canPublish },
        ],
      });

      expect(workflow.canTransition('draft', 'publish')).toBe(false);
      
      canPublish = true;
      expect(workflow.canTransition('draft', 'publish')).toBe(true);
    });
  });
});

describe('Pre-defined Workflows', () => {
  describe('approvalWorkflow', () => {
    it('should follow approval flow', () => {
      expect(approvalWorkflow.getInitialStatus()).toBe('draft');
      expect(approvalWorkflow.transition('draft', 'submit')).toBe('pending');
      expect(approvalWorkflow.transition('pending', 'approve')).toBe('approved');
    });

    it('should allow revision after rejection', () => {
      expect(approvalWorkflow.transition('pending', 'reject')).toBe('rejected');
      expect(approvalWorkflow.transition('rejected', 'revise')).toBe('draft');
    });
  });

  describe('taskWorkflow', () => {
    it('should follow task flow', () => {
      expect(taskWorkflow.getInitialStatus()).toBe('pending');
      let status: TaskStatus = 'pending';
      
      status = taskWorkflow.transition(status, 'confirm');
      expect(status).toBe('confirmed');
      
      status = taskWorkflow.transition(status, 'start');
      expect(status).toBe('in_progress');
      
      status = taskWorkflow.transition(status, 'complete');
      expect(status).toBe('completed');
    });
  });

  describe('reservationWorkflow', () => {
    it('should follow reservation flow', () => {
      expect(reservationWorkflow.getInitialStatus()).toBe('tentative');
      expect(reservationWorkflow.transition('tentative', 'confirm')).toBe('confirmed');
      expect(reservationWorkflow.transition('confirmed', 'check_in')).toBe('active');
      expect(reservationWorkflow.transition('active', 'check_out')).toBe('completed');
    });

    it('should handle no-show', () => {
      expect(reservationWorkflow.transition('confirmed', 'mark_no_show')).toBe('no_show');
    });
  });
});
