/**
 * Task Status Tests
 * 
 * @see TSK-PM-001 - Value Objects実装
 * @see BP-TEST-005 - Status Transition Testing
 */

import { describe, it, expect } from 'vitest';
import {
  type TaskStatus,
  validTaskStatusTransitions,
  isValidTaskStatusTransition,
  getAvailableTaskStatuses,
} from '../../../src/domain/value-objects/task-status.js';

describe('TaskStatus', () => {
  describe('validTaskStatusTransitions', () => {
    it('should define all status transitions', () => {
      const statuses: TaskStatus[] = ['backlog', 'todo', 'inProgress', 'review', 'done'];
      statuses.forEach(status => {
        expect(validTaskStatusTransitions[status]).toBeDefined();
      });
    });

    it('should have done as terminal state', () => {
      expect(validTaskStatusTransitions.done).toEqual([]);
    });
  });

  describe('isValidTaskStatusTransition', () => {
    // Valid Kanban flow
    it('should allow backlog → todo', () => {
      expect(isValidTaskStatusTransition('backlog', 'todo')).toBe(true);
    });

    it('should allow todo → inProgress', () => {
      expect(isValidTaskStatusTransition('todo', 'inProgress')).toBe(true);
    });

    it('should allow inProgress → review', () => {
      expect(isValidTaskStatusTransition('inProgress', 'review')).toBe(true);
    });

    it('should allow review → done', () => {
      expect(isValidTaskStatusTransition('review', 'done')).toBe(true);
    });

    // Backward flow (return for rework)
    it('should allow todo → backlog (move back)', () => {
      expect(isValidTaskStatusTransition('todo', 'backlog')).toBe(true);
    });

    it('should allow inProgress → todo (unassign)', () => {
      expect(isValidTaskStatusTransition('inProgress', 'todo')).toBe(true);
    });

    it('should allow review → inProgress (rework)', () => {
      expect(isValidTaskStatusTransition('review', 'inProgress')).toBe(true);
    });

    // Invalid transitions
    it('should reject backlog → done (must go through workflow)', () => {
      expect(isValidTaskStatusTransition('backlog', 'done')).toBe(false);
    });

    it('should reject done → anything (terminal state)', () => {
      expect(isValidTaskStatusTransition('done', 'todo')).toBe(false);
      expect(isValidTaskStatusTransition('done', 'inProgress')).toBe(false);
    });
  });

  describe('getAvailableTaskStatuses', () => {
    it('should return correct options for inProgress', () => {
      expect(getAvailableTaskStatuses('inProgress')).toEqual(['review', 'todo']);
    });

    it('should return empty array for done', () => {
      expect(getAvailableTaskStatuses('done')).toEqual([]);
    });
  });
});
