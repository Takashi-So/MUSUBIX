/**
 * Project Status Tests
 * 
 * @see TSK-PM-001 - Value Objects実装
 * @see BP-TEST-005 - Status Transition Testing
 */

import { describe, it, expect } from 'vitest';
import {
  type ProjectStatus,
  validProjectStatusTransitions,
  isValidProjectStatusTransition,
  getAvailableProjectStatuses,
} from '../../../src/domain/value-objects/project-status.js';

describe('ProjectStatus', () => {
  describe('validProjectStatusTransitions', () => {
    it('should define all status transitions', () => {
      const statuses: ProjectStatus[] = ['planning', 'active', 'onHold', 'completed', 'archived'];
      statuses.forEach(status => {
        expect(validProjectStatusTransitions[status]).toBeDefined();
      });
    });

    it('should have archived as terminal state', () => {
      expect(validProjectStatusTransitions.archived).toEqual([]);
    });
  });

  describe('isValidProjectStatusTransition', () => {
    // Valid transitions
    it('should allow planning → active', () => {
      expect(isValidProjectStatusTransition('planning', 'active')).toBe(true);
    });

    it('should allow active → completed', () => {
      expect(isValidProjectStatusTransition('active', 'completed')).toBe(true);
    });

    it('should allow active → onHold', () => {
      expect(isValidProjectStatusTransition('active', 'onHold')).toBe(true);
    });

    it('should allow onHold → active (resume)', () => {
      expect(isValidProjectStatusTransition('onHold', 'active')).toBe(true);
    });

    // Invalid transitions
    it('should reject planning → completed (must go through active)', () => {
      expect(isValidProjectStatusTransition('planning', 'completed')).toBe(false);
    });

    it('should reject completed → active (no un-complete)', () => {
      expect(isValidProjectStatusTransition('completed', 'active')).toBe(false);
    });

    it('should reject archived → anything (terminal state)', () => {
      expect(isValidProjectStatusTransition('archived', 'active')).toBe(false);
      expect(isValidProjectStatusTransition('archived', 'planning')).toBe(false);
    });
  });

  describe('getAvailableProjectStatuses', () => {
    it('should return correct options for planning', () => {
      expect(getAvailableProjectStatuses('planning')).toEqual(['active', 'archived']);
    });

    it('should return empty array for archived', () => {
      expect(getAvailableProjectStatuses('archived')).toEqual([]);
    });
  });
});
