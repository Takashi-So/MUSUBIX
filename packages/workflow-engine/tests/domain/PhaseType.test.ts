/**
 * PhaseType Value Object Tests
 * 
 * @see REQ-ORCH-001 - Phase Transition
 * @see DES-ORCH-001 - PhaseController
 */

import { describe, it, expect } from 'vitest';
import {
  type PhaseType,
  PHASES,
  getPhaseMetadata,
  isValidTransition,
  getAllPhases,
  getPhaseNumber,
  getValidTransitions,
} from '../../src/domain/value-objects/PhaseType.js';

describe('PhaseType', () => {
  describe('getAllPhases', () => {
    it('should return all 5 phases in order', () => {
      const phases = getAllPhases();
      expect(phases).toHaveLength(5);
      expect(phases).toEqual([
        'requirements',
        'design',
        'task-breakdown',
        'implementation',
        'completion',
      ]);
    });
  });

  describe('getPhaseMetadata', () => {
    it('should return correct metadata for requirements phase', () => {
      const meta = getPhaseMetadata('requirements');
      expect(meta.label).toBe('Phase 1: 要件定義');
      expect(meta.number).toBe(1);
    });

    it('should return correct metadata for design phase', () => {
      const meta = getPhaseMetadata('design');
      expect(meta.label).toBe('Phase 2: 設計');
      expect(meta.number).toBe(2);
    });

    it('should return correct metadata for task-breakdown phase', () => {
      const meta = getPhaseMetadata('task-breakdown');
      expect(meta.label).toBe('Phase 3: タスク分解');
      expect(meta.number).toBe(3);
    });

    it('should return correct metadata for implementation phase', () => {
      const meta = getPhaseMetadata('implementation');
      expect(meta.label).toBe('Phase 4: 実装');
      expect(meta.number).toBe(4);
    });

    it('should return correct metadata for completion phase', () => {
      const meta = getPhaseMetadata('completion');
      expect(meta.label).toBe('Phase 5: 完了');
      expect(meta.number).toBe(5);
    });
  });

  describe('isValidTransition', () => {
    // Valid transitions
    it('should allow requirements -> design transition', () => {
      expect(isValidTransition('requirements', 'design')).toBe(true);
    });

    it('should allow design -> task-breakdown transition', () => {
      expect(isValidTransition('design', 'task-breakdown')).toBe(true);
    });

    it('should allow task-breakdown -> implementation transition', () => {
      expect(isValidTransition('task-breakdown', 'implementation')).toBe(true);
    });

    it('should allow implementation -> completion transition', () => {
      expect(isValidTransition('implementation', 'completion')).toBe(true);
    });

    // CRITICAL: Prohibited transition
    it('should PROHIBIT design -> implementation direct transition', () => {
      // This is the key rule from AGENTS.md
      expect(isValidTransition('design', 'implementation')).toBe(false);
    });

    // Invalid transitions (backwards)
    it('should not allow backwards transitions', () => {
      expect(isValidTransition('design', 'requirements')).toBe(false);
      expect(isValidTransition('completion', 'implementation')).toBe(false);
    });

    // Invalid transitions (skipping)
    it('should not allow skipping phases', () => {
      expect(isValidTransition('requirements', 'task-breakdown')).toBe(false);
      expect(isValidTransition('requirements', 'implementation')).toBe(false);
    });
  });

  describe('getPhaseNumber', () => {
    it('should return correct number for each phase', () => {
      expect(getPhaseNumber('requirements')).toBe(1);
      expect(getPhaseNumber('design')).toBe(2);
      expect(getPhaseNumber('task-breakdown')).toBe(3);
      expect(getPhaseNumber('implementation')).toBe(4);
      expect(getPhaseNumber('completion')).toBe(5);
    });
  });

  describe('getValidTransitions', () => {
    it('should return design as valid transition from requirements', () => {
      const valid = getValidTransitions('requirements');
      expect(valid).toContain('design');
      expect(valid).toHaveLength(1);
    });

    it('should return task-breakdown as valid transition from design', () => {
      const valid = getValidTransitions('design');
      expect(valid).toContain('task-breakdown');
      expect(valid).not.toContain('implementation'); // Prohibited!
    });

    it('should return empty array for completion phase', () => {
      const valid = getValidTransitions('completion');
      expect(valid).toHaveLength(0);
    });
  });

  describe('PHASES constant', () => {
    it('should have metadata for all phases', () => {
      expect(PHASES.size).toBe(5);
      expect(PHASES.has('requirements')).toBe(true);
      expect(PHASES.has('design')).toBe(true);
      expect(PHASES.has('task-breakdown')).toBe(true);
      expect(PHASES.has('implementation')).toBe(true);
      expect(PHASES.has('completion')).toBe(true);
    });
  });
});
