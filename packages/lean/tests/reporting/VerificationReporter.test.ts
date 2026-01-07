/**
 * @fileoverview Unit tests for VerificationReporter
 * @module @nahisaho/musubix-lean/tests/reporting/VerificationReporter
 * @traceability REQ-LEAN-FEEDBACK-001 to REQ-LEAN-FEEDBACK-003
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  VerificationReporter,
  type VerificationResultEntry,
  type VerificationStatus,
} from '../../src/reporting/VerificationReporter.ts';
import type { LeanTheorem, ReportFormat } from '../../src/types.ts';

describe('VerificationReporter', () => {
  let reporter: VerificationReporter;

  beforeEach(() => {
    reporter = new VerificationReporter();
  });

  const createTheorem = (id: string = 'THM-001'): LeanTheorem => ({
    id,
    name: `test_theorem_${id}`,
    statement: 'test statement',
    requirementId: `REQ-${id}`,
    hypotheses: [],
    conclusion: { type: 'bool', leanCode: 'true' },
    leanCode: 'theorem test : true := by trivial',
  });

  describe('addResult', () => {
    it('should add verification result', () => {
      const entry: VerificationResultEntry = {
        theorem: createTheorem('001'),
        status: 'proved',
        duration: 100,
      };

      reporter.addResult(entry);
      expect(reporter.getResultCount()).toBe(1);
    });

    it('should add multiple results', () => {
      reporter.addResult({
        theorem: createTheorem('001'),
        status: 'proved',
        duration: 100,
      });

      reporter.addResult({
        theorem: createTheorem('002'),
        status: 'error',
        error: 'Failed',
        duration: 200,
      });

      expect(reporter.getResultCount()).toBe(2);
    });
  });

  describe('generate', () => {
    it('should generate report with statistics', () => {
      reporter.addResult({
        theorem: createTheorem('001'),
        status: 'proved',
        duration: 100,
      });

      reporter.addResult({
        theorem: createTheorem('002'),
        status: 'proved',
        duration: 200,
      });

      const report = reporter.generate();
      expect(report.statistics.totalTheorems).toBe(2);
      expect(report.statistics.provedCount).toBe(2);
      expect(report.statistics.failedCount).toBe(0);
    });

    it('should calculate average proof time', () => {
      reporter.addResult({
        theorem: createTheorem('001'),
        status: 'proved',
        duration: 100,
      });

      reporter.addResult({
        theorem: createTheorem('002'),
        status: 'proved',
        duration: 300,
      });

      const report = reporter.generate();
      expect(report.statistics.averageProofTime).toBe(200);
    });

    it('should count failed proofs', () => {
      reporter.addResult({
        theorem: createTheorem('001'),
        status: 'proved',
        duration: 100,
      });

      reporter.addResult({
        theorem: createTheorem('002'),
        status: 'error',
        error: 'Failed',
        duration: 200,
      });

      reporter.addResult({
        theorem: createTheorem('003'),
        status: 'incomplete',
        duration: 150,
      });

      const report = reporter.generate();
      expect(report.statistics.provedCount).toBe(1);
      expect(report.statistics.failedCount).toBe(1);
      expect(report.statistics.incompleteCount).toBe(1);
    });

    it('should include report id and timestamp', () => {
      reporter.addResult({
        theorem: createTheorem('001'),
        status: 'proved',
        duration: 100,
      });

      const report = reporter.generate();
      expect(report.id).toBeDefined();
      expect(report.id.startsWith('RPT-')).toBe(true);
      expect(report.timestamp).toBeDefined();
    });
  });

  describe('export', () => {
    beforeEach(() => {
      reporter.addResult({
        theorem: createTheorem('001'),
        status: 'proved',
        duration: 100,
      });
    });

    it('should export as JSON', () => {
      const formatted = reporter.export('json');
      expect(() => JSON.parse(formatted)).not.toThrow();
    });

    it('should export as Markdown', () => {
      const formatted = reporter.export('markdown');
      expect(formatted).toContain('#');
      // createTheorem('001') creates a theorem with id='001'
      expect(formatted).toContain('001');
    });

    it('should export as HTML', () => {
      const formatted = reporter.export('html');
      expect(formatted).toContain('<');
      expect(formatted).toContain('</');
      expect(formatted).toContain('html');
    });

    it('should export as CSV', () => {
      const formatted = reporter.export('csv');
      expect(formatted).toContain(',');
      expect(formatted).toContain('Theorem ID');
    });
  });

  describe('clear', () => {
    it('should clear all results', () => {
      reporter.addResult({
        theorem: createTheorem('001'),
        status: 'proved',
        duration: 100,
      });

      expect(reporter.getResultCount()).toBe(1);
      reporter.clear();
      expect(reporter.getResultCount()).toBe(0);
    });
  });

  describe('getResultCount', () => {
    it('should return correct count', () => {
      expect(reporter.getResultCount()).toBe(0);

      reporter.addResult({
        theorem: createTheorem('001'),
        status: 'proved',
        duration: 100,
      });
      expect(reporter.getResultCount()).toBe(1);

      reporter.addResult({
        theorem: createTheorem('002'),
        status: 'error',
        error: 'Failed',
        duration: 200,
      });
      expect(reporter.getResultCount()).toBe(2);
    });
  });

  describe('generateUserFeedback (static)', () => {
    it('should generate feedback for goals', () => {
      const state = {
        goals: [{ id: 0, type: 'a = a', leanCode: 'a = a' }],
        hypotheses: [],
        currentGoal: 0,
      };

      const feedback = VerificationReporter.generateUserFeedback(state, ['simp']);
      expect(feedback.length).toBeGreaterThan(0);
      expect(feedback.some(f => f.includes('rfl') || f.includes('simp'))).toBe(true);
    });

    it('should indicate when all goals are proved', () => {
      const state = {
        goals: [],
        hypotheses: [],
        currentGoal: 0,
      };

      const feedback = VerificationReporter.generateUserFeedback(state, []);
      expect(feedback[0]).toContain('proved');
    });

    it('should list available hypotheses', () => {
      const state = {
        goals: [{ id: 0, type: 'p', leanCode: 'p' }],
        hypotheses: [{ name: 'h', type: 'p', leanCode: 'h : p' }],
        currentGoal: 0,
      };

      const feedback = VerificationReporter.generateUserFeedback(state, []);
      expect(feedback.some(f => f.includes('hypotheses') || f.includes('h'))).toBe(true);
    });
  });
});
