/**
 * Context Analyzer Tests
 *
 * @see REQ-CLARIFY-001 - Evaluate completeness of requirements input
 * @see REQ-CLARIFY-010 - Return clarifying questions when context incomplete
 */

import { describe, it, expect } from 'vitest';
import {
  analyzeContextCompleteness,
  meetsMinimumRequirements,
  formatAnalysisSummary,
  type ClarificationContext,
} from '../context-analyzer.js';

describe('analyzeContextCompleteness', () => {
  describe('complete context', () => {
    it('should return complete when all 5 questions are answered', () => {
      const context: ClarificationContext = {
        purpose: 'Solve login issues',
        targetUser: 'Admin users',
        successState: 'Fast and secure login',
        constraints: 'No password exposure',
        successCriteria: 'Login under 2 seconds',
      };

      const result = analyzeContextCompleteness(context);

      expect(result.level).toBe('complete');
      expect(result.needsClarification).toBe(false);
      expect(result.answeredCount).toBe(5);
      expect(result.totalRequired).toBe(5);
      expect(result.completenessPercent).toBe(100);
      expect(result.missingQuestionIds).toHaveLength(0);
    });
  });

  describe('partial context', () => {
    it('should return partial when 2-4 questions are answered', () => {
      const context: ClarificationContext = {
        purpose: 'Solve login issues',
        targetUser: 'Admin users',
      };

      const result = analyzeContextCompleteness(context);

      expect(result.level).toBe('partial');
      expect(result.needsClarification).toBe(true);
      expect(result.answeredCount).toBe(2);
      expect(result.completenessPercent).toBe(40);
      expect(result.missingQuestionIds).toContain('successState');
      expect(result.missingQuestionIds).toContain('constraints');
      expect(result.missingQuestionIds).toContain('successCriteria');
    });

    it('should return partial when 4 questions are answered', () => {
      const context: ClarificationContext = {
        purpose: 'Solve login issues',
        targetUser: 'Admin users',
        successState: 'Fast login',
        constraints: 'No exposure',
      };

      const result = analyzeContextCompleteness(context);

      expect(result.level).toBe('partial');
      expect(result.answeredCount).toBe(4);
      expect(result.missingQuestionIds).toEqual(['successCriteria']);
    });
  });

  describe('minimal context', () => {
    it('should return minimal when undefined is passed', () => {
      const result = analyzeContextCompleteness(undefined);

      expect(result.level).toBe('minimal');
      expect(result.needsClarification).toBe(true);
      expect(result.answeredCount).toBe(0);
      expect(result.completenessPercent).toBe(0);
      expect(result.missingQuestionIds).toHaveLength(5);
    });

    it('should return minimal when only 1 question is answered', () => {
      const context: ClarificationContext = {
        purpose: 'Solve login issues',
      };

      const result = analyzeContextCompleteness(context);

      expect(result.level).toBe('minimal');
      expect(result.answeredCount).toBe(1);
    });

    it('should return minimal when 0 questions are answered', () => {
      const context: ClarificationContext = {};

      const result = analyzeContextCompleteness(context);

      expect(result.level).toBe('minimal');
      expect(result.answeredCount).toBe(0);
    });
  });

  describe('edge cases', () => {
    it('should treat empty string as unanswered', () => {
      const context: ClarificationContext = {
        purpose: '',
        targetUser: 'Admin users',
      };

      const result = analyzeContextCompleteness(context);

      expect(result.answeredCount).toBe(1);
      expect(result.missingQuestionIds).toContain('purpose');
    });

    it('should treat whitespace-only string as unanswered', () => {
      const context: ClarificationContext = {
        purpose: '   ',
        targetUser: 'Admin users',
      };

      const result = analyzeContextCompleteness(context);

      expect(result.answeredCount).toBe(1);
      expect(result.missingQuestionIds).toContain('purpose');
    });

    it('should include missing questions in result', () => {
      const context: ClarificationContext = {
        purpose: 'Something',
      };

      const result = analyzeContextCompleteness(context);

      expect(result.missingQuestions).toHaveLength(4);
      expect(result.missingQuestions[0]).toHaveProperty('questionJa');
      expect(result.missingQuestions[0]).toHaveProperty('questionEn');
    });
  });
});

describe('meetsMinimumRequirements', () => {
  it('should return true when purpose and targetUser are provided', () => {
    const context: ClarificationContext = {
      purpose: 'Solve issues',
      targetUser: 'Users',
    };

    expect(meetsMinimumRequirements(context)).toBe(true);
  });

  it('should return false when only purpose is provided', () => {
    const context: ClarificationContext = {
      purpose: 'Solve issues',
    };

    expect(meetsMinimumRequirements(context)).toBe(false);
  });

  it('should return false when undefined is passed', () => {
    expect(meetsMinimumRequirements(undefined)).toBe(false);
  });

  it('should return false when purpose is empty', () => {
    const context: ClarificationContext = {
      purpose: '',
      targetUser: 'Users',
    };

    expect(meetsMinimumRequirements(context)).toBe(false);
  });
});

describe('formatAnalysisSummary', () => {
  it('should format complete status correctly', () => {
    const result = analyzeContextCompleteness({
      purpose: 'a',
      targetUser: 'b',
      successState: 'c',
      constraints: 'd',
      successCriteria: 'e',
    });

    const summary = formatAnalysisSummary(result);

    expect(summary).toContain('✅');
    expect(summary).toContain('100%');
    expect(summary).toContain('5/5');
  });

  it('should format partial status correctly', () => {
    const result = analyzeContextCompleteness({
      purpose: 'a',
      targetUser: 'b',
    });

    const summary = formatAnalysisSummary(result);

    expect(summary).toContain('⚠️');
    expect(summary).toContain('40%');
    expect(summary).toContain('2/5');
  });

  it('should format minimal status correctly', () => {
    const result = analyzeContextCompleteness(undefined);

    const summary = formatAnalysisSummary(result);

    expect(summary).toContain('❓');
    expect(summary).toContain('0%');
    expect(summary).toContain('0/5');
  });
});
