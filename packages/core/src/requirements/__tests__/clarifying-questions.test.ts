/**
 * Tests for clarifying-questions.ts
 *
 * @see TSK-002-04 - Unit tests for getMissingQuestions overloads
 * @see REQ-BUGFIX-002-01〜04
 */

import { describe, it, expect } from 'vitest';
import {
  getMissingQuestions,
  CORE_QUESTIONS,
  getAllQuestionIds,
} from '../clarifying-questions.js';

describe('getMissingQuestions', () => {
  describe('TSK-002-01: no arguments (undefined)', () => {
    it('should return all questions when called with no arguments', () => {
      const result = getMissingQuestions();
      expect(result).toHaveLength(CORE_QUESTIONS.length);
      expect(result).toEqual([...CORE_QUESTIONS]);
    });

    it('should return all questions when called with undefined', () => {
      const result = getMissingQuestions(undefined);
      expect(result).toHaveLength(CORE_QUESTIONS.length);
    });
  });

  describe('TSK-002-02: string array input', () => {
    it('should filter questions by IDs', () => {
      const result = getMissingQuestions(['purpose', 'constraints']);
      expect(result).toHaveLength(2);
      expect(result.map(q => q.id)).toEqual(['purpose', 'constraints']);
    });

    it('should return all questions for empty array', () => {
      const result = getMissingQuestions([]);
      expect(result).toHaveLength(CORE_QUESTIONS.length);
    });

    it('should return empty array for non-matching IDs', () => {
      const result = getMissingQuestions(['nonexistent']);
      expect(result).toHaveLength(0);
    });

    it('should return correct questions for all valid IDs', () => {
      const allIds = getAllQuestionIds();
      const result = getMissingQuestions(allIds);
      expect(result).toHaveLength(allIds.length);
    });
  });

  describe('TSK-002-02: context object input', () => {
    it('should return missing questions for partial context', () => {
      const result = getMissingQuestions({
        purpose: 'solve X',
        targetUser: 'developers',
      });
      // 3 questions should be missing: successState, constraints, successCriteria
      expect(result).toHaveLength(3);
      expect(result.map(q => q.id)).toContain('successState');
      expect(result.map(q => q.id)).toContain('constraints');
      expect(result.map(q => q.id)).toContain('successCriteria');
    });

    it('should return all questions for empty context', () => {
      const result = getMissingQuestions({});
      expect(result).toHaveLength(CORE_QUESTIONS.length);
    });

    it('should return no questions for complete context', () => {
      const result = getMissingQuestions({
        purpose: 'solve X',
        targetUser: 'developers',
        successState: 'feature works',
        constraints: 'no security issues',
        successCriteria: '100% test pass',
      });
      expect(result).toHaveLength(0);
    });

    it('should ignore empty string values', () => {
      const result = getMissingQuestions({
        purpose: '   ',
        targetUser: '',
        successState: 'feature works',
      });
      // purpose and targetUser are empty, constraints and successCriteria undefined
      expect(result).toHaveLength(4);
    });
  });

  describe('TSK-002-03: error handling', () => {
    it('should throw TypeError for invalid input type (number)', () => {
      expect(() => getMissingQuestions(123 as unknown as string[])).toThrow(TypeError);
    });

    it('should throw TypeError for null', () => {
      expect(() => getMissingQuestions(null as unknown as string[])).toThrow(TypeError);
    });

    it('should provide descriptive error message', () => {
      try {
        getMissingQuestions(123 as unknown as string[]);
      } catch (e) {
        expect((e as Error).message).toContain('getMissingQuestions');
        expect((e as Error).message).toContain('Expected');
        expect((e as Error).message).toContain('number');
      }
    });
  });
});
