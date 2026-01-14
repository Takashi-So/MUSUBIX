/**
 * Context Analyzer for Requirements Clarification
 *
 * @module requirements/context-analyzer
 * @description
 * Analyzes the completeness of requirements context and determines
 * whether clarification questions are needed before proceeding.
 *
 * @requirements
 * - REQ-CLARIFY-001: Evaluate completeness of requirements input
 * - REQ-CLARIFY-010: Return clarifying questions when context incomplete
 * - REQ-CLARIFY-020: Continue prompting while context incomplete
 * - REQ-CLARIFY-040: Do not generate requirements without minimum context
 */

import {
  type QuestionId,
  CORE_QUESTIONS,
  getMissingQuestions,
  type ClarifyingQuestion,
} from './clarifying-questions.js';

/**
 * Context provided by user for requirements gathering
 */
export interface ClarificationContext {
  /** WHY - The real problem being solved */
  purpose?: string;
  /** WHO - The target user */
  targetUser?: string;
  /** WHAT-IF - The success scenario */
  successState?: string;
  /** CONSTRAINT - What must NOT happen */
  constraints?: string;
  /** SUCCESS - Measurable success criteria */
  successCriteria?: string;
}

/**
 * Completeness level of the provided context
 *
 * - complete: All 5 core questions answered (can proceed)
 * - partial: 2-4 questions answered (need more info)
 * - minimal: 0-1 questions answered (need full hearing)
 */
export type CompletenessLevel = 'complete' | 'partial' | 'minimal';

/**
 * Result of context analysis
 */
export interface ContextAnalysisResult {
  /** Overall completeness level */
  level: CompletenessLevel;
  /** Number of questions answered */
  answeredCount: number;
  /** Total number of required questions */
  totalRequired: number;
  /** IDs of questions that haven't been answered */
  missingQuestionIds: QuestionId[];
  /** Full question objects for missing questions */
  missingQuestions: ClarifyingQuestion[];
  /** Whether clarification is needed */
  needsClarification: boolean;
  /** Completeness as percentage */
  completenessPercent: number;
}

/**
 * Check if a context value is considered "answered"
 * Empty strings and whitespace-only strings are not considered answers
 */
function isAnswered(value: string | undefined): boolean {
  return value !== undefined && value.trim().length > 0;
}

/**
 * Analyze the completeness of provided context
 *
 * @param context - The clarification context (may be undefined)
 * @returns Analysis result with completeness level and missing questions
 *
 * @example
 * ```typescript
 * // Minimal context - need all questions
 * const result1 = analyzeContextCompleteness(undefined);
 * // result1.level === 'minimal', result1.needsClarification === true
 *
 * // Partial context
 * const result2 = analyzeContextCompleteness({
 *   purpose: 'Solve login issues',
 *   targetUser: 'Admin users',
 * });
 * // result2.level === 'partial', result2.missingQuestionIds.length === 3
 *
 * // Complete context
 * const result3 = analyzeContextCompleteness({
 *   purpose: 'Solve login issues',
 *   targetUser: 'Admin users',
 *   successState: 'Fast login',
 *   constraints: 'No password exposure',
 *   successCriteria: 'Login under 2 seconds',
 * });
 * // result3.level === 'complete', result3.needsClarification === false
 * ```
 */
export function analyzeContextCompleteness(
  context: ClarificationContext | undefined
): ContextAnalysisResult {
  const totalRequired = CORE_QUESTIONS.filter((q) => q.required).length;

  // Handle undefined context
  if (!context) {
    const allIds = CORE_QUESTIONS.map((q) => q.id);
    return {
      level: 'minimal',
      answeredCount: 0,
      totalRequired,
      missingQuestionIds: allIds,
      missingQuestions: getMissingQuestions(allIds),
      needsClarification: true,
      completenessPercent: 0,
    };
  }

  // Check which questions are answered
  const answered: QuestionId[] = [];
  const missing: QuestionId[] = [];

  for (const question of CORE_QUESTIONS) {
    const value = context[question.id];
    if (isAnswered(value)) {
      answered.push(question.id);
    } else {
      missing.push(question.id);
    }
  }

  const answeredCount = answered.length;
  const completenessPercent = Math.round((answeredCount / totalRequired) * 100);

  // Determine completeness level
  let level: CompletenessLevel;
  if (answeredCount >= totalRequired) {
    level = 'complete';
  } else if (answeredCount >= 2) {
    level = 'partial';
  } else {
    level = 'minimal';
  }

  return {
    level,
    answeredCount,
    totalRequired,
    missingQuestionIds: missing,
    missingQuestions: getMissingQuestions(missing),
    needsClarification: level !== 'complete',
    completenessPercent,
  };
}

/**
 * Check if context meets minimum requirements for proceeding
 * At minimum, purpose and targetUser must be provided
 *
 * @param context - The clarification context
 * @returns true if minimum requirements met
 *
 * @requirements
 * - REQ-CLARIFY-040: Do not generate without purpose and targetUser
 */
export function meetsMinimumRequirements(
  context: ClarificationContext | undefined
): boolean {
  if (!context) return false;
  return isAnswered(context.purpose) && isAnswered(context.targetUser);
}

/**
 * Create a summary of the analysis for display
 */
export function formatAnalysisSummary(result: ContextAnalysisResult): string {
  const status =
    result.level === 'complete'
      ? '✅ コンテキスト完了'
      : result.level === 'partial'
        ? '⚠️ 追加情報が必要'
        : '❓ ヒアリングが必要';

  return `${status} (${result.completenessPercent}% - ${result.answeredCount}/${result.totalRequired}問)`;
}
