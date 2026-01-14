/**
 * Clarifying Questions for Requirements Gathering
 *
 * @module requirements/clarifying-questions
 * @description
 * Defines the core questions used to gather context when requirements
 * information is incomplete. These questions are used by both CLI
 * interactive hearing and MCP tool clarification flow.
 *
 * @requirements
 * - REQ-CLARIFY-002: Define 5 core questions (WHY, WHO, WHAT-IF, CONSTRAINT, SUCCESS)
 * - REQ-CLARIFY-003: Return questions in structured format for AI agents
 */

/**
 * Question identifier type
 */
export type QuestionId =
  | 'purpose'
  | 'targetUser'
  | 'successState'
  | 'constraints'
  | 'successCriteria';

/**
 * Clarifying question definition
 */
export interface ClarifyingQuestion {
  /** Unique identifier for the question */
  id: QuestionId;
  /** Question text in Japanese */
  questionJa: string;
  /** Question text in English */
  questionEn: string;
  /** Whether this question is required for complete context */
  required: boolean;
  /** Optional follow-up question */
  followUp?: string;
  /** Category/aspect this question addresses */
  aspect: 'WHY' | 'WHO' | 'WHAT-IF' | 'CONSTRAINT' | 'SUCCESS';
}

/**
 * The 5 core questions for requirements gathering
 *
 * These questions are designed to capture essential context:
 * 1. WHY - The real problem being solved
 * 2. WHO - The target user
 * 3. WHAT-IF - The success scenario
 * 4. CONSTRAINT - What must NOT happen
 * 5. SUCCESS - Measurable success criteria
 */
export const CORE_QUESTIONS: readonly ClarifyingQuestion[] = [
  {
    id: 'purpose',
    aspect: 'WHY',
    questionJa: 'この機能で解決したい「本当の課題」は何ですか？',
    questionEn: 'What is the TRUE problem you want to solve with this feature?',
    required: true,
    followUp: '具体的なシナリオがあれば教えてください。',
  },
  {
    id: 'targetUser',
    aspect: 'WHO',
    questionJa: 'この機能を最も必要としているのは誰ですか？（ユーザー種別）',
    questionEn: 'Who needs this feature the most? (user type)',
    required: true,
    followUp: 'そのユーザーの技術レベルは？',
  },
  {
    id: 'successState',
    aspect: 'WHAT-IF',
    questionJa: 'もしこの機能が完璧に動作したら、何が変わりますか？',
    questionEn: 'If this feature works perfectly, what changes?',
    required: true,
  },
  {
    id: 'constraints',
    aspect: 'CONSTRAINT',
    questionJa: 'この機能で「絶対にやってはいけないこと」はありますか？',
    questionEn: 'Are there any things this feature must NEVER do?',
    required: true,
    followUp: 'セキュリティやパフォーマンスの制約は？',
  },
  {
    id: 'successCriteria',
    aspect: 'SUCCESS',
    questionJa: 'この機能が「成功した」と言えるのはどんな状態ですか？',
    questionEn: 'What state indicates this feature is "successful"?',
    required: true,
    followUp: '測定可能な指標はありますか？',
  },
] as const;

/**
 * Get questions that haven't been answered yet
 *
 * @param missingIds - Array of question IDs that are missing
 * @returns Array of ClarifyingQuestion objects for the missing questions
 *
 * @example
 * ```typescript
 * const missing = getMissingQuestions(['purpose', 'constraints']);
 * // Returns questions for 'purpose' and 'constraints'
 * ```
 */
export function getMissingQuestions(
  missingIds: readonly string[]
): ClarifyingQuestion[] {
  return CORE_QUESTIONS.filter((q) => missingIds.includes(q.id));
}

/**
 * Get all question IDs
 */
export function getAllQuestionIds(): QuestionId[] {
  return CORE_QUESTIONS.map((q) => q.id);
}

/**
 * Get the total number of required questions
 */
export function getRequiredQuestionCount(): number {
  return CORE_QUESTIONS.filter((q) => q.required).length;
}

/**
 * Format questions for display to user
 *
 * @param questions - Questions to format
 * @param locale - 'ja' for Japanese, 'en' for English
 * @returns Formatted string for display
 */
export function formatQuestionsForDisplay(
  questions: readonly ClarifyingQuestion[],
  locale: 'ja' | 'en' = 'ja'
): string {
  const header =
    locale === 'ja'
      ? '📋 要件を明確にするため、いくつか質問させてください：\n'
      : '📋 Let me ask a few questions to clarify the requirements:\n';

  const questionList = questions
    .map((q, i) => {
      const text = locale === 'ja' ? q.questionJa : q.questionEn;
      return `${i + 1}. ${text}`;
    })
    .join('\n');

  return `${header}\n${questionList}`;
}
