/**
 * Quiz Entity
 * Traceability: REQ-ELEARN-001-F040, DES-ELEARN-001 §4.1.6
 */

import type { Quiz, CreateQuizInput, QuizId, Question } from './types.js';

// ID counter for testing (BP-TEST-001: Test Counter Reset)
let quizCounter = 0;

/**
 * Reset quiz counter for testing
 */
export function resetQuizCounter(): void {
  quizCounter = 0;
}

/**
 * Generate quiz ID (BP-CODE-002: Date-based ID Format)
 * Format: QIZ-YYYYMMDD-NNN
 */
function generateQuizId(): QuizId {
  const now = new Date();
  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, '');
  quizCounter++;
  const counter = String(quizCounter).padStart(3, '0');
  return `QIZ-${dateStr}-${counter}` as QuizId;
}

/**
 * Validate question
 */
function validateQuestion(question: Question, index: number): void {
  if (!question.text || question.text.trim().length === 0) {
    throw new Error(`Question ${index + 1}: Text is required`);
  }
  if (!question.options || question.options.length < 2) {
    throw new Error(`Question ${index + 1}: At least 2 options are required`);
  }
  if (!question.correctAnswers || question.correctAnswers.length === 0) {
    throw new Error(`Question ${index + 1}: At least one correct answer is required`);
  }
  if (question.correctAnswers.some(i => i < 0 || i >= question.options.length)) {
    throw new Error(`Question ${index + 1}: Correct answer indices are out of range`);
  }
  if (question.points < 0) {
    throw new Error(`Question ${index + 1}: Points must be non-negative`);
  }
}

/**
 * Create a new Quiz entity (BP-CODE-001: Entity Input DTO)
 */
export function createQuiz(input: CreateQuizInput): Quiz {
  // Validation
  if (!input.lessonId) {
    throw new Error('Lesson ID is required');
  }
  if (!input.title || input.title.trim().length === 0) {
    throw new Error('Quiz title is required');
  }
  if (!input.questions || input.questions.length === 0) {
    throw new Error('At least one question is required');
  }
  if (input.passingScorePercent < 0 || input.passingScorePercent > 100) {
    throw new Error('Passing score must be between 0 and 100');
  }
  if (input.timeLimitMinutes !== undefined && input.timeLimitMinutes < 1) {
    throw new Error('Time limit must be at least 1 minute');
  }
  if (input.maxAttempts !== undefined && input.maxAttempts < 1) {
    throw new Error('Max attempts must be at least 1');
  }

  // Validate all questions
  input.questions.forEach((q, i) => validateQuestion(q, i));

  const now = new Date();
  return {
    id: generateQuizId(),
    lessonId: input.lessonId,
    title: input.title.trim(),
    questions: input.questions,
    passingScorePercent: input.passingScorePercent,
    timeLimitMinutes: input.timeLimitMinutes,
    maxAttempts: input.maxAttempts,
    createdAt: now,
    updatedAt: now,
  };
}

/**
 * Calculate total possible points for a quiz
 */
export function getTotalPoints(quiz: Quiz): number {
  return quiz.questions.reduce((sum, q) => sum + q.points, 0);
}
