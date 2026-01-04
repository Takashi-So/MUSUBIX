/**
 * QuizAttempt Entity
 * Traceability: REQ-ELEARN-001-F041, DES-ELEARN-001 §4.1.7
 */

import type { 
  QuizAttempt, 
  CreateQuizAttemptInput, 
  QuizAttemptId,
  Quiz 
} from './types.js';

// ID counter for testing (BP-TEST-001: Test Counter Reset)
let quizAttemptCounter = 0;

/**
 * Reset quiz attempt counter for testing
 */
export function resetQuizAttemptCounter(): void {
  quizAttemptCounter = 0;
}

/**
 * Generate quiz attempt ID (BP-CODE-002: Date-based ID Format)
 * Format: ATT-YYYYMMDD-NNN
 */
function generateQuizAttemptId(): QuizAttemptId {
  const now = new Date();
  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, '');
  quizAttemptCounter++;
  const counter = String(quizAttemptCounter).padStart(3, '0');
  return `ATT-${dateStr}-${counter}` as QuizAttemptId;
}

/**
 * Calculate score for a quiz attempt
 */
export function calculateQuizScore(quiz: Quiz, answers: Record<string, number[]>): number {
  let earnedPoints = 0;
  let totalPoints = 0;

  for (const question of quiz.questions) {
    totalPoints += question.points;
    const userAnswers = answers[question.id] ?? [];
    
    // Check if answers match exactly
    const correctSet = new Set(question.correctAnswers);
    const userSet = new Set(userAnswers);
    
    if (correctSet.size === userSet.size && 
        [...correctSet].every(a => userSet.has(a))) {
      earnedPoints += question.points;
    }
  }

  if (totalPoints === 0) return 0;
  return Math.round((earnedPoints / totalPoints) * 100);
}

/**
 * Create a new QuizAttempt entity (BP-CODE-001: Entity Input DTO)
 */
export function createQuizAttempt(input: CreateQuizAttemptInput, quiz: Quiz): QuizAttempt {
  // Validation
  if (!input.quizId) {
    throw new Error('Quiz ID is required');
  }
  if (!input.learnerId) {
    throw new Error('Learner ID is required');
  }

  const scorePercent = calculateQuizScore(quiz, input.answers);
  const passed = scorePercent >= quiz.passingScorePercent;

  const now = new Date();
  return {
    id: generateQuizAttemptId(),
    quizId: input.quizId,
    learnerId: input.learnerId,
    answers: input.answers,
    scorePercent,
    passed,
    startedAt: now, // In real app, this would be tracked separately
    completedAt: now,
  };
}
