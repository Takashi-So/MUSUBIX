/**
 * InMemory QuizAttempt Repository
 * Traceability: DES-ELEARN-001 §6.1
 */

import type { QuizAttempt, QuizAttemptId, QuizId, LearnerId } from '../domain/types.js';

export interface QuizAttemptRepository {
  save(attempt: QuizAttempt): Promise<void>;
  findById(id: QuizAttemptId): Promise<QuizAttempt | null>;
  findByQuizAndLearner(quizId: QuizId, learnerId: LearnerId): Promise<QuizAttempt[]>;
  countByQuizAndLearner(quizId: QuizId, learnerId: LearnerId): Promise<number>;
}

export class InMemoryQuizAttemptRepository implements QuizAttemptRepository {
  private attempts: Map<QuizAttemptId, QuizAttempt> = new Map();

  async save(attempt: QuizAttempt): Promise<void> {
    this.attempts.set(attempt.id, { ...attempt });
  }

  async findById(id: QuizAttemptId): Promise<QuizAttempt | null> {
    const attempt = this.attempts.get(id);
    return attempt ? { ...attempt } : null;
  }

  async findByQuizAndLearner(quizId: QuizId, learnerId: LearnerId): Promise<QuizAttempt[]> {
    return Array.from(this.attempts.values())
      .filter(a => a.quizId === quizId && a.learnerId === learnerId)
      .map(a => ({ ...a }));
  }

  async countByQuizAndLearner(quizId: QuizId, learnerId: LearnerId): Promise<number> {
    return Array.from(this.attempts.values())
      .filter(a => a.quizId === quizId && a.learnerId === learnerId)
      .length;
  }

  // For testing
  clear(): void {
    this.attempts.clear();
  }
}
