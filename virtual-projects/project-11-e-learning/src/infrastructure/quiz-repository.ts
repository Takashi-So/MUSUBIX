/**
 * InMemory Quiz Repository
 * Traceability: DES-ELEARN-001 §6.1
 */

import type { Quiz, QuizId, LessonId } from '../domain/types.js';

export interface QuizRepository {
  save(quiz: Quiz): Promise<void>;
  findById(id: QuizId): Promise<Quiz | null>;
  findByLessonId(lessonId: LessonId): Promise<Quiz | null>;
}

export class InMemoryQuizRepository implements QuizRepository {
  private quizzes: Map<QuizId, Quiz> = new Map();

  async save(quiz: Quiz): Promise<void> {
    this.quizzes.set(quiz.id, { 
      ...quiz,
      questions: quiz.questions.map(q => ({ ...q, correctAnswers: [...q.correctAnswers] })),
    });
  }

  async findById(id: QuizId): Promise<Quiz | null> {
    const quiz = this.quizzes.get(id);
    return quiz ? { 
      ...quiz,
      questions: quiz.questions.map(q => ({ ...q, correctAnswers: [...q.correctAnswers] })),
    } : null;
  }

  async findByLessonId(lessonId: LessonId): Promise<Quiz | null> {
    for (const quiz of this.quizzes.values()) {
      if (quiz.lessonId === lessonId) {
        return { 
          ...quiz,
          questions: quiz.questions.map(q => ({ ...q, correctAnswers: [...q.correctAnswers] })),
        };
      }
    }
    return null;
  }

  // For testing
  clear(): void {
    this.quizzes.clear();
  }
}
