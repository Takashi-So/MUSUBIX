/**
 * InMemory Lesson Repository
 * Traceability: DES-ELEARN-001 §6.1
 */

import type { Lesson, LessonId, CourseId } from '../domain/types.js';

export interface LessonRepository {
  save(lesson: Lesson): Promise<void>;
  findById(id: LessonId): Promise<Lesson | null>;
  findByCourseId(courseId: CourseId): Promise<Lesson[]>;
  delete(id: LessonId): Promise<void>;
  countByCourseId(courseId: CourseId): Promise<number>;
}

export class InMemoryLessonRepository implements LessonRepository {
  private lessons: Map<LessonId, Lesson> = new Map();

  async save(lesson: Lesson): Promise<void> {
    this.lessons.set(lesson.id, { ...lesson });
  }

  async findById(id: LessonId): Promise<Lesson | null> {
    const lesson = this.lessons.get(id);
    return lesson ? { ...lesson } : null;
  }

  async findByCourseId(courseId: CourseId): Promise<Lesson[]> {
    return Array.from(this.lessons.values())
      .filter(l => l.courseId === courseId)
      .sort((a, b) => a.order - b.order)
      .map(l => ({ ...l }));
  }

  async delete(id: LessonId): Promise<void> {
    this.lessons.delete(id);
  }

  async countByCourseId(courseId: CourseId): Promise<number> {
    return Array.from(this.lessons.values())
      .filter(l => l.courseId === courseId)
      .length;
  }

  // For testing
  clear(): void {
    this.lessons.clear();
  }
}
