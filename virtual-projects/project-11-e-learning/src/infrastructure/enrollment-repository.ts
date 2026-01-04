/**
 * InMemory Enrollment Repository
 * Traceability: DES-ELEARN-001 §6.1
 */

import type { Enrollment, EnrollmentId, LearnerId, CourseId } from '../domain/types.js';

export interface EnrollmentRepository {
  save(enrollment: Enrollment): Promise<void>;
  findById(id: EnrollmentId): Promise<Enrollment | null>;
  findByLearnerAndCourse(learnerId: LearnerId, courseId: CourseId): Promise<Enrollment | null>;
  findByLearnerId(learnerId: LearnerId): Promise<Enrollment[]>;
  findByCourseId(courseId: CourseId): Promise<Enrollment[]>;
}

export class InMemoryEnrollmentRepository implements EnrollmentRepository {
  private enrollments: Map<EnrollmentId, Enrollment> = new Map();

  async save(enrollment: Enrollment): Promise<void> {
    this.enrollments.set(enrollment.id, { 
      ...enrollment,
      completedLessonIds: [...enrollment.completedLessonIds],
    });
  }

  async findById(id: EnrollmentId): Promise<Enrollment | null> {
    const enrollment = this.enrollments.get(id);
    return enrollment ? { 
      ...enrollment,
      completedLessonIds: [...enrollment.completedLessonIds],
    } : null;
  }

  async findByLearnerAndCourse(learnerId: LearnerId, courseId: CourseId): Promise<Enrollment | null> {
    for (const enrollment of this.enrollments.values()) {
      if (enrollment.learnerId === learnerId && enrollment.courseId === courseId) {
        return { 
          ...enrollment,
          completedLessonIds: [...enrollment.completedLessonIds],
        };
      }
    }
    return null;
  }

  async findByLearnerId(learnerId: LearnerId): Promise<Enrollment[]> {
    return Array.from(this.enrollments.values())
      .filter(e => e.learnerId === learnerId)
      .map(e => ({ 
        ...e,
        completedLessonIds: [...e.completedLessonIds],
      }));
  }

  async findByCourseId(courseId: CourseId): Promise<Enrollment[]> {
    return Array.from(this.enrollments.values())
      .filter(e => e.courseId === courseId)
      .map(e => ({ 
        ...e,
        completedLessonIds: [...e.completedLessonIds],
      }));
  }

  // For testing
  clear(): void {
    this.enrollments.clear();
  }
}
