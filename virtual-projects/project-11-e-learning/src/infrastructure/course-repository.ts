/**
 * InMemory Course Repository
 * Traceability: DES-ELEARN-001 §6.1
 */

import type { Course, CourseId, InstructorId, CourseSearchCriteria } from '../domain/types.js';

export interface CourseRepository {
  save(course: Course): Promise<void>;
  findById(id: CourseId): Promise<Course | null>;
  findByInstructorId(instructorId: InstructorId): Promise<Course[]>;
  search(criteria: CourseSearchCriteria): Promise<Course[]>;
  findAll(): Promise<Course[]>;
  delete(id: CourseId): Promise<void>;
}

export class InMemoryCourseRepository implements CourseRepository {
  private courses: Map<CourseId, Course> = new Map();

  async save(course: Course): Promise<void> {
    this.courses.set(course.id, { ...course });
  }

  async findById(id: CourseId): Promise<Course | null> {
    const course = this.courses.get(id);
    return course ? { ...course } : null;
  }

  async findByInstructorId(instructorId: InstructorId): Promise<Course[]> {
    return Array.from(this.courses.values())
      .filter(c => c.instructorId === instructorId)
      .map(c => ({ ...c }));
  }

  async search(criteria: CourseSearchCriteria): Promise<Course[]> {
    let results = Array.from(this.courses.values());

    if (criteria.titleKeyword) {
      const keyword = criteria.titleKeyword.toLowerCase();
      results = results.filter(c => 
        c.title.toLowerCase().includes(keyword) ||
        c.description.toLowerCase().includes(keyword)
      );
    }

    if (criteria.category) {
      results = results.filter(c => c.category === criteria.category);
    }

    if (criteria.difficultyLevel) {
      results = results.filter(c => c.difficultyLevel === criteria.difficultyLevel);
    }

    if (criteria.instructorId) {
      results = results.filter(c => c.instructorId === criteria.instructorId);
    }

    if (criteria.status) {
      results = results.filter(c => c.status === criteria.status);
    }

    return results.map(c => ({ ...c }));
  }

  async findAll(): Promise<Course[]> {
    return Array.from(this.courses.values()).map(c => ({ ...c }));
  }

  async delete(id: CourseId): Promise<void> {
    this.courses.delete(id);
  }

  // For testing
  clear(): void {
    this.courses.clear();
  }
}
