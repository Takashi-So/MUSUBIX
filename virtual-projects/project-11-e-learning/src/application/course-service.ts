/**
 * Course Service
 * Traceability: REQ-ELEARN-001-F001, F002, F003, DES-ELEARN-001 §5.1
 */

import type { 
  Course, 
  CourseId, 
  CreateCourseInput, 
  CourseSearchCriteria,
  InstructorId 
} from '../domain/types.js';
import { createCourse, transitionCourseStatus } from '../domain/course.js';
import type { CourseRepository } from '../infrastructure/course-repository.js';
import type { LessonRepository } from '../infrastructure/lesson-repository.js';

/**
 * Domain Errors
 */
export class CourseNotFoundError extends Error {
  constructor(courseId: CourseId) {
    super(`Course not found: ${courseId}`);
    this.name = 'CourseNotFoundError';
  }
}

export class CannotPublishCourseError extends Error {
  constructor(courseId: CourseId, reason: string) {
    super(`Cannot publish course ${courseId}: ${reason}`);
    this.name = 'CannotPublishCourseError';
  }
}

/**
 * Course Service (BP-DESIGN-003: Service Layer with DI)
 */
export class CourseService {
  constructor(
    private courseRepository: CourseRepository,
    private lessonRepository: LessonRepository
  ) {}

  /**
   * Create a new course
   * Traceability: REQ-ELEARN-001-F001
   */
  async createCourse(input: CreateCourseInput): Promise<Course> {
    const course = createCourse(input);
    await this.courseRepository.save(course);
    return course;
  }

  /**
   * Get course by ID
   */
  async getCourse(id: CourseId): Promise<Course | null> {
    return this.courseRepository.findById(id);
  }

  /**
   * Update course
   */
  async updateCourse(id: CourseId, updates: Partial<CreateCourseInput>): Promise<Course> {
    const course = await this.courseRepository.findById(id);
    if (!course) {
      throw new CourseNotFoundError(id);
    }

    const updatedCourse: Course = {
      ...course,
      ...(updates.title && { title: updates.title }),
      ...(updates.description && { description: updates.description }),
      ...(updates.category && { category: updates.category }),
      ...(updates.difficultyLevel && { difficultyLevel: updates.difficultyLevel }),
      ...(updates.thumbnail !== undefined && { thumbnail: updates.thumbnail }),
      ...(updates.prerequisites !== undefined && { prerequisites: updates.prerequisites }),
      ...(updates.estimatedDurationMinutes !== undefined && { estimatedDurationMinutes: updates.estimatedDurationMinutes }),
      updatedAt: new Date(),
    };

    await this.courseRepository.save(updatedCourse);
    return updatedCourse;
  }

  /**
   * Publish a course
   * Traceability: REQ-ELEARN-001-F002
   */
  async publishCourse(id: CourseId): Promise<Course> {
    const course = await this.courseRepository.findById(id);
    if (!course) {
      throw new CourseNotFoundError(id);
    }

    // Check if course has at least one lesson
    const lessonCount = await this.lessonRepository.countByCourseId(id);
    if (lessonCount === 0) {
      throw new CannotPublishCourseError(id, 'Course must have at least one lesson');
    }

    const publishedCourse = transitionCourseStatus(course, 'published');
    await this.courseRepository.save(publishedCourse);
    return publishedCourse;
  }

  /**
   * Archive a course
   */
  async archiveCourse(id: CourseId): Promise<Course> {
    const course = await this.courseRepository.findById(id);
    if (!course) {
      throw new CourseNotFoundError(id);
    }

    const archivedCourse = transitionCourseStatus(course, 'archived');
    await this.courseRepository.save(archivedCourse);
    return archivedCourse;
  }

  /**
   * Search courses
   * Traceability: REQ-ELEARN-001-F003
   */
  async searchCourses(criteria: CourseSearchCriteria): Promise<Course[]> {
    return this.courseRepository.search(criteria);
  }

  /**
   * Get courses by instructor
   */
  async getCoursesByInstructor(instructorId: InstructorId): Promise<Course[]> {
    return this.courseRepository.findByInstructorId(instructorId);
  }

  /**
   * Get lesson count for a course
   */
  async getLessonCount(courseId: CourseId): Promise<number> {
    return this.lessonRepository.countByCourseId(courseId);
  }
}
