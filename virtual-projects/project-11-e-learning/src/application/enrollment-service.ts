/**
 * Enrollment Service
 * Traceability: REQ-ELEARN-001-F021, F030, F031, F032, F060, F061, DES-ELEARN-001 §5.2
 */

import type { 
  Enrollment, 
  EnrollmentId, 
  CreateEnrollmentInput,
  LearnerId,
  CourseId,
  LessonId
} from '../domain/types.js';
import { createEnrollment, completeLessonInEnrollment } from '../domain/enrollment.js';
import type { EnrollmentRepository } from '../infrastructure/enrollment-repository.js';
import type { CourseRepository } from '../infrastructure/course-repository.js';
import type { LessonRepository } from '../infrastructure/lesson-repository.js';

/**
 * Domain Errors
 */
export class DuplicateEnrollmentError extends Error {
  constructor(learnerId: LearnerId, courseId: CourseId) {
    super(`Learner ${learnerId} is already enrolled in course ${courseId}`);
    this.name = 'DuplicateEnrollmentError';
  }
}

export class EnrollmentNotFoundError extends Error {
  constructor(enrollmentId: EnrollmentId) {
    super(`Enrollment not found: ${enrollmentId}`);
    this.name = 'EnrollmentNotFoundError';
  }
}

export class CourseNotPublishedError extends Error {
  constructor(courseId: CourseId) {
    super(`Cannot enroll in unpublished course ${courseId}`);
    this.name = 'CourseNotPublishedError';
  }
}

export class LessonNotFoundError extends Error {
  constructor(lessonId: LessonId) {
    super(`Lesson not found: ${lessonId}`);
    this.name = 'LessonNotFoundError';
  }
}

export class LessonNotInCourseError extends Error {
  constructor(lessonId: LessonId, courseId: CourseId) {
    super(`Lesson ${lessonId} does not belong to course ${courseId}`);
    this.name = 'LessonNotInCourseError';
  }
}

/**
 * Enrollment Service (BP-DESIGN-003: Service Layer with DI)
 */
export class EnrollmentService {
  constructor(
    private enrollmentRepository: EnrollmentRepository,
    private courseRepository: CourseRepository,
    private lessonRepository: LessonRepository
  ) {}

  /**
   * Enroll a learner in a course
   * Traceability: REQ-ELEARN-001-F021, F060
   */
  async enrollLearner(input: CreateEnrollmentInput): Promise<Enrollment> {
    // REQ-ELEARN-001-F060: Duplicate Enrollment Prevention
    const existing = await this.enrollmentRepository.findByLearnerAndCourse(
      input.learnerId, 
      input.courseId
    );
    if (existing) {
      throw new DuplicateEnrollmentError(input.learnerId, input.courseId);
    }

    // Check if course is published
    const course = await this.courseRepository.findById(input.courseId);
    if (!course || course.status !== 'published') {
      throw new CourseNotPublishedError(input.courseId);
    }

    const enrollment = createEnrollment(input);
    await this.enrollmentRepository.save(enrollment);
    return enrollment;
  }

  /**
   * Get enrollment by ID
   */
  async getEnrollment(id: EnrollmentId): Promise<Enrollment | null> {
    return this.enrollmentRepository.findById(id);
  }

  /**
   * Get enrollment by learner and course
   */
  async getEnrollmentByLearnerAndCourse(
    learnerId: LearnerId, 
    courseId: CourseId
  ): Promise<Enrollment | null> {
    return this.enrollmentRepository.findByLearnerAndCourse(learnerId, courseId);
  }

  /**
   * Complete a lesson
   * Traceability: REQ-ELEARN-001-F030, F031, F032, F061
   */
  async completeLesson(enrollmentId: EnrollmentId, lessonId: LessonId): Promise<Enrollment> {
    const enrollment = await this.enrollmentRepository.findById(enrollmentId);
    if (!enrollment) {
      throw new EnrollmentNotFoundError(enrollmentId);
    }

    // Verify lesson exists and belongs to the course
    const lesson = await this.lessonRepository.findById(lessonId);
    if (!lesson) {
      throw new LessonNotFoundError(lessonId);
    }
    if (lesson.courseId !== enrollment.courseId) {
      throw new LessonNotInCourseError(lessonId, enrollment.courseId);
    }

    // Get total lesson count for progress calculation
    const totalLessons = await this.lessonRepository.countByCourseId(enrollment.courseId);

    // REQ-ELEARN-001-F030, F032: Update progress and check for completion
    const updatedEnrollment = completeLessonInEnrollment(enrollment, lessonId, totalLessons);
    await this.enrollmentRepository.save(updatedEnrollment);

    return updatedEnrollment;
  }

  /**
   * Get progress for an enrollment
   */
  async getProgress(enrollmentId: EnrollmentId): Promise<number> {
    const enrollment = await this.enrollmentRepository.findById(enrollmentId);
    if (!enrollment) {
      throw new EnrollmentNotFoundError(enrollmentId);
    }
    return enrollment.progressPercent;
  }

  /**
   * Get all enrollments for a learner
   */
  async getEnrollmentsByLearner(learnerId: LearnerId): Promise<Enrollment[]> {
    return this.enrollmentRepository.findByLearnerId(learnerId);
  }

  /**
   * Get all enrollments for a course
   */
  async getEnrollmentsByCourse(courseId: CourseId): Promise<Enrollment[]> {
    return this.enrollmentRepository.findByCourseId(courseId);
  }
}
