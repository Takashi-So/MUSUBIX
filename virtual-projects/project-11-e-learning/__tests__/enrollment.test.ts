/**
 * Enrollment Entity & Service Tests
 * Traceability: REQ-ELEARN-001-F021, F030, F031, F032, F060, F061
 * Tests: TEST-021, TEST-030, TEST-031, TEST-032, TEST-060, TEST-061
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { 
  createEnrollment,
  resetEnrollmentCounter,
  completeLessonInEnrollment,
  calculateProgress
} from '../src/domain/enrollment.js';
import { createCourse, resetCourseCounter } from '../src/domain/course.js';
import { createLesson, resetLessonCounter } from '../src/domain/lesson.js';
import { createLearner, resetLearnerCounter } from '../src/domain/learner.js';
import { EnrollmentService, DuplicateEnrollmentError, CourseNotPublishedError } from '../src/application/enrollment-service.js';
import { InMemoryEnrollmentRepository } from '../src/infrastructure/enrollment-repository.js';
import { InMemoryCourseRepository } from '../src/infrastructure/course-repository.js';
import { InMemoryLessonRepository } from '../src/infrastructure/lesson-repository.js';
import type { LearnerId, CourseId, LessonId, InstructorId } from '../src/domain/types.js';

describe('Enrollment Entity', () => {
  // BP-TEST-001: Test Counter Reset
  beforeEach(() => {
    resetEnrollmentCounter();
    resetCourseCounter();
    resetLessonCounter();
    resetLearnerCounter();
  });

  describe('createEnrollment', () => {
    it('should create enrollment with initial progress of 0', () => {
      const enrollment = createEnrollment({
        learnerId: 'LRN-20260104-001' as LearnerId,
        courseId: 'CRS-20260104-001' as CourseId,
      });

      expect(enrollment.id).toMatch(/^ENR-\d{8}-001$/);
      expect(enrollment.learnerId).toBe('LRN-20260104-001');
      expect(enrollment.courseId).toBe('CRS-20260104-001');
      expect(enrollment.status).toBe('active');
      expect(enrollment.progressPercent).toBe(0);
      expect(enrollment.completedLessonIds).toEqual([]);
      expect(enrollment.enrolledAt).toBeInstanceOf(Date);
      expect(enrollment.completedAt).toBeUndefined();
    });
  });

  describe('completeLessonInEnrollment', () => {
    it('should update progress when lesson is completed', () => {
      const enrollment = createEnrollment({
        learnerId: 'LRN-20260104-001' as LearnerId,
        courseId: 'CRS-20260104-001' as CourseId,
      });

      const lessonId = 'LES-20260104-001' as LessonId;
      const updated = completeLessonInEnrollment(enrollment, lessonId, 4);

      expect(updated.progressPercent).toBe(25); // 1/4 = 25%
      expect(updated.completedLessonIds).toContain(lessonId);
      expect(updated.status).toBe('active');
    });

    it('should mark as completed when progress reaches 100%', () => {
      let enrollment = createEnrollment({
        learnerId: 'LRN-20260104-001' as LearnerId,
        courseId: 'CRS-20260104-001' as CourseId,
      });

      const totalLessons = 2;
      enrollment = completeLessonInEnrollment(enrollment, 'LES-20260104-001' as LessonId, totalLessons);
      expect(enrollment.status).toBe('active');
      expect(enrollment.progressPercent).toBe(50);

      enrollment = completeLessonInEnrollment(enrollment, 'LES-20260104-002' as LessonId, totalLessons);
      expect(enrollment.status).toBe('completed');
      expect(enrollment.progressPercent).toBe(100);
      expect(enrollment.completedAt).toBeInstanceOf(Date);
    });

    it('should not add duplicate lesson completions', () => {
      const enrollment = createEnrollment({
        learnerId: 'LRN-20260104-001' as LearnerId,
        courseId: 'CRS-20260104-001' as CourseId,
      });

      const lessonId = 'LES-20260104-001' as LessonId;
      const updated1 = completeLessonInEnrollment(enrollment, lessonId, 4);
      const updated2 = completeLessonInEnrollment(updated1, lessonId, 4);

      expect(updated2.completedLessonIds.length).toBe(1);
      expect(updated2.progressPercent).toBe(25);
    });
  });

  describe('calculateProgress', () => {
    it('should calculate correct percentage', () => {
      expect(calculateProgress(1, 4)).toBe(25);
      expect(calculateProgress(2, 4)).toBe(50);
      expect(calculateProgress(3, 4)).toBe(75);
      expect(calculateProgress(4, 4)).toBe(100);
    });

    it('should return 0 for 0 total lessons', () => {
      expect(calculateProgress(0, 0)).toBe(0);
    });

    // REQ-ELEARN-001-F061: Progress must be between 0 and 100
    it('should cap progress at 100', () => {
      expect(calculateProgress(5, 4)).toBe(100);
    });
  });
});

describe('EnrollmentService', () => {
  let service: EnrollmentService;
  let enrollmentRepo: InMemoryEnrollmentRepository;
  let courseRepo: InMemoryCourseRepository;
  let lessonRepo: InMemoryLessonRepository;

  beforeEach(() => {
    resetEnrollmentCounter();
    resetCourseCounter();
    resetLessonCounter();
    
    enrollmentRepo = new InMemoryEnrollmentRepository();
    courseRepo = new InMemoryCourseRepository();
    lessonRepo = new InMemoryLessonRepository();
    
    service = new EnrollmentService(enrollmentRepo, courseRepo, lessonRepo);
  });

  describe('enrollLearner', () => {
    it('should enroll learner in published course', async () => {
      // Setup: Create and publish a course
      const course = createCourse({
        title: 'Test Course',
        description: 'Test',
        category: 'programming',
        difficultyLevel: 'beginner',
        instructorId: 'INS-20260104-001' as InstructorId,
      });
      course.status = 'published';
      await courseRepo.save(course);

      const enrollment = await service.enrollLearner({
        learnerId: 'LRN-20260104-001' as LearnerId,
        courseId: course.id,
      });

      expect(enrollment.courseId).toBe(course.id);
      expect(enrollment.status).toBe('active');
    });

    // REQ-ELEARN-001-F060: Duplicate Enrollment Prevention
    it('should throw DuplicateEnrollmentError for duplicate enrollment', async () => {
      const course = createCourse({
        title: 'Test Course',
        description: 'Test',
        category: 'programming',
        difficultyLevel: 'beginner',
        instructorId: 'INS-20260104-001' as InstructorId,
      });
      course.status = 'published';
      await courseRepo.save(course);

      const input = {
        learnerId: 'LRN-20260104-001' as LearnerId,
        courseId: course.id,
      };

      await service.enrollLearner(input);

      await expect(service.enrollLearner(input))
        .rejects.toThrow(DuplicateEnrollmentError);
    });

    it('should throw CourseNotPublishedError for draft course', async () => {
      const course = createCourse({
        title: 'Test Course',
        description: 'Test',
        category: 'programming',
        difficultyLevel: 'beginner',
        instructorId: 'INS-20260104-001' as InstructorId,
      });
      await courseRepo.save(course);

      await expect(service.enrollLearner({
        learnerId: 'LRN-20260104-001' as LearnerId,
        courseId: course.id,
      })).rejects.toThrow(CourseNotPublishedError);
    });
  });

  describe('completeLesson', () => {
    it('should complete lesson and update progress', async () => {
      // Setup
      const course = createCourse({
        title: 'Test Course',
        description: 'Test',
        category: 'programming',
        difficultyLevel: 'beginner',
        instructorId: 'INS-20260104-001' as InstructorId,
      });
      course.status = 'published';
      await courseRepo.save(course);

      const lesson1 = createLesson({
        courseId: course.id,
        title: 'Lesson 1',
        contentType: 'text',
        content: 'Content 1',
        order: 1,
      });
      const lesson2 = createLesson({
        courseId: course.id,
        title: 'Lesson 2',
        contentType: 'text',
        content: 'Content 2',
        order: 2,
      });
      await lessonRepo.save(lesson1);
      await lessonRepo.save(lesson2);

      const enrollment = await service.enrollLearner({
        learnerId: 'LRN-20260104-001' as LearnerId,
        courseId: course.id,
      });

      // Complete first lesson
      const updated = await service.completeLesson(enrollment.id, lesson1.id);
      expect(updated.progressPercent).toBe(50);
      expect(updated.status).toBe('active');

      // Complete second lesson
      const completed = await service.completeLesson(enrollment.id, lesson2.id);
      expect(completed.progressPercent).toBe(100);
      expect(completed.status).toBe('completed');
    });
  });
});
