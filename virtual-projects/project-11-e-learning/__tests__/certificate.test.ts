/**
 * Certificate Service Tests
 * Traceability: REQ-ELEARN-001-F050, TEST-050
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { createCertificate, resetCertificateCounter } from '../src/domain/certificate.js';
import { createEnrollment, resetEnrollmentCounter } from '../src/domain/enrollment.js';
import { createCourse, resetCourseCounter } from '../src/domain/course.js';
import { createLearner, resetLearnerCounter } from '../src/domain/learner.js';
import { createInstructor, resetInstructorCounter } from '../src/domain/instructor.js';
import { CertificateService, EnrollmentNotCompletedError, CertificateAlreadyExistsError } from '../src/application/certificate-service.js';
import { InMemoryCertificateRepository } from '../src/infrastructure/certificate-repository.js';
import { InMemoryEnrollmentRepository } from '../src/infrastructure/enrollment-repository.js';
import { InMemoryCourseRepository } from '../src/infrastructure/course-repository.js';
import { InMemoryLearnerRepository } from '../src/infrastructure/learner-repository.js';
import { InMemoryInstructorRepository } from '../src/infrastructure/instructor-repository.js';
import type { EnrollmentId, LearnerId, CourseId } from '../src/domain/types.js';

describe('Certificate Entity', () => {
  beforeEach(() => {
    resetCertificateCounter();
  });

  describe('createCertificate', () => {
    it('should create certificate with valid input', () => {
      const certificate = createCertificate({
        enrollmentId: 'ENR-20260104-001' as EnrollmentId,
        learnerId: 'LRN-20260104-001' as LearnerId,
        courseId: 'CRS-20260104-001' as CourseId,
        learnerName: 'John Doe',
        courseTitle: 'TypeScript Mastery',
        instructorName: 'Jane Smith',
      });

      expect(certificate.id).toMatch(/^CERT-\d{8}-001$/);
      expect(certificate.learnerName).toBe('John Doe');
      expect(certificate.courseTitle).toBe('TypeScript Mastery');
      expect(certificate.instructorName).toBe('Jane Smith');
      expect(certificate.issuedAt).toBeInstanceOf(Date);
    });

    it('should throw error for missing learner name', () => {
      expect(() => createCertificate({
        enrollmentId: 'ENR-20260104-001' as EnrollmentId,
        learnerId: 'LRN-20260104-001' as LearnerId,
        courseId: 'CRS-20260104-001' as CourseId,
        learnerName: '',
        courseTitle: 'TypeScript Mastery',
        instructorName: 'Jane Smith',
      })).toThrow('Learner name is required');
    });
  });
});

describe('CertificateService', () => {
  let service: CertificateService;
  let certificateRepo: InMemoryCertificateRepository;
  let enrollmentRepo: InMemoryEnrollmentRepository;
  let courseRepo: InMemoryCourseRepository;
  let learnerRepo: InMemoryLearnerRepository;
  let instructorRepo: InMemoryInstructorRepository;

  beforeEach(() => {
    resetCertificateCounter();
    resetEnrollmentCounter();
    resetCourseCounter();
    resetLearnerCounter();
    resetInstructorCounter();

    certificateRepo = new InMemoryCertificateRepository();
    enrollmentRepo = new InMemoryEnrollmentRepository();
    courseRepo = new InMemoryCourseRepository();
    learnerRepo = new InMemoryLearnerRepository();
    instructorRepo = new InMemoryInstructorRepository();

    service = new CertificateService(
      certificateRepo,
      enrollmentRepo,
      courseRepo,
      learnerRepo,
      instructorRepo
    );
  });

  describe('generateCertificate', () => {
    it('should generate certificate for completed enrollment', async () => {
      // Setup: Create instructor
      const instructor = createInstructor({
        name: 'Jane Smith',
        email: 'jane@example.com',
        passwordHash: 'hash123',
        bio: 'Expert instructor',
      });
      await instructorRepo.save(instructor);

      // Create course
      const course = createCourse({
        title: 'TypeScript Mastery',
        description: 'Master TypeScript',
        category: 'programming',
        difficultyLevel: 'advanced',
        instructorId: instructor.id,
      });
      await courseRepo.save(course);

      // Create learner
      const learner = createLearner({
        name: 'John Doe',
        email: 'john@example.com',
        passwordHash: 'hash456',
      });
      await learnerRepo.save(learner);

      // Create completed enrollment
      const enrollment = createEnrollment({
        learnerId: learner.id,
        courseId: course.id,
      });
      enrollment.status = 'completed';
      enrollment.progressPercent = 100;
      enrollment.completedAt = new Date();
      await enrollmentRepo.save(enrollment);

      // Generate certificate
      const certificate = await service.generateCertificate(enrollment.id);

      expect(certificate.learnerName).toBe('John Doe');
      expect(certificate.courseTitle).toBe('TypeScript Mastery');
      expect(certificate.instructorName).toBe('Jane Smith');
    });

    it('should throw EnrollmentNotCompletedError for active enrollment', async () => {
      // Setup
      const instructor = createInstructor({
        name: 'Jane Smith',
        email: 'jane@example.com',
        passwordHash: 'hash123',
        bio: 'Expert instructor',
      });
      await instructorRepo.save(instructor);

      const course = createCourse({
        title: 'Test Course',
        description: 'Test',
        category: 'programming',
        difficultyLevel: 'beginner',
        instructorId: instructor.id,
      });
      await courseRepo.save(course);

      const learner = createLearner({
        name: 'John Doe',
        email: 'john@example.com',
        passwordHash: 'hash456',
      });
      await learnerRepo.save(learner);

      const enrollment = createEnrollment({
        learnerId: learner.id,
        courseId: course.id,
      });
      // enrollment.status is 'active' by default
      await enrollmentRepo.save(enrollment);

      await expect(service.generateCertificate(enrollment.id))
        .rejects.toThrow(EnrollmentNotCompletedError);
    });

    it('should throw CertificateAlreadyExistsError for duplicate certificate', async () => {
      // Setup
      const instructor = createInstructor({
        name: 'Jane Smith',
        email: 'jane@example.com',
        passwordHash: 'hash123',
        bio: 'Expert instructor',
      });
      await instructorRepo.save(instructor);

      const course = createCourse({
        title: 'Test Course',
        description: 'Test',
        category: 'programming',
        difficultyLevel: 'beginner',
        instructorId: instructor.id,
      });
      await courseRepo.save(course);

      const learner = createLearner({
        name: 'John Doe',
        email: 'john@example.com',
        passwordHash: 'hash456',
      });
      await learnerRepo.save(learner);

      const enrollment = createEnrollment({
        learnerId: learner.id,
        courseId: course.id,
      });
      enrollment.status = 'completed';
      enrollment.progressPercent = 100;
      await enrollmentRepo.save(enrollment);

      // Generate first certificate
      await service.generateCertificate(enrollment.id);

      // Try to generate duplicate
      await expect(service.generateCertificate(enrollment.id))
        .rejects.toThrow(CertificateAlreadyExistsError);
    });
  });

  describe('verifyCertificate', () => {
    it('should return true for valid certificate', async () => {
      // Setup
      const instructor = createInstructor({
        name: 'Jane Smith',
        email: 'jane@example.com',
        passwordHash: 'hash123',
        bio: 'Expert instructor',
      });
      await instructorRepo.save(instructor);

      const course = createCourse({
        title: 'Test Course',
        description: 'Test',
        category: 'programming',
        difficultyLevel: 'beginner',
        instructorId: instructor.id,
      });
      await courseRepo.save(course);

      const learner = createLearner({
        name: 'John Doe',
        email: 'john@example.com',
        passwordHash: 'hash456',
      });
      await learnerRepo.save(learner);

      const enrollment = createEnrollment({
        learnerId: learner.id,
        courseId: course.id,
      });
      enrollment.status = 'completed';
      enrollment.progressPercent = 100;
      await enrollmentRepo.save(enrollment);

      const certificate = await service.generateCertificate(enrollment.id);

      const isValid = await service.verifyCertificate(certificate.id);
      expect(isValid).toBe(true);
    });

    it('should return false for non-existent certificate', async () => {
      const isValid = await service.verifyCertificate('CERT-20260104-999' as any);
      expect(isValid).toBe(false);
    });
  });
});
