/**
 * Certificate Service
 * Traceability: REQ-ELEARN-001-F050, DES-ELEARN-001 §5.4
 */

import type { 
  Certificate, 
  CertificateId, 
  EnrollmentId
} from '../domain/types.js';
import { createCertificate } from '../domain/certificate.js';
import type { CertificateRepository } from '../infrastructure/certificate-repository.js';
import type { EnrollmentRepository } from '../infrastructure/enrollment-repository.js';
import type { CourseRepository } from '../infrastructure/course-repository.js';
import type { LearnerRepository } from '../infrastructure/learner-repository.js';
import type { InstructorRepository } from '../infrastructure/instructor-repository.js';

/**
 * Domain Errors
 */
export class EnrollmentNotCompletedError extends Error {
  constructor(enrollmentId: EnrollmentId) {
    super(`Cannot generate certificate for incomplete enrollment ${enrollmentId}`);
    this.name = 'EnrollmentNotCompletedError';
  }
}

export class CertificateAlreadyExistsError extends Error {
  constructor(enrollmentId: EnrollmentId) {
    super(`Certificate already exists for enrollment ${enrollmentId}`);
    this.name = 'CertificateAlreadyExistsError';
  }
}

export class CertificateNotFoundError extends Error {
  constructor(certificateId: CertificateId) {
    super(`Certificate not found: ${certificateId}`);
    this.name = 'CertificateNotFoundError';
  }
}

export class EnrollmentNotFoundError extends Error {
  constructor(enrollmentId: EnrollmentId) {
    super(`Enrollment not found: ${enrollmentId}`);
    this.name = 'EnrollmentNotFoundError';
  }
}

/**
 * Certificate Service (BP-DESIGN-003: Service Layer with DI)
 */
export class CertificateService {
  constructor(
    private certificateRepository: CertificateRepository,
    private enrollmentRepository: EnrollmentRepository,
    private courseRepository: CourseRepository,
    private learnerRepository: LearnerRepository,
    private instructorRepository: InstructorRepository
  ) {}

  /**
   * Generate a certificate for a completed enrollment
   * Traceability: REQ-ELEARN-001-F050
   */
  async generateCertificate(enrollmentId: EnrollmentId): Promise<Certificate> {
    // Check if certificate already exists
    const existing = await this.certificateRepository.findByEnrollmentId(enrollmentId);
    if (existing) {
      throw new CertificateAlreadyExistsError(enrollmentId);
    }

    // Get enrollment
    const enrollment = await this.enrollmentRepository.findById(enrollmentId);
    if (!enrollment) {
      throw new EnrollmentNotFoundError(enrollmentId);
    }

    // Check if enrollment is completed
    if (enrollment.status !== 'completed') {
      throw new EnrollmentNotCompletedError(enrollmentId);
    }

    // Get course
    const course = await this.courseRepository.findById(enrollment.courseId);
    if (!course) {
      throw new Error(`Course not found: ${enrollment.courseId}`);
    }

    // Get learner
    const learner = await this.learnerRepository.findById(enrollment.learnerId);
    if (!learner) {
      throw new Error(`Learner not found: ${enrollment.learnerId}`);
    }

    // Get instructor
    const instructor = await this.instructorRepository.findById(course.instructorId);
    if (!instructor) {
      throw new Error(`Instructor not found: ${course.instructorId}`);
    }

    // Create certificate
    const certificate = createCertificate({
      enrollmentId,
      learnerId: enrollment.learnerId,
      courseId: enrollment.courseId,
      learnerName: learner.name,
      courseTitle: course.title,
      instructorName: instructor.name,
    });

    await this.certificateRepository.save(certificate);
    return certificate;
  }

  /**
   * Get certificate by ID
   */
  async getCertificate(id: CertificateId): Promise<Certificate | null> {
    return this.certificateRepository.findById(id);
  }

  /**
   * Verify a certificate exists and is valid
   */
  async verifyCertificate(id: CertificateId): Promise<boolean> {
    const certificate = await this.certificateRepository.findById(id);
    if (!certificate) {
      return false;
    }

    // Verify the enrollment is still completed
    const enrollment = await this.enrollmentRepository.findById(certificate.enrollmentId);
    return enrollment !== null && enrollment.status === 'completed';
  }

  /**
   * Get certificate by enrollment ID
   */
  async getCertificateByEnrollment(enrollmentId: EnrollmentId): Promise<Certificate | null> {
    return this.certificateRepository.findByEnrollmentId(enrollmentId);
  }
}
