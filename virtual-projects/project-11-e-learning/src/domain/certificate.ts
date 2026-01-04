/**
 * Certificate Entity
 * Traceability: REQ-ELEARN-001-F050, DES-ELEARN-001 §4.1.8
 */

import type { Certificate, CreateCertificateInput, CertificateId } from './types.js';

// ID counter for testing (BP-TEST-001: Test Counter Reset)
let certificateCounter = 0;

/**
 * Reset certificate counter for testing
 */
export function resetCertificateCounter(): void {
  certificateCounter = 0;
}

/**
 * Generate certificate ID (BP-CODE-002: Date-based ID Format)
 * Format: CERT-YYYYMMDD-NNN
 */
function generateCertificateId(): CertificateId {
  const now = new Date();
  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, '');
  certificateCounter++;
  const counter = String(certificateCounter).padStart(3, '0');
  return `CERT-${dateStr}-${counter}` as CertificateId;
}

/**
 * Create a new Certificate entity (BP-CODE-001: Entity Input DTO)
 */
export function createCertificate(input: CreateCertificateInput): Certificate {
  // Validation
  if (!input.enrollmentId) {
    throw new Error('Enrollment ID is required');
  }
  if (!input.learnerId) {
    throw new Error('Learner ID is required');
  }
  if (!input.courseId) {
    throw new Error('Course ID is required');
  }
  if (!input.learnerName || input.learnerName.trim().length === 0) {
    throw new Error('Learner name is required');
  }
  if (!input.courseTitle || input.courseTitle.trim().length === 0) {
    throw new Error('Course title is required');
  }
  if (!input.instructorName || input.instructorName.trim().length === 0) {
    throw new Error('Instructor name is required');
  }

  return {
    id: generateCertificateId(),
    enrollmentId: input.enrollmentId,
    learnerId: input.learnerId,
    courseId: input.courseId,
    learnerName: input.learnerName.trim(),
    courseTitle: input.courseTitle.trim(),
    instructorName: input.instructorName.trim(),
    issuedAt: new Date(),
  };
}
