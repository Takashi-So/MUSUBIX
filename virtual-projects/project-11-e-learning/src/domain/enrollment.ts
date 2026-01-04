/**
 * Enrollment Entity
 * Traceability: REQ-ELEARN-001-F021, F030, F031, F032, DES-ELEARN-001 §4.1.4
 */

import type { 
  Enrollment, 
  CreateEnrollmentInput, 
  EnrollmentId, 
  EnrollmentStatus,
  LessonId 
} from './types.js';
import { validEnrollmentStatusTransitions } from './types.js';

// ID counter for testing (BP-TEST-001: Test Counter Reset)
let enrollmentCounter = 0;

/**
 * Reset enrollment counter for testing
 */
export function resetEnrollmentCounter(): void {
  enrollmentCounter = 0;
}

/**
 * Generate enrollment ID (BP-CODE-002: Date-based ID Format)
 * Format: ENR-YYYYMMDD-NNN
 */
function generateEnrollmentId(): EnrollmentId {
  const now = new Date();
  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, '');
  enrollmentCounter++;
  const counter = String(enrollmentCounter).padStart(3, '0');
  return `ENR-${dateStr}-${counter}` as EnrollmentId;
}

/**
 * Create a new Enrollment entity (BP-CODE-001: Entity Input DTO)
 */
export function createEnrollment(input: CreateEnrollmentInput): Enrollment {
  // Validation
  if (!input.learnerId) {
    throw new Error('Learner ID is required');
  }
  if (!input.courseId) {
    throw new Error('Course ID is required');
  }

  return {
    id: generateEnrollmentId(),
    learnerId: input.learnerId,
    courseId: input.courseId,
    status: 'active',
    progressPercent: 0,
    completedLessonIds: [],
    enrolledAt: new Date(),
    completedAt: undefined,
  };
}

/**
 * Check if a status transition is valid (BP-DESIGN-001: Status Transition Map)
 */
export function canTransitionEnrollmentStatus(from: EnrollmentStatus, to: EnrollmentStatus): boolean {
  return validEnrollmentStatusTransitions[from].includes(to);
}

/**
 * Transition enrollment status
 * @throws Error if transition is invalid
 */
export function transitionEnrollmentStatus(enrollment: Enrollment, newStatus: EnrollmentStatus): Enrollment {
  if (!canTransitionEnrollmentStatus(enrollment.status, newStatus)) {
    throw new Error(`Invalid status transition from ${enrollment.status} to ${newStatus}`);
  }
  return {
    ...enrollment,
    status: newStatus,
    completedAt: newStatus === 'completed' ? new Date() : enrollment.completedAt,
  };
}

/**
 * Mark a lesson as completed and update progress
 * REQ-ELEARN-001-F030: Lesson Completion Tracking
 * REQ-ELEARN-001-F061: Invalid Progress Prevention
 */
export function completeLessonInEnrollment(
  enrollment: Enrollment,
  lessonId: LessonId,
  totalLessons: number
): Enrollment {
  // Don't add if already completed
  if (enrollment.completedLessonIds.includes(lessonId)) {
    return enrollment;
  }

  const newCompletedLessonIds = [...enrollment.completedLessonIds, lessonId];
  const progressPercent = Math.min(100, Math.round((newCompletedLessonIds.length / totalLessons) * 100));

  // REQ-ELEARN-001-F032: Course Completion
  const isCompleted = progressPercent >= 100;
  
  return {
    ...enrollment,
    completedLessonIds: newCompletedLessonIds,
    progressPercent,
    status: isCompleted ? 'completed' : enrollment.status,
    completedAt: isCompleted ? new Date() : enrollment.completedAt,
  };
}

/**
 * Calculate progress percentage
 */
export function calculateProgress(completedLessons: number, totalLessons: number): number {
  if (totalLessons === 0) return 0;
  const progress = (completedLessons / totalLessons) * 100;
  // REQ-ELEARN-001-F061: Progress must be between 0 and 100
  return Math.min(100, Math.max(0, Math.round(progress)));
}
