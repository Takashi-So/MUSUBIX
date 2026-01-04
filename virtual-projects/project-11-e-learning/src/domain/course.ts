/**
 * Course Entity
 * Traceability: REQ-ELEARN-001-F001, F002, DES-ELEARN-001 §4.1.1
 */

import type { Course, CreateCourseInput, CourseId, CourseStatus } from './types.js';
import { validCourseStatusTransitions } from './types.js';

// ID counter for testing (BP-TEST-001: Test Counter Reset)
let courseCounter = 0;

/**
 * Reset course counter for testing
 */
export function resetCourseCounter(): void {
  courseCounter = 0;
}

/**
 * Generate course ID (BP-CODE-002: Date-based ID Format)
 * Format: CRS-YYYYMMDD-NNN
 */
function generateCourseId(): CourseId {
  const now = new Date();
  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, '');
  courseCounter++;
  const counter = String(courseCounter).padStart(3, '0');
  return `CRS-${dateStr}-${counter}` as CourseId;
}

/**
 * Create a new Course entity (BP-CODE-001: Entity Input DTO)
 */
export function createCourse(input: CreateCourseInput): Course {
  // Validation
  if (!input.title || input.title.trim().length === 0) {
    throw new Error('Course title is required');
  }
  if (!input.description || input.description.trim().length === 0) {
    throw new Error('Course description is required');
  }
  if (!input.instructorId) {
    throw new Error('Instructor ID is required');
  }

  const now = new Date();
  return {
    id: generateCourseId(),
    title: input.title.trim(),
    description: input.description.trim(),
    category: input.category,
    difficultyLevel: input.difficultyLevel,
    instructorId: input.instructorId,
    status: 'draft', // Initial status is always draft
    thumbnail: input.thumbnail,
    prerequisites: input.prerequisites ?? [],
    estimatedDurationMinutes: input.estimatedDurationMinutes,
    createdAt: now,
    updatedAt: now,
  };
}

/**
 * Check if a status transition is valid (BP-DESIGN-001: Status Transition Map)
 */
export function canTransitionCourseStatus(from: CourseStatus, to: CourseStatus): boolean {
  return validCourseStatusTransitions[from].includes(to);
}

/**
 * Transition course status
 * @throws Error if transition is invalid
 */
export function transitionCourseStatus(course: Course, newStatus: CourseStatus): Course {
  if (!canTransitionCourseStatus(course.status, newStatus)) {
    throw new Error(`Invalid status transition from ${course.status} to ${newStatus}`);
  }
  return {
    ...course,
    status: newStatus,
    updatedAt: new Date(),
  };
}
