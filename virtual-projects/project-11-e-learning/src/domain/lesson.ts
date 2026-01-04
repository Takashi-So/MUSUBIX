/**
 * Lesson Entity
 * Traceability: REQ-ELEARN-001-F010, F011, DES-ELEARN-001 §4.1.2
 */

import type { Lesson, CreateLessonInput, LessonId } from './types.js';

// ID counter for testing (BP-TEST-001: Test Counter Reset)
let lessonCounter = 0;

/**
 * Reset lesson counter for testing
 */
export function resetLessonCounter(): void {
  lessonCounter = 0;
}

/**
 * Generate lesson ID (BP-CODE-002: Date-based ID Format)
 * Format: LES-YYYYMMDD-NNN
 */
function generateLessonId(): LessonId {
  const now = new Date();
  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, '');
  lessonCounter++;
  const counter = String(lessonCounter).padStart(3, '0');
  return `LES-${dateStr}-${counter}` as LessonId;
}

/**
 * Create a new Lesson entity (BP-CODE-001: Entity Input DTO)
 */
export function createLesson(input: CreateLessonInput): Lesson {
  // Validation
  if (!input.title || input.title.trim().length === 0) {
    throw new Error('Lesson title is required');
  }
  if (!input.courseId) {
    throw new Error('Course ID is required');
  }
  if (!input.content || input.content.trim().length === 0) {
    throw new Error('Lesson content is required');
  }
  if (input.order < 1) {
    throw new Error('Lesson order must be at least 1');
  }

  const now = new Date();
  return {
    id: generateLessonId(),
    courseId: input.courseId,
    title: input.title.trim(),
    contentType: input.contentType,
    content: input.content.trim(),
    order: input.order,
    durationMinutes: input.durationMinutes,
    createdAt: now,
    updatedAt: now,
  };
}

/**
 * Update lesson order
 */
export function updateLessonOrder(lesson: Lesson, newOrder: number): Lesson {
  if (newOrder < 1) {
    throw new Error('Lesson order must be at least 1');
  }
  return {
    ...lesson,
    order: newOrder,
    updatedAt: new Date(),
  };
}
