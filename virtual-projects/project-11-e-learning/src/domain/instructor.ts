/**
 * Instructor Entity
 * Traceability: REQ-ELEARN-001-F000, DES-ELEARN-001 §4.1.0
 */

import type { Instructor, CreateInstructorInput, InstructorId } from './types.js';

// ID counter for testing (BP-TEST-001: Test Counter Reset)
let instructorCounter = 0;

/**
 * Reset instructor counter for testing
 */
export function resetInstructorCounter(): void {
  instructorCounter = 0;
}

/**
 * Generate instructor ID (BP-CODE-002: Date-based ID Format)
 * Format: INS-YYYYMMDD-NNN
 */
function generateInstructorId(): InstructorId {
  const now = new Date();
  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, '');
  instructorCounter++;
  const counter = String(instructorCounter).padStart(3, '0');
  return `INS-${dateStr}-${counter}` as InstructorId;
}

/**
 * Create a new Instructor entity (BP-CODE-001: Entity Input DTO)
 */
export function createInstructor(input: CreateInstructorInput): Instructor {
  // Validation
  if (!input.name || input.name.trim().length === 0) {
    throw new Error('Instructor name is required');
  }
  if (!input.email || !input.email.includes('@')) {
    throw new Error('Valid email is required');
  }
  if (!input.bio || input.bio.trim().length === 0) {
    throw new Error('Instructor bio is required');
  }

  const now = new Date();
  return {
    id: generateInstructorId(),
    name: input.name.trim(),
    email: input.email.toLowerCase().trim(),
    passwordHash: input.passwordHash,
    bio: input.bio.trim(),
    profilePicture: input.profilePicture,
    expertiseAreas: input.expertiseAreas ?? [],
    createdAt: now,
    updatedAt: now,
  };
}
