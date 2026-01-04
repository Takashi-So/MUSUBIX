/**
 * Learner Entity
 * Traceability: REQ-ELEARN-001-F020, DES-ELEARN-001 §4.1.3
 */

import type { Learner, CreateLearnerInput, LearnerId } from './types.js';

// ID counter for testing (BP-TEST-001: Test Counter Reset)
let learnerCounter = 0;

/**
 * Reset learner counter for testing
 */
export function resetLearnerCounter(): void {
  learnerCounter = 0;
}

/**
 * Generate learner ID (BP-CODE-002: Date-based ID Format)
 * Format: LRN-YYYYMMDD-NNN
 */
function generateLearnerId(): LearnerId {
  const now = new Date();
  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, '');
  learnerCounter++;
  const counter = String(learnerCounter).padStart(3, '0');
  return `LRN-${dateStr}-${counter}` as LearnerId;
}

/**
 * Create a new Learner entity (BP-CODE-001: Entity Input DTO)
 */
export function createLearner(input: CreateLearnerInput): Learner {
  // Validation
  if (!input.name || input.name.trim().length === 0) {
    throw new Error('Learner name is required');
  }
  if (!input.email || !input.email.includes('@')) {
    throw new Error('Valid email is required');
  }

  const now = new Date();
  return {
    id: generateLearnerId(),
    name: input.name.trim(),
    email: input.email.toLowerCase().trim(),
    passwordHash: input.passwordHash,
    profilePicture: input.profilePicture,
    bio: input.bio,
    learningInterests: input.learningInterests ?? [],
    createdAt: now,
    updatedAt: now,
  };
}
