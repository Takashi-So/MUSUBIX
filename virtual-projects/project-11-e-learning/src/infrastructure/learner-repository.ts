/**
 * InMemory Learner Repository
 * Traceability: DES-ELEARN-001 §6.1
 */

import type { Learner, LearnerId } from '../domain/types.js';

export interface LearnerRepository {
  save(learner: Learner): Promise<void>;
  findById(id: LearnerId): Promise<Learner | null>;
  findByEmail(email: string): Promise<Learner | null>;
  findAll(): Promise<Learner[]>;
  delete(id: LearnerId): Promise<void>;
}

export class InMemoryLearnerRepository implements LearnerRepository {
  private learners: Map<LearnerId, Learner> = new Map();

  async save(learner: Learner): Promise<void> {
    this.learners.set(learner.id, { ...learner });
  }

  async findById(id: LearnerId): Promise<Learner | null> {
    const learner = this.learners.get(id);
    return learner ? { ...learner } : null;
  }

  async findByEmail(email: string): Promise<Learner | null> {
    const normalizedEmail = email.toLowerCase().trim();
    for (const learner of this.learners.values()) {
      if (learner.email === normalizedEmail) {
        return { ...learner };
      }
    }
    return null;
  }

  async findAll(): Promise<Learner[]> {
    return Array.from(this.learners.values()).map(l => ({ ...l }));
  }

  async delete(id: LearnerId): Promise<void> {
    this.learners.delete(id);
  }

  // For testing
  clear(): void {
    this.learners.clear();
  }
}
