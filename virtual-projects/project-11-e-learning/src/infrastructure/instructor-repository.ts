/**
 * InMemory Instructor Repository
 * Traceability: DES-ELEARN-001 §6.1
 */

import type { Instructor, InstructorId } from '../domain/types.js';

export interface InstructorRepository {
  save(instructor: Instructor): Promise<void>;
  findById(id: InstructorId): Promise<Instructor | null>;
  findByEmail(email: string): Promise<Instructor | null>;
  findAll(): Promise<Instructor[]>;
  delete(id: InstructorId): Promise<void>;
}

export class InMemoryInstructorRepository implements InstructorRepository {
  private instructors: Map<InstructorId, Instructor> = new Map();

  async save(instructor: Instructor): Promise<void> {
    this.instructors.set(instructor.id, { ...instructor });
  }

  async findById(id: InstructorId): Promise<Instructor | null> {
    const instructor = this.instructors.get(id);
    return instructor ? { ...instructor } : null;
  }

  async findByEmail(email: string): Promise<Instructor | null> {
    const normalizedEmail = email.toLowerCase().trim();
    for (const instructor of this.instructors.values()) {
      if (instructor.email === normalizedEmail) {
        return { ...instructor };
      }
    }
    return null;
  }

  async findAll(): Promise<Instructor[]> {
    return Array.from(this.instructors.values()).map(i => ({ ...i }));
  }

  async delete(id: InstructorId): Promise<void> {
    this.instructors.delete(id);
  }

  // For testing
  clear(): void {
    this.instructors.clear();
  }
}
