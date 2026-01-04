/**
 * Guarantor Repository
 * TSK-015: GuarantorRepository
 * 
 * @see DES-RENTAL-001 §5.2
 */

import type {
  Guarantor,
  GuarantorId,
} from '../types/index.js';

/**
 * Guarantor Repository Interface
 */
export interface IGuarantorRepository {
  create(guarantor: Guarantor): Promise<Guarantor>;
  findById(id: GuarantorId): Promise<Guarantor | null>;
  update(guarantor: Guarantor): Promise<Guarantor>;
  delete(id: GuarantorId): Promise<boolean>;
  findAll(): Promise<Guarantor[]>;
}

/**
 * In-Memory Guarantor Repository Implementation
 */
export class InMemoryGuarantorRepository implements IGuarantorRepository {
  private guarantors: Map<GuarantorId, Guarantor> = new Map();

  async create(guarantor: Guarantor): Promise<Guarantor> {
    if (this.guarantors.has(guarantor.id)) {
      throw new Error(`Guarantor with ID ${guarantor.id} already exists`);
    }
    
    this.guarantors.set(guarantor.id, { ...guarantor });
    return { ...guarantor };
  }

  async findById(id: GuarantorId): Promise<Guarantor | null> {
    const guarantor = this.guarantors.get(id);
    return guarantor ? { ...guarantor } : null;
  }

  async update(guarantor: Guarantor): Promise<Guarantor> {
    if (!this.guarantors.has(guarantor.id)) {
      throw new Error(`Guarantor with ID ${guarantor.id} not found`);
    }
    
    this.guarantors.set(guarantor.id, { ...guarantor });
    return { ...guarantor };
  }

  async delete(id: GuarantorId): Promise<boolean> {
    return this.guarantors.delete(id);
  }

  async findAll(): Promise<Guarantor[]> {
    return Array.from(this.guarantors.values()).map(g => ({ ...g }));
  }

  /**
   * Clear all data (for testing)
   */
  clear(): void {
    this.guarantors.clear();
  }
}
