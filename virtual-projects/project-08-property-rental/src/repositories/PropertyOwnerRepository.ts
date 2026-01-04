/**
 * PropertyOwner Repository
 * TSK-013: PropertyOwnerRepository
 * 
 * @see DES-RENTAL-001 §5.1
 */

import type {
  PropertyOwner,
  OwnerId,
} from '../types/index.js';

/**
 * PropertyOwner Repository Interface
 */
export interface IPropertyOwnerRepository {
  create(owner: PropertyOwner): Promise<PropertyOwner>;
  findById(id: OwnerId): Promise<PropertyOwner | null>;
  findByEmail(email: string): Promise<PropertyOwner | null>;
  update(owner: PropertyOwner): Promise<PropertyOwner>;
  delete(id: OwnerId): Promise<boolean>;
  findAll(): Promise<PropertyOwner[]>;
}

/**
 * In-Memory PropertyOwner Repository Implementation
 */
export class InMemoryPropertyOwnerRepository implements IPropertyOwnerRepository {
  private owners: Map<OwnerId, PropertyOwner> = new Map();

  async create(owner: PropertyOwner): Promise<PropertyOwner> {
    if (this.owners.has(owner.id)) {
      throw new Error(`Owner with ID ${owner.id} already exists`);
    }
    
    // Check email uniqueness
    for (const existing of this.owners.values()) {
      if (existing.contact.email === owner.contact.email) {
        throw new Error(`Owner with email ${owner.contact.email} already exists`);
      }
    }
    
    this.owners.set(owner.id, { ...owner });
    return { ...owner };
  }

  async findById(id: OwnerId): Promise<PropertyOwner | null> {
    const owner = this.owners.get(id);
    return owner ? { ...owner } : null;
  }

  async findByEmail(email: string): Promise<PropertyOwner | null> {
    for (const owner of this.owners.values()) {
      if (owner.contact.email === email) {
        return { ...owner };
      }
    }
    return null;
  }

  async update(owner: PropertyOwner): Promise<PropertyOwner> {
    if (!this.owners.has(owner.id)) {
      throw new Error(`Owner with ID ${owner.id} not found`);
    }
    
    // Check email uniqueness (excluding self)
    for (const existing of this.owners.values()) {
      if (existing.id !== owner.id && existing.contact.email === owner.contact.email) {
        throw new Error(`Owner with email ${owner.contact.email} already exists`);
      }
    }
    
    this.owners.set(owner.id, { ...owner });
    return { ...owner };
  }

  async delete(id: OwnerId): Promise<boolean> {
    return this.owners.delete(id);
  }

  async findAll(): Promise<PropertyOwner[]> {
    return Array.from(this.owners.values()).map(o => ({ ...o }));
  }

  /**
   * Clear all data (for testing)
   */
  clear(): void {
    this.owners.clear();
  }
}
