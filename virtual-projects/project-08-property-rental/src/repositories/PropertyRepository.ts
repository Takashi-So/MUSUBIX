/**
 * Property Repository
 * TSK-012: PropertyRepository
 * 
 * @see DES-RENTAL-001 §5.1
 */

import type {
  Property,
  PropertyId,
  OwnerId,
  PropertySearchCriteria,
} from '../types/index.js';
import { matchesSearchCriteria } from '../entities/Property.js';

/**
 * Property Repository Interface
 */
export interface IPropertyRepository {
  create(property: Property): Promise<Property>;
  findById(id: PropertyId): Promise<Property | null>;
  findByOwnerId(ownerId: OwnerId): Promise<Property[]>;
  update(property: Property): Promise<Property>;
  delete(id: PropertyId): Promise<boolean>;
  search(criteria: PropertySearchCriteria): Promise<Property[]>;
  findAll(): Promise<Property[]>;
}

/**
 * In-Memory Property Repository Implementation
 */
export class InMemoryPropertyRepository implements IPropertyRepository {
  private properties: Map<PropertyId, Property> = new Map();

  async create(property: Property): Promise<Property> {
    if (this.properties.has(property.id)) {
      throw new Error(`Property with ID ${property.id} already exists`);
    }
    this.properties.set(property.id, { ...property });
    return { ...property };
  }

  async findById(id: PropertyId): Promise<Property | null> {
    const property = this.properties.get(id);
    return property ? { ...property } : null;
  }

  async findByOwnerId(ownerId: OwnerId): Promise<Property[]> {
    const results: Property[] = [];
    for (const property of this.properties.values()) {
      if (property.ownerId === ownerId) {
        results.push({ ...property });
      }
    }
    return results;
  }

  async update(property: Property): Promise<Property> {
    if (!this.properties.has(property.id)) {
      throw new Error(`Property with ID ${property.id} not found`);
    }
    this.properties.set(property.id, { ...property });
    return { ...property };
  }

  async delete(id: PropertyId): Promise<boolean> {
    return this.properties.delete(id);
  }

  async search(criteria: PropertySearchCriteria): Promise<Property[]> {
    const results: Property[] = [];
    for (const property of this.properties.values()) {
      if (matchesSearchCriteria(property, criteria)) {
        results.push({ ...property });
      }
    }
    return results;
  }

  async findAll(): Promise<Property[]> {
    return Array.from(this.properties.values()).map(p => ({ ...p }));
  }

  /**
   * Clear all data (for testing)
   */
  clear(): void {
    this.properties.clear();
  }
}
