/**
 * Application Repository
 * TSK-019: ApplicationRepository
 * 
 * @see DES-RENTAL-001 §5.2
 */

import type {
  RentalApplication,
  RentalApplicationId,
  PropertyId,
  TenantId,
  ApplicationStatus,
} from '../types/index.js';

/**
 * Application Repository Interface
 */
export interface IApplicationRepository {
  create(application: RentalApplication): Promise<RentalApplication>;
  findById(id: RentalApplicationId): Promise<RentalApplication | null>;
  findByPropertyId(propertyId: PropertyId): Promise<RentalApplication[]>;
  findByTenantId(tenantId: TenantId): Promise<RentalApplication[]>;
  findByStatus(status: ApplicationStatus): Promise<RentalApplication[]>;
  update(application: RentalApplication): Promise<RentalApplication>;
  delete(id: RentalApplicationId): Promise<boolean>;
  findAll(): Promise<RentalApplication[]>;
}

/**
 * In-Memory Application Repository Implementation
 */
export class InMemoryApplicationRepository implements IApplicationRepository {
  private applications: Map<RentalApplicationId, RentalApplication> = new Map();

  async create(application: RentalApplication): Promise<RentalApplication> {
    if (this.applications.has(application.id)) {
      throw new Error(`Application with ID ${application.id} already exists`);
    }
    
    this.applications.set(application.id, { ...application });
    return { ...application };
  }

  async findById(id: RentalApplicationId): Promise<RentalApplication | null> {
    const application = this.applications.get(id);
    return application ? { ...application } : null;
  }

  async findByPropertyId(propertyId: PropertyId): Promise<RentalApplication[]> {
    const results: RentalApplication[] = [];
    for (const app of this.applications.values()) {
      if (app.propertyId === propertyId) {
        results.push({ ...app });
      }
    }
    // Sort by creation date (newest first)
    return results.sort((a, b) => b.createdAt.getTime() - a.createdAt.getTime());
  }

  async findByTenantId(tenantId: TenantId): Promise<RentalApplication[]> {
    const results: RentalApplication[] = [];
    for (const app of this.applications.values()) {
      if (app.tenantId === tenantId) {
        results.push({ ...app });
      }
    }
    return results.sort((a, b) => b.createdAt.getTime() - a.createdAt.getTime());
  }

  async findByStatus(status: ApplicationStatus): Promise<RentalApplication[]> {
    const results: RentalApplication[] = [];
    for (const app of this.applications.values()) {
      if (app.status === status) {
        results.push({ ...app });
      }
    }
    return results;
  }

  async update(application: RentalApplication): Promise<RentalApplication> {
    if (!this.applications.has(application.id)) {
      throw new Error(`Application with ID ${application.id} not found`);
    }
    
    this.applications.set(application.id, { ...application });
    return { ...application };
  }

  async delete(id: RentalApplicationId): Promise<boolean> {
    return this.applications.delete(id);
  }

  async findAll(): Promise<RentalApplication[]> {
    return Array.from(this.applications.values()).map(a => ({ ...a }));
  }

  /**
   * Find pending applications (submitted or screening)
   */
  async findPending(): Promise<RentalApplication[]> {
    const results: RentalApplication[] = [];
    for (const app of this.applications.values()) {
      if (app.status === 'submitted' || app.status === 'screening') {
        results.push({ ...app });
      }
    }
    return results.sort((a, b) => a.createdAt.getTime() - b.createdAt.getTime());
  }

  /**
   * Check if tenant has pending application for property
   */
  async hasPendingApplication(tenantId: TenantId, propertyId: PropertyId): Promise<boolean> {
    for (const app of this.applications.values()) {
      if (app.tenantId === tenantId && 
          app.propertyId === propertyId &&
          (app.status === 'submitted' || app.status === 'screening')) {
        return true;
      }
    }
    return false;
  }

  /**
   * Clear all data (for testing)
   */
  clear(): void {
    this.applications.clear();
  }
}
