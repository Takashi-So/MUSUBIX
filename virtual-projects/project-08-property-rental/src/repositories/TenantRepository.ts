/**
 * Tenant Repository
 * TSK-014: TenantRepository
 * 
 * @see DES-RENTAL-001 §5.2
 */

import type {
  Tenant,
  TenantId,
  TenantStatus,
} from '../types/index.js';

/**
 * Tenant Repository Interface
 */
export interface ITenantRepository {
  create(tenant: Tenant): Promise<Tenant>;
  findById(id: TenantId): Promise<Tenant | null>;
  findByEmail(email: string): Promise<Tenant | null>;
  findByStatus(status: TenantStatus): Promise<Tenant[]>;
  update(tenant: Tenant): Promise<Tenant>;
  delete(id: TenantId): Promise<boolean>;
  findAll(): Promise<Tenant[]>;
}

/**
 * In-Memory Tenant Repository Implementation
 */
export class InMemoryTenantRepository implements ITenantRepository {
  private tenants: Map<TenantId, Tenant> = new Map();

  async create(tenant: Tenant): Promise<Tenant> {
    if (this.tenants.has(tenant.id)) {
      throw new Error(`Tenant with ID ${tenant.id} already exists`);
    }
    
    // Check email uniqueness
    for (const existing of this.tenants.values()) {
      if (existing.contact.email === tenant.contact.email) {
        throw new Error(`Tenant with email ${tenant.contact.email} already exists`);
      }
    }
    
    this.tenants.set(tenant.id, { ...tenant });
    return { ...tenant };
  }

  async findById(id: TenantId): Promise<Tenant | null> {
    const tenant = this.tenants.get(id);
    return tenant ? { ...tenant } : null;
  }

  async findByEmail(email: string): Promise<Tenant | null> {
    for (const tenant of this.tenants.values()) {
      if (tenant.contact.email === email) {
        return { ...tenant };
      }
    }
    return null;
  }

  async findByStatus(status: TenantStatus): Promise<Tenant[]> {
    const results: Tenant[] = [];
    for (const tenant of this.tenants.values()) {
      if (tenant.status === status) {
        results.push({ ...tenant });
      }
    }
    return results;
  }

  async update(tenant: Tenant): Promise<Tenant> {
    if (!this.tenants.has(tenant.id)) {
      throw new Error(`Tenant with ID ${tenant.id} not found`);
    }
    
    // Check email uniqueness (excluding self)
    for (const existing of this.tenants.values()) {
      if (existing.id !== tenant.id && existing.contact.email === tenant.contact.email) {
        throw new Error(`Tenant with email ${tenant.contact.email} already exists`);
      }
    }
    
    this.tenants.set(tenant.id, { ...tenant });
    return { ...tenant };
  }

  async delete(id: TenantId): Promise<boolean> {
    return this.tenants.delete(id);
  }

  async findAll(): Promise<Tenant[]> {
    return Array.from(this.tenants.values()).map(t => ({ ...t }));
  }

  /**
   * Clear all data (for testing)
   */
  clear(): void {
    this.tenants.clear();
  }
}
