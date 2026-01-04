/**
 * Maintenance Repository
 * TSK-018: MaintenanceRepository
 * 
 * @see DES-RENTAL-001 §5.5
 */

import type {
  MaintenanceRequest,
  MaintenanceRequestId,
  PropertyId,
  TenantId,
  MaintenanceStatus,
  UrgencyLevel,
} from '../types/index.js';

/**
 * Maintenance Repository Interface
 */
export interface IMaintenanceRepository {
  create(request: MaintenanceRequest): Promise<MaintenanceRequest>;
  findById(id: MaintenanceRequestId): Promise<MaintenanceRequest | null>;
  findByPropertyId(propertyId: PropertyId): Promise<MaintenanceRequest[]>;
  findByTenantId(tenantId: TenantId): Promise<MaintenanceRequest[]>;
  findByStatus(status: MaintenanceStatus): Promise<MaintenanceRequest[]>;
  findByUrgency(urgency: UrgencyLevel): Promise<MaintenanceRequest[]>;
  update(request: MaintenanceRequest): Promise<MaintenanceRequest>;
  delete(id: MaintenanceRequestId): Promise<boolean>;
  findAll(): Promise<MaintenanceRequest[]>;
}

/**
 * In-Memory Maintenance Repository Implementation
 */
export class InMemoryMaintenanceRepository implements IMaintenanceRepository {
  private requests: Map<MaintenanceRequestId, MaintenanceRequest> = new Map();

  async create(request: MaintenanceRequest): Promise<MaintenanceRequest> {
    if (this.requests.has(request.id)) {
      throw new Error(`Maintenance request with ID ${request.id} already exists`);
    }
    
    this.requests.set(request.id, { ...request });
    return { ...request };
  }

  async findById(id: MaintenanceRequestId): Promise<MaintenanceRequest | null> {
    const request = this.requests.get(id);
    return request ? { ...request } : null;
  }

  async findByPropertyId(propertyId: PropertyId): Promise<MaintenanceRequest[]> {
    const results: MaintenanceRequest[] = [];
    for (const request of this.requests.values()) {
      if (request.propertyId === propertyId) {
        results.push({ ...request });
      }
    }
    // Sort by creation date (newest first)
    return results.sort((a, b) => b.createdAt.getTime() - a.createdAt.getTime());
  }

  async findByTenantId(tenantId: TenantId): Promise<MaintenanceRequest[]> {
    const results: MaintenanceRequest[] = [];
    for (const request of this.requests.values()) {
      if (request.tenantId === tenantId) {
        results.push({ ...request });
      }
    }
    return results.sort((a, b) => b.createdAt.getTime() - a.createdAt.getTime());
  }

  async findByStatus(status: MaintenanceStatus): Promise<MaintenanceRequest[]> {
    const results: MaintenanceRequest[] = [];
    for (const request of this.requests.values()) {
      if (request.status === status) {
        results.push({ ...request });
      }
    }
    return results;
  }

  async findByUrgency(urgency: UrgencyLevel): Promise<MaintenanceRequest[]> {
    const results: MaintenanceRequest[] = [];
    for (const request of this.requests.values()) {
      if (request.urgency === urgency) {
        results.push({ ...request });
      }
    }
    return results;
  }

  async update(request: MaintenanceRequest): Promise<MaintenanceRequest> {
    if (!this.requests.has(request.id)) {
      throw new Error(`Maintenance request with ID ${request.id} not found`);
    }
    
    this.requests.set(request.id, { ...request });
    return { ...request };
  }

  async delete(id: MaintenanceRequestId): Promise<boolean> {
    return this.requests.delete(id);
  }

  async findAll(): Promise<MaintenanceRequest[]> {
    return Array.from(this.requests.values()).map(r => ({ ...r }));
  }

  /**
   * Find open requests (not completed or cancelled)
   */
  async findOpen(): Promise<MaintenanceRequest[]> {
    const results: MaintenanceRequest[] = [];
    for (const request of this.requests.values()) {
      if (request.status !== 'completed' && request.status !== 'cancelled') {
        results.push({ ...request });
      }
    }
    // Sort by urgency (emergency first) then by date
    const urgencyOrder: UrgencyLevel[] = ['emergency', 'high', 'medium', 'low'];
    return results.sort((a, b) => {
      const urgencyDiff = urgencyOrder.indexOf(a.urgency) - urgencyOrder.indexOf(b.urgency);
      if (urgencyDiff !== 0) return urgencyDiff;
      return a.createdAt.getTime() - b.createdAt.getTime();
    });
  }

  /**
   * Clear all data (for testing)
   */
  clear(): void {
    this.requests.clear();
  }
}
