/**
 * Contract Repository
 * TSK-016: ContractRepository
 * 
 * @see DES-RENTAL-001 §5.3
 */

import type {
  LeaseContract,
  LeaseContractId,
  PropertyId,
  TenantId,
  ContractStatus,
} from '../types/index.js';
import { isContractExpiringWithinDays } from '../entities/LeaseContract.js';

/**
 * Contract Repository Interface
 */
export interface IContractRepository {
  create(contract: LeaseContract): Promise<LeaseContract>;
  findById(id: LeaseContractId): Promise<LeaseContract | null>;
  findByPropertyId(propertyId: PropertyId): Promise<LeaseContract[]>;
  findByTenantId(tenantId: TenantId): Promise<LeaseContract[]>;
  findByStatus(status: ContractStatus): Promise<LeaseContract[]>;
  findExpiring(days: number): Promise<LeaseContract[]>;
  update(contract: LeaseContract): Promise<LeaseContract>;
  delete(id: LeaseContractId): Promise<boolean>;
  findAll(): Promise<LeaseContract[]>;
}

/**
 * In-Memory Contract Repository Implementation
 */
export class InMemoryContractRepository implements IContractRepository {
  private contracts: Map<LeaseContractId, LeaseContract> = new Map();

  async create(contract: LeaseContract): Promise<LeaseContract> {
    if (this.contracts.has(contract.id)) {
      throw new Error(`Contract with ID ${contract.id} already exists`);
    }
    
    this.contracts.set(contract.id, { ...contract });
    return { ...contract };
  }

  async findById(id: LeaseContractId): Promise<LeaseContract | null> {
    const contract = this.contracts.get(id);
    return contract ? { ...contract } : null;
  }

  async findByPropertyId(propertyId: PropertyId): Promise<LeaseContract[]> {
    const results: LeaseContract[] = [];
    for (const contract of this.contracts.values()) {
      if (contract.propertyId === propertyId) {
        results.push({ ...contract });
      }
    }
    return results;
  }

  async findByTenantId(tenantId: TenantId): Promise<LeaseContract[]> {
    const results: LeaseContract[] = [];
    for (const contract of this.contracts.values()) {
      if (contract.tenantId === tenantId) {
        results.push({ ...contract });
      }
    }
    return results;
  }

  async findByStatus(status: ContractStatus): Promise<LeaseContract[]> {
    const results: LeaseContract[] = [];
    for (const contract of this.contracts.values()) {
      if (contract.status === status) {
        results.push({ ...contract });
      }
    }
    return results;
  }

  async findExpiring(days: number): Promise<LeaseContract[]> {
    const results: LeaseContract[] = [];
    for (const contract of this.contracts.values()) {
      if (isContractExpiringWithinDays(contract, days)) {
        results.push({ ...contract });
      }
    }
    return results;
  }

  async update(contract: LeaseContract): Promise<LeaseContract> {
    if (!this.contracts.has(contract.id)) {
      throw new Error(`Contract with ID ${contract.id} not found`);
    }
    
    this.contracts.set(contract.id, { ...contract });
    return { ...contract };
  }

  async delete(id: LeaseContractId): Promise<boolean> {
    return this.contracts.delete(id);
  }

  async findAll(): Promise<LeaseContract[]> {
    return Array.from(this.contracts.values()).map(c => ({ ...c }));
  }

  /**
   * Clear all data (for testing)
   */
  clear(): void {
    this.contracts.clear();
  }
}
