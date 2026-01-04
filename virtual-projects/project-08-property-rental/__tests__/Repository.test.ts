/**
 * Repository Unit Tests
 * TSK-032: Repository Layer Unit Tests
 * 
 * @see REQ-RENTAL-001 F001-F080
 * @see DES-RENTAL-001 §5.1
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  InMemoryPropertyRepository,
  InMemoryTenantRepository,
  InMemoryContractRepository,
} from '../src/repositories/index.js';
import {
  createProperty,
  resetPropertyCounter,
} from '../src/entities/Property.js';
import {
  createTenant,
  resetTenantCounter,
} from '../src/entities/Tenant.js';
import {
  createLeaseContract,
  resetContractCounter,
} from '../src/entities/LeaseContract.js';
import type {
  CreatePropertyInput,
  CreateTenantInput,
  CreateContractInput,
} from '../src/types/index.js';

describe('Repository Layer', () => {
  beforeEach(() => {
    resetPropertyCounter();
    resetTenantCounter();
    resetContractCounter();
  });

  describe('PropertyRepository', () => {
    let repository: InMemoryPropertyRepository;
    let validPropertyInput: CreatePropertyInput;

    beforeEach(() => {
      repository = new InMemoryPropertyRepository();
      validPropertyInput = {
        ownerId: 'OWN-20250101-001',
        address: {
          postalCode: '150-0001',
          prefecture: '東京都',
          city: '渋谷区',
          street: '神宮前1-2-3',
        },
        propertyType: 'apartment',
        sizeSqm: 45,
        monthlyRent: 150000,
        deposit: 300000,
        keyMoney: 150000,
        maintenanceFee: 5000,
      };
    });

    it('should create and retrieve a property', async () => {
      const property = createProperty(validPropertyInput);
      await repository.create(property);
      
      const found = await repository.findById(property.id);
      expect(found).not.toBeNull();
      expect(found?.id).toBe(property.id);
    });

    it('should return null for non-existent property', async () => {
      const found = await repository.findById('PROP-99999999-999');
      expect(found).toBeNull();
    });

    it('should find all properties', async () => {
      const property1 = createProperty(validPropertyInput);
      const property2 = createProperty(validPropertyInput);
      
      await repository.create(property1);
      await repository.create(property2);
      
      const all = await repository.findAll();
      expect(all).toHaveLength(2);
    });

    it('should find properties by owner', async () => {
      const property = createProperty(validPropertyInput);
      await repository.create(property);
      
      const found = await repository.findByOwnerId('OWN-20250101-001');
      expect(found).toHaveLength(1);
    });

    it('should delete a property', async () => {
      const property = createProperty(validPropertyInput);
      await repository.create(property);
      await repository.delete(property.id);
      
      const found = await repository.findById(property.id);
      expect(found).toBeNull();
    });
  });

  describe('TenantRepository', () => {
    let repository: InMemoryTenantRepository;
    let validTenantInput: CreateTenantInput;

    beforeEach(() => {
      repository = new InMemoryTenantRepository();
      validTenantInput = {
        name: {
          firstName: '太郎',
          lastName: '山田',
          firstNameKana: 'タロウ',
          lastNameKana: 'ヤマダ',
        },
        contact: {
          phone: '090-1234-5678',
          email: 'taro@example.com',
          address: {
            postalCode: '150-0002',
            prefecture: '東京都',
            city: '渋谷区',
            street: '道玄坂1-1-1',
          },
        },
        identification: {
          type: '運転免許証',
          number: '123456789012',
          issuedDate: new Date('2020-01-01'),
          expiryDate: new Date('2030-01-01'),
        },
        employment: {
          companyName: 'テスト株式会社',
          position: 'エンジニア',
          employmentType: '正社員',
          yearsEmployed: 3,
          annualIncome: { amount: 5000000, currency: 'JPY' },
        },
        emergencyContact: {
          name: { firstName: '花子', lastName: '山田', firstNameKana: 'ハナコ', lastNameKana: 'ヤマダ' },
          relationship: '母',
          phone: '090-9876-5432',
        },
      };
    });

    it('should create and retrieve a tenant', async () => {
      const tenant = createTenant(validTenantInput);
      await repository.create(tenant);
      
      const found = await repository.findById(tenant.id);
      expect(found).not.toBeNull();
      expect(found?.name.lastName).toBe('山田');
    });

    it('should find by email', async () => {
      const tenant = createTenant(validTenantInput);
      await repository.create(tenant);
      
      const found = await repository.findByEmail('taro@example.com');
      expect(found).not.toBeNull();
      expect(found?.id).toBe(tenant.id);
    });
  });

  describe('ContractRepository', () => {
    let repository: InMemoryContractRepository;
    let validContractInput: CreateContractInput;

    beforeEach(() => {
      repository = new InMemoryContractRepository();
      const startDate = new Date();
      const endDate = new Date();
      endDate.setFullYear(endDate.getFullYear() + 1);
      
      validContractInput = {
        propertyId: 'PROP-20250101-001',
        tenantId: 'TEN-20250101-001',
        startDate,
        endDate,
        monthlyRent: 150000,
        deposit: 300000,
        keyMoney: 150000,
        maintenanceFee: 5000,
        guarantorId: 'GUA-20250101-001',
      };
    });

    it('should create and retrieve a contract', async () => {
      const contract = createLeaseContract(validContractInput);
      await repository.create(contract);
      
      const found = await repository.findById(contract.id);
      expect(found).not.toBeNull();
      expect(found?.propertyId).toBe('PROP-20250101-001');
    });

    it('should find contracts by tenant', async () => {
      const contract = createLeaseContract(validContractInput);
      await repository.create(contract);
      
      const found = await repository.findByTenantId('TEN-20250101-001');
      expect(found).toHaveLength(1);
    });

    it('should find active contracts', async () => {
      const contract = createLeaseContract(validContractInput);
      const activeContract = { ...contract, status: 'active' as const };
      await repository.create(activeContract);
      
      const active = await repository.findByStatus('active');
      expect(active.length).toBeGreaterThanOrEqual(1);
    });
  });
});
