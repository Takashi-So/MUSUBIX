/**
 * Integration Tests
 * TSK-033: End-to-End Integration Tests
 * 
 * @see REQ-RENTAL-001 F001-F080
 * @see DES-RENTAL-001 §7
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  InMemoryPropertyRepository,
  InMemoryTenantRepository,
  InMemoryContractRepository,
  InMemoryMaintenanceRepository,
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
  activateContract,
  resetContractCounter,
} from '../src/entities/LeaseContract.js';
import {
  createMaintenanceRequest,
  assignStaff,
  startWork,
  completeMaintenanceRequest,
  resetMaintenanceCounter,
} from '../src/entities/MaintenanceRequest.js';
import type {
  CreatePropertyInput,
  CreateTenantInput,
  CreateContractInput,
  SubmitMaintenanceInput,
} from '../src/types/index.js';

describe('Integration Tests', () => {
  // 共通テストデータ
  const getValidPropertyInput = (): CreatePropertyInput => ({
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
  });

  const getValidTenantInput = (): CreateTenantInput => ({
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
  });

  beforeEach(() => {
    resetPropertyCounter();
    resetTenantCounter();
    resetContractCounter();
    resetMaintenanceCounter();
  });

  describe('Property Management Flow', () => {
    it('should manage property lifecycle', async () => {
      const propertyRepo = new InMemoryPropertyRepository();
      
      const property = createProperty(getValidPropertyInput());
      expect(property.status).toBe('available');
      
      await propertyRepo.create(property);
      
      const found = await propertyRepo.findById(property.id);
      expect(found?.id).toBe(property.id);
    });
  });

  describe('Tenant Management Flow', () => {
    it('should manage tenant lifecycle', async () => {
      const tenantRepo = new InMemoryTenantRepository();
      
      const tenant = createTenant(getValidTenantInput());
      // 初期ステータスは'prospective'（入居希望者）
      expect(tenant.status).toBe('prospective');
      
      await tenantRepo.create(tenant);
      
      const found = await tenantRepo.findById(tenant.id);
      expect(found?.name.lastName).toBe('山田');
    });
  });

  describe('Lease Contract Flow', () => {
    it('should manage lease contract lifecycle', async () => {
      const contractRepo = new InMemoryContractRepository();
      
      // 開始日を過去に設定
      const startDate = new Date();
      startDate.setDate(startDate.getDate() - 30);
      const endDate = new Date();
      endDate.setFullYear(endDate.getFullYear() + 1);

      const contractInput: CreateContractInput = {
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

      const contract = createLeaseContract(contractInput);
      expect(contract.status).toBe('draft');
      
      const activated = activateContract(contract);
      expect(activated.status).toBe('active');
      
      await contractRepo.create(activated);
      
      const found = await contractRepo.findById(activated.id);
      expect(found?.status).toBe('active');
    });
  });

  describe('Maintenance Request Flow', () => {
    it('should manage maintenance request lifecycle', async () => {
      const maintenanceRepo = new InMemoryMaintenanceRepository();

      const maintenanceInput: SubmitMaintenanceInput = {
        propertyId: 'PROP-20250101-001',
        tenantId: 'TEN-20250101-001',
        title: '水漏れ修理',
        description: 'キッチンの蛇口から水漏れがあります',
        urgency: 'medium',
      };

      // Step 1: Submit request
      const request = createMaintenanceRequest(maintenanceInput);
      expect(request.status).toBe('submitted');

      // Step 2: Assign staff
      const assigned = assignStaff(request, 'STAFF-001');
      expect(assigned.assignedTo).toBe('STAFF-001');
      expect(assigned.status).toBe('assigned');

      // Step 3: Start work
      const inProgress = startWork(assigned);
      expect(inProgress.status).toBe('in_progress');

      // Step 4: Complete maintenance
      const completed = completeMaintenanceRequest(inProgress, 15000);
      expect(completed.status).toBe('completed');
      expect(completed.cost?.amount).toBe(15000);

      await maintenanceRepo.create(completed);
      
      const found = await maintenanceRepo.findById(completed.id);
      expect(found?.status).toBe('completed');
    });
  });

  describe('End-to-End Scenario', () => {
    it('should handle complete rental workflow', async () => {
      const propertyRepo = new InMemoryPropertyRepository();
      const tenantRepo = new InMemoryTenantRepository();
      const contractRepo = new InMemoryContractRepository();

      // 1. Register property
      const property = createProperty(getValidPropertyInput());
      await propertyRepo.create(property);

      // 2. Register tenant
      const tenant = createTenant(getValidTenantInput());
      await tenantRepo.create(tenant);

      // 3. Create contract
      const startDate = new Date();
      startDate.setDate(startDate.getDate() - 30);
      const endDate = new Date();
      endDate.setFullYear(endDate.getFullYear() + 1);

      const contract = createLeaseContract({
        propertyId: property.id,
        tenantId: tenant.id,
        startDate,
        endDate,
        monthlyRent: 150000,
        deposit: 300000,
        keyMoney: 150000,
        maintenanceFee: 5000,
        guarantorId: 'GUA-20250101-001',
      });

      const activeContract = activateContract(contract);
      await contractRepo.create(activeContract);

      // Verify complete flow
      const foundProperty = await propertyRepo.findById(property.id);
      const foundTenant = await tenantRepo.findById(tenant.id);
      const foundContract = await contractRepo.findById(activeContract.id);

      expect(foundProperty).not.toBeNull();
      expect(foundTenant).not.toBeNull();
      expect(foundContract).not.toBeNull();
      expect(foundContract?.propertyId).toBe(foundProperty?.id);
      expect(foundContract?.tenantId).toBe(foundTenant?.id);
    });
  });
});
