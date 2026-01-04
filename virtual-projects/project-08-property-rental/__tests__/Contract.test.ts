/**
 * LeaseContract Entity Tests
 * TSK-028: LeaseContract Entity Unit Tests
 * 
 * @see REQ-RENTAL-001 F030-F033
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createLeaseContract,
  activateContract,
  renewContract,
  terminateContract,
  resetContractCounter,
} from '../src/entities/LeaseContract.js';
import type { CreateContractInput } from '../src/types/index.js';

describe('LeaseContract Entity', () => {
  let validInput: CreateContractInput;

  beforeEach(() => {
    resetContractCounter();
    // 開始日を過去に設定（契約有効化のため）
    const pastStart = new Date();
    pastStart.setDate(pastStart.getDate() - 30);
    const futureEnd = new Date();
    futureEnd.setFullYear(futureEnd.getFullYear() + 1);
    
    validInput = {
      propertyId: 'PROP-20250101-001',
      tenantId: 'TEN-20250101-001',
      ownerId: 'OWN-20250101-001',
      startDate: pastStart,
      endDate: futureEnd,
      monthlyRent: 150000,
      deposit: 300000,
      keyMoney: 150000,
      maintenanceFee: 5000,
      guarantorId: 'GUA-20250101-001',
      paymentDueDay: 27,
      renewalTerms: '1年ごとに更新可',
    };
  });

  describe('createLeaseContract', () => {
    it('should create a lease contract with valid inputs', () => {
      const contract = createLeaseContract(validInput);

      expect(contract.id).toMatch(/^LEASE-\d{8}-\d{3}$/);
      expect(contract.propertyId).toBe('PROP-20250101-001');
      expect(contract.tenantId).toBe('TEN-20250101-001');
      expect(contract.status).toBe('draft');
    });

    it('should throw error for contract period less than 1 month', () => {
      const shortEnd = new Date(validInput.startDate);
      shortEnd.setDate(shortEnd.getDate() + 10);
      const invalidInput = { ...validInput, endDate: shortEnd };
      expect(() => createLeaseContract(invalidInput)).toThrow('Contract duration must be at least 1 month');
    });

    it('should throw error for contract period exceeding 5 years', () => {
      const longEnd = new Date(validInput.startDate);
      longEnd.setFullYear(longEnd.getFullYear() + 6);
      const invalidInput = { ...validInput, endDate: longEnd };
      expect(() => createLeaseContract(invalidInput)).toThrow('Contract duration cannot exceed 5 years');
    });

    it('should throw error for zero monthly rent', () => {
      const invalidInput = { ...validInput, monthlyRent: 0 };
      expect(() => createLeaseContract(invalidInput)).toThrow('Monthly rent must be greater than 0');
    });
  });

  describe('activateContract', () => {
    it('should activate a draft contract', () => {
      const contract = createLeaseContract(validInput);
      const activated = activateContract(contract);
      expect(activated.status).toBe('active');
    });

    it('should throw error when activating non-draft contract', () => {
      const contract = createLeaseContract(validInput);
      const activated = activateContract(contract);
      expect(() => activateContract(activated)).toThrow('Only draft contracts can be activated');
    });
  });

  describe('renewContract', () => {
    it('should renew an active contract and return new contract', () => {
      const contract = createLeaseContract(validInput);
      const activated = activateContract(contract);
      
      const newEndDate = new Date();
      newEndDate.setFullYear(newEndDate.getFullYear() + 2);
      const renewed = renewContract(activated, newEndDate);

      // renewContractは新しい契約を返すのでstatusは'active'
      expect(renewed.status).toBe('active');
      expect(renewed.renewedFromId).toBe(activated.id);
      expect(renewed.id).not.toBe(activated.id);
    });
  });

  describe('terminateContract', () => {
    it('should terminate contract', () => {
      const contract = createLeaseContract(validInput);
      const activated = activateContract(contract);
      const terminated = terminateContract(activated, 'tenant_request');

      expect(terminated.status).toBe('terminated');
    });
  });
});
