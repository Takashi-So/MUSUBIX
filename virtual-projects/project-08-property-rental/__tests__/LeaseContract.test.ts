/**
 * LeaseContract Entity Tests
 * 
 * @requirement REQ-RENTAL-001-F020 (Contract Creation)
 * @requirement REQ-RENTAL-001-F021 (Contract Termination)
 * @design DES-RENTAL-001-C003
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  LeaseContract,
  createLeaseContract,
  CreateLeaseContractInput,
  canTransitionContractStatus,
  terminateContract,
} from '../src/entities/LeaseContract.js';
import {
  resetAllCounters,
  ContractStatus,
} from '../src/types/common.js';

describe('LeaseContract Entity', () => {
  beforeEach(() => {
    resetAllCounters();
  });

  describe('createLeaseContract', () => {
    it('should create a lease contract with valid input', () => {
      const input: CreateLeaseContractInput = {
        propertyId: { value: 'PROP-20260106-001' },
        tenantId: { value: 'TEN-20260106-001' },
        startDate: new Date('2026-02-01'),
        endDate: new Date('2028-01-31'),
        monthlyRent: 150000,
        deposit: 300000,
      };

      const result = createLeaseContract(input);

      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        const contract = result.value;
        expect(contract.id.value).toMatch(/^LEASE-\d{8}-001$/);
        expect(contract.propertyId.value).toBe('PROP-20260106-001');
        expect(contract.tenantId.value).toBe('TEN-20260106-001');
        expect(contract.monthlyRent.amount).toBe(150000);
        expect(contract.deposit.amount).toBe(300000);
        expect(contract.status).toBe('draft');
        expect(contract.version).toBe(1);
      }
    });

    it('should reject end date before start date', () => {
      const input: CreateLeaseContractInput = {
        propertyId: { value: 'PROP-20260106-001' },
        tenantId: { value: 'TEN-20260106-001' },
        startDate: new Date('2026-02-01'),
        endDate: new Date('2026-01-01'), // Before start
        monthlyRent: 150000,
        deposit: 300000,
      };

      const result = createLeaseContract(input);

      expect(result.isErr()).toBe(true);
      if (result.isErr()) {
        expect(result.error.message).toContain('end date');
      }
    });

    it('should reject negative monthly rent', () => {
      const input: CreateLeaseContractInput = {
        propertyId: { value: 'PROP-20260106-001' },
        tenantId: { value: 'TEN-20260106-001' },
        startDate: new Date('2026-02-01'),
        endDate: new Date('2028-01-31'),
        monthlyRent: -10000, // Invalid
        deposit: 300000,
      };

      const result = createLeaseContract(input);

      expect(result.isErr()).toBe(true);
    });

    it('should reject negative deposit', () => {
      const input: CreateLeaseContractInput = {
        propertyId: { value: 'PROP-20260106-001' },
        tenantId: { value: 'TEN-20260106-001' },
        startDate: new Date('2026-02-01'),
        endDate: new Date('2028-01-31'),
        monthlyRent: 150000,
        deposit: -50000, // Invalid
      };

      const result = createLeaseContract(input);

      expect(result.isErr()).toBe(true);
    });
  });

  describe('Contract Status Transitions', () => {
    it('should allow draft → active transition', () => {
      expect(canTransitionContractStatus('draft', 'active')).toBe(true);
    });

    it('should allow active → terminated transition', () => {
      expect(canTransitionContractStatus('active', 'terminated')).toBe(true);
    });

    it('should allow active → expired transition', () => {
      expect(canTransitionContractStatus('active', 'expired')).toBe(true);
    });

    it('should NOT allow draft → terminated transition', () => {
      expect(canTransitionContractStatus('draft', 'terminated')).toBe(false);
    });

    it('should NOT allow terminated → any transition', () => {
      expect(canTransitionContractStatus('terminated', 'active')).toBe(false);
      expect(canTransitionContractStatus('terminated', 'draft')).toBe(false);
    });

    it('should NOT allow expired → any transition', () => {
      expect(canTransitionContractStatus('expired', 'active')).toBe(false);
      expect(canTransitionContractStatus('expired', 'draft')).toBe(false);
    });
  });

  describe('terminateContract', () => {
    it('should terminate an active contract with natural-expiry', () => {
      const input: CreateLeaseContractInput = {
        propertyId: { value: 'PROP-20260106-001' },
        tenantId: { value: 'TEN-20260106-001' },
        startDate: new Date('2026-02-01'),
        endDate: new Date('2028-01-31'),
        monthlyRent: 150000,
        deposit: 300000,
      };

      const createResult = createLeaseContract(input);
      expect(createResult.isOk()).toBe(true);
      if (!createResult.isOk()) return;

      // First activate the contract
      const contract = { ...createResult.value, status: 'active' as ContractStatus };
      
      const terminateResult = terminateContract(contract, 'natural-expiry');

      expect(terminateResult.isOk()).toBe(true);
      if (terminateResult.isOk()) {
        expect(terminateResult.value.status).toBe('terminated');
        expect(terminateResult.value.terminationReason).toBe('natural-expiry');
        expect(terminateResult.value.terminationDate).toBeInstanceOf(Date);
      }
    });

    it('should terminate with early-termination reason', () => {
      const input: CreateLeaseContractInput = {
        propertyId: { value: 'PROP-20260106-001' },
        tenantId: { value: 'TEN-20260106-001' },
        startDate: new Date('2026-02-01'),
        endDate: new Date('2028-01-31'),
        monthlyRent: 150000,
        deposit: 300000,
      };

      const createResult = createLeaseContract(input);
      expect(createResult.isOk()).toBe(true);
      if (!createResult.isOk()) return;

      const contract = { ...createResult.value, status: 'active' as ContractStatus };
      
      const terminateResult = terminateContract(contract, 'early-termination');

      expect(terminateResult.isOk()).toBe(true);
      if (terminateResult.isOk()) {
        expect(terminateResult.value.terminationReason).toBe('early-termination');
      }
    });

    it('should terminate with breach reason', () => {
      const input: CreateLeaseContractInput = {
        propertyId: { value: 'PROP-20260106-001' },
        tenantId: { value: 'TEN-20260106-001' },
        startDate: new Date('2026-02-01'),
        endDate: new Date('2028-01-31'),
        monthlyRent: 150000,
        deposit: 300000,
      };

      const createResult = createLeaseContract(input);
      expect(createResult.isOk()).toBe(true);
      if (!createResult.isOk()) return;

      const contract = { ...createResult.value, status: 'active' as ContractStatus };
      
      const terminateResult = terminateContract(contract, 'breach');

      expect(terminateResult.isOk()).toBe(true);
      if (terminateResult.isOk()) {
        expect(terminateResult.value.terminationReason).toBe('breach');
      }
    });

    it('should NOT terminate a draft contract', () => {
      const input: CreateLeaseContractInput = {
        propertyId: { value: 'PROP-20260106-001' },
        tenantId: { value: 'TEN-20260106-001' },
        startDate: new Date('2026-02-01'),
        endDate: new Date('2028-01-31'),
        monthlyRent: 150000,
        deposit: 300000,
      };

      const createResult = createLeaseContract(input);
      expect(createResult.isOk()).toBe(true);
      if (!createResult.isOk()) return;

      const contract = createResult.value; // Still in draft status
      
      const terminateResult = terminateContract(contract, 'natural-expiry');

      expect(terminateResult.isErr()).toBe(true);
      if (terminateResult.isErr()) {
        expect(terminateResult.error._tag).toBe('InvalidStatusTransitionError');
      }
    });
  });
});
