/**
 * Tenant Entity Tests
 * 
 * @requirement REQ-RENTAL-001-F010 (Tenant Registration)
 * @requirement REQ-RENTAL-001-F011 (Tenant Verification Status)
 * @design DES-RENTAL-001-C002
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  Tenant,
  createTenant,
  CreateTenantInput,
  canTransitionVerificationStatus,
  transitionVerificationStatus,
} from '../src/entities/Tenant.js';
import {
  resetTenantCounter,
  VerificationStatus,
} from '../src/types/common.js';

describe('Tenant Entity', () => {
  beforeEach(() => {
    resetTenantCounter();
  });

  describe('createTenant', () => {
    it('should create a tenant with valid input', () => {
      const input: CreateTenantInput = {
        fullName: '山田太郎',
        email: 'yamada@example.com',
        phone: '090-1234-5678',
        emergencyContact: {
          name: '山田花子',
          phone: '080-9876-5432',
        },
      };

      const result = createTenant(input);

      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        const tenant = result.value;
        expect(tenant.id.value).toMatch(/^TEN-\d{8}-001$/);
        expect(tenant.fullName).toBe('山田太郎');
        expect(tenant.email.value).toBe('yamada@example.com');
        expect(tenant.phone.value).toBe('090-1234-5678');
        expect(tenant.emergencyContact.name).toBe('山田花子');
        expect(tenant.verificationStatus).toBe('pending-verification');
        expect(tenant.version).toBe(1);
      }
    });

    it('should normalize email to lowercase', () => {
      const input: CreateTenantInput = {
        fullName: '山田太郎',
        email: 'YAMADA@EXAMPLE.COM',
        phone: '090-1234-5678',
        emergencyContact: {
          name: '山田花子',
          phone: '080-9876-5432',
        },
      };

      const result = createTenant(input);

      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.email.value).toBe('yamada@example.com');
      }
    });

    it('should reject invalid email format', () => {
      const input: CreateTenantInput = {
        fullName: '山田太郎',
        email: 'invalid-email', // Invalid
        phone: '090-1234-5678',
        emergencyContact: {
          name: '山田花子',
          phone: '080-9876-5432',
        },
      };

      const result = createTenant(input);

      expect(result.isErr()).toBe(true);
      if (result.isErr()) {
        expect(result.error.message).toContain('email');
      }
    });

    it('should reject invalid phone format', () => {
      const input: CreateTenantInput = {
        fullName: '山田太郎',
        email: 'yamada@example.com',
        phone: 'abc-defg', // Invalid
        emergencyContact: {
          name: '山田花子',
          phone: '080-9876-5432',
        },
      };

      const result = createTenant(input);

      expect(result.isErr()).toBe(true);
      if (result.isErr()) {
        expect(result.error.message).toContain('phone');
      }
    });

    it('should reject empty full name', () => {
      const input: CreateTenantInput = {
        fullName: '  ', // Empty after trim
        email: 'yamada@example.com',
        phone: '090-1234-5678',
        emergencyContact: {
          name: '山田花子',
          phone: '080-9876-5432',
        },
      };

      const result = createTenant(input);

      expect(result.isErr()).toBe(true);
      if (result.isErr()) {
        expect(result.error.message).toContain('name');
      }
    });

    it('should reject invalid emergency contact phone', () => {
      const input: CreateTenantInput = {
        fullName: '山田太郎',
        email: 'yamada@example.com',
        phone: '090-1234-5678',
        emergencyContact: {
          name: '山田花子',
          phone: 'invalid', // Invalid
        },
      };

      const result = createTenant(input);

      expect(result.isErr()).toBe(true);
    });
  });

  describe('Verification Status Transitions', () => {
    // REQ-RENTAL-001-F011: Valid transitions
    
    it('should allow pending-verification → verified transition', () => {
      expect(canTransitionVerificationStatus('pending-verification', 'verified')).toBe(true);
    });

    it('should allow pending-verification → rejected transition', () => {
      expect(canTransitionVerificationStatus('pending-verification', 'rejected')).toBe(true);
    });

    // Invalid transitions
    it('should NOT allow verified → any transition', () => {
      expect(canTransitionVerificationStatus('verified', 'pending-verification')).toBe(false);
      expect(canTransitionVerificationStatus('verified', 'rejected')).toBe(false);
    });

    it('should NOT allow rejected → any transition', () => {
      expect(canTransitionVerificationStatus('rejected', 'pending-verification')).toBe(false);
      expect(canTransitionVerificationStatus('rejected', 'verified')).toBe(false);
    });
  });

  describe('transitionVerificationStatus', () => {
    it('should verify tenant successfully', () => {
      const input: CreateTenantInput = {
        fullName: '山田太郎',
        email: 'yamada@example.com',
        phone: '090-1234-5678',
        emergencyContact: {
          name: '山田花子',
          phone: '080-9876-5432',
        },
      };

      const createResult = createTenant(input);
      expect(createResult.isOk()).toBe(true);
      if (!createResult.isOk()) return;

      const tenant = createResult.value;
      const transitionResult = transitionVerificationStatus(tenant, 'verified');

      expect(transitionResult.isOk()).toBe(true);
      if (transitionResult.isOk()) {
        expect(transitionResult.value.verificationStatus).toBe('verified');
        expect(transitionResult.value.version).toBe(2);
      }
    });

    it('should reject tenant successfully', () => {
      const input: CreateTenantInput = {
        fullName: '山田太郎',
        email: 'yamada@example.com',
        phone: '090-1234-5678',
        emergencyContact: {
          name: '山田花子',
          phone: '080-9876-5432',
        },
      };

      const createResult = createTenant(input);
      expect(createResult.isOk()).toBe(true);
      if (!createResult.isOk()) return;

      const tenant = createResult.value;
      const transitionResult = transitionVerificationStatus(tenant, 'rejected');

      expect(transitionResult.isOk()).toBe(true);
      if (transitionResult.isOk()) {
        expect(transitionResult.value.verificationStatus).toBe('rejected');
      }
    });

    it('should not allow transition from verified status', () => {
      const input: CreateTenantInput = {
        fullName: '山田太郎',
        email: 'yamada@example.com',
        phone: '090-1234-5678',
        emergencyContact: {
          name: '山田花子',
          phone: '080-9876-5432',
        },
      };

      const createResult = createTenant(input);
      expect(createResult.isOk()).toBe(true);
      if (!createResult.isOk()) return;

      const tenant = createResult.value;
      const verifyResult = transitionVerificationStatus(tenant, 'verified');
      expect(verifyResult.isOk()).toBe(true);
      if (!verifyResult.isOk()) return;

      const verifiedTenant = verifyResult.value;
      const rejectResult = transitionVerificationStatus(verifiedTenant, 'rejected');

      expect(rejectResult.isErr()).toBe(true);
      if (rejectResult.isErr()) {
        expect(rejectResult.error._tag).toBe('InvalidStatusTransitionError');
      }
    });
  });
});
