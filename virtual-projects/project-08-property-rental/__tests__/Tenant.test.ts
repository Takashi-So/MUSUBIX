/**
 * Tenant Entity Tests
 * TSK-027: Tenant Entity Unit Tests
 * 
 * @see REQ-RENTAL-001 F010-F013
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createTenant,
  updateTenant,
  assignGuarantor,
  resetTenantCounter,
} from '../src/entities/Tenant.js';
import type { CreateTenantInput, PersonName, ContactInfo, EmploymentInfo, EmergencyContact, Identification } from '../src/types/index.js';

describe('Tenant Entity', () => {
  let validInput: CreateTenantInput;

  beforeEach(() => {
    resetTenantCounter();

    const name: PersonName = {
      firstName: '太郎',
      lastName: '山田',
      firstNameKana: 'タロウ',
      lastNameKana: 'ヤマダ',
    };

    const contact: ContactInfo = {
      phone: '090-1234-5678',
      email: 'yamada@example.com',
      address: {
        postalCode: '150-0001',
        prefecture: '東京都',
        city: '渋谷区',
        street: '神宮前1-2-3',
      },
    };

    const identification: Identification = {
      type: '運転免許証',
      number: '123456789012',
      issuedDate: new Date('2020-01-01'),
      expiryDate: new Date('2030-01-01'),
    };

    const employment: EmploymentInfo = {
      companyName: '株式会社テスト',
      position: 'エンジニア',
      annualIncome: { amount: 5000000, currency: 'JPY' },
      employmentType: '正社員',
      yearsEmployed: 3,
    };

    const emergencyContact: EmergencyContact = {
      name: { firstName: '花子', lastName: '山田', firstNameKana: 'ハナコ', lastNameKana: 'ヤマダ' },
      relationship: '母',
      phone: '090-9999-8888',
    };

    validInput = { name, contact, identification, employment, emergencyContact };
  });

  describe('createTenant', () => {
    it('should create a tenant with valid inputs', () => {
      const tenant = createTenant(validInput);

      expect(tenant.id).toMatch(/^TEN-\d{8}-\d{3}$/);
      expect(tenant.name.lastName).toBe('山田');
      expect(tenant.status).toBe('prospective');
    });

    it('should throw error for missing company name', () => {
      const invalidInput = {
        ...validInput,
        employment: { ...validInput.employment, companyName: '' },
      };
      expect(() => createTenant(invalidInput)).toThrow('Company name is required');
    });
  });

  describe('updateTenant', () => {
    it('should update tenant contact', () => {
      const tenant = createTenant(validInput);
      const newContact: ContactInfo = {
        ...validInput.contact,
        phone: '080-1111-2222',
      };
      const updated = updateTenant(tenant, { contact: newContact });
      expect(updated.contact.phone).toBe('080-1111-2222');
    });
  });

  describe('assignGuarantor', () => {
    it('should assign guarantor to tenant', () => {
      const tenant = createTenant(validInput);
      const updated = assignGuarantor(tenant, 'GUA-20250101-001');
      expect(updated.guarantorId).toBe('GUA-20250101-001');
    });
  });
});
