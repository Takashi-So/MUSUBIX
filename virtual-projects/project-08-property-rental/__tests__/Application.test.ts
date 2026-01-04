/**
 * RentalApplication Entity Tests
 * TSK-031: RentalApplication Entity Unit Tests
 * 
 * @see REQ-RENTAL-001 F021
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createRentalApplication,
  approveApplication,
  rejectApplication,
  withdrawApplication,
  startScreening,
  resetApplicationCounter,
} from '../src/entities/RentalApplication.js';
import type { SubmitApplicationInput } from '../src/types/index.js';

describe('RentalApplication Entity', () => {
  let validInput: SubmitApplicationInput;

  beforeEach(() => {
    resetApplicationCounter();
    // 30日後の日付を設定
    const futureDate = new Date();
    futureDate.setDate(futureDate.getDate() + 30);
    
    validInput = {
      propertyId: 'PROP-20250101-001',
      tenantId: 'TEN-20250101-001',
      desiredMoveInDate: futureDate,
    };
  });

  describe('createRentalApplication', () => {
    it('should create an application with valid inputs', () => {
      const application = createRentalApplication(validInput);

      expect(application.id).toMatch(/^APP-\d{8}-\d{3}$/);
      expect(application.propertyId).toBe('PROP-20250101-001');
      expect(application.tenantId).toBe('TEN-20250101-001');
      expect(application.status).toBe('submitted');
    });

    it('should throw error for past move-in date', () => {
      const pastDate = new Date('2024-01-01');
      const invalidInput = { ...validInput, desiredMoveInDate: pastDate };
      expect(() => createRentalApplication(invalidInput)).toThrow('Desired move-in date must be in the future');
    });

    it('should throw error for undefined move-in date', () => {
      const invalidInput = { ...validInput, desiredMoveInDate: undefined as any };
      expect(() => createRentalApplication(invalidInput)).toThrow('Desired move-in date is required');
    });

    it('should generate sequential IDs', () => {
      const app1 = createRentalApplication(validInput);
      const app2 = createRentalApplication(validInput);

      expect(app1.id).toContain('-001');
      expect(app2.id).toContain('-002');
    });
  });

  describe('startScreening', () => {
    it('should start screening for submitted application', () => {
      const application = createRentalApplication(validInput);
      const screening = startScreening(application);

      expect(screening.status).toBe('screening');
    });
  });

  describe('approveApplication', () => {
    it('should approve application after screening', () => {
      const application = createRentalApplication(validInput);
      const screening = startScreening(application);
      const approved = approveApplication(screening);

      expect(approved.status).toBe('approved');
    });
  });

  describe('rejectApplication', () => {
    it('should reject application with reason', () => {
      const application = createRentalApplication(validInput);
      const screening = startScreening(application);
      const rejected = rejectApplication(screening, '収入証明が不十分');

      expect(rejected.status).toBe('rejected');
      expect(rejected.rejectionReason).toBe('収入証明が不十分');
    });
  });

  describe('withdrawApplication', () => {
    it('should allow withdrawal of submitted application', () => {
      const application = createRentalApplication(validInput);
      const withdrawn = withdrawApplication(application);

      expect(withdrawn.status).toBe('withdrawn');
    });
  });
});
