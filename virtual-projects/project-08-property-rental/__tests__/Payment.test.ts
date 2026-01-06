/**
 * Payment Entity Tests
 * 
 * @requirement REQ-RENTAL-001-F030 (Payment Recording)
 * @requirement REQ-RENTAL-001-F031 (Overdue Payment Detection)
 * @design DES-RENTAL-001-C004
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  Payment,
  createPayment,
  CreatePaymentInput,
  isPaymentOverdue,
  PAYMENT_GRACE_PERIOD_DAYS,
} from '../src/entities/Payment.js';
import {
  resetPaymentCounter,
} from '../src/types/common.js';

describe('Payment Entity', () => {
  beforeEach(() => {
    resetPaymentCounter();
  });

  describe('createPayment', () => {
    it('should create a payment with valid input', () => {
      const input: CreatePaymentInput = {
        contractId: { value: 'LEASE-20260106-001' },
        amount: 150000,
        paymentDate: new Date('2026-01-25'),
        paymentMethod: 'bank-transfer',
        paymentPeriod: '2026-01',
        dueDate: new Date('2026-01-31'),
      };

      const result = createPayment(input);

      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        const payment = result.value;
        expect(payment.id.value).toMatch(/^PAY-\d{8}-001$/);
        expect(payment.contractId.value).toBe('LEASE-20260106-001');
        expect(payment.amount.amount).toBe(150000);
        expect(payment.paymentMethod).toBe('bank-transfer');
        expect(payment.paymentPeriod).toBe('2026-01');
        expect(payment.status).toBe('paid');
      }
    });

    it('should create payment with credit-card method', () => {
      const input: CreatePaymentInput = {
        contractId: { value: 'LEASE-20260106-001' },
        amount: 150000,
        paymentDate: new Date('2026-01-25'),
        paymentMethod: 'credit-card',
        paymentPeriod: '2026-01',
        dueDate: new Date('2026-01-31'),
      };

      const result = createPayment(input);

      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.paymentMethod).toBe('credit-card');
      }
    });

    it('should create payment with cash method', () => {
      const input: CreatePaymentInput = {
        contractId: { value: 'LEASE-20260106-001' },
        amount: 150000,
        paymentDate: new Date('2026-01-25'),
        paymentMethod: 'cash',
        paymentPeriod: '2026-01',
        dueDate: new Date('2026-01-31'),
      };

      const result = createPayment(input);

      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.paymentMethod).toBe('cash');
      }
    });

    it('should create payment with auto-debit method', () => {
      const input: CreatePaymentInput = {
        contractId: { value: 'LEASE-20260106-001' },
        amount: 150000,
        paymentDate: new Date('2026-01-25'),
        paymentMethod: 'auto-debit',
        paymentPeriod: '2026-01',
        dueDate: new Date('2026-01-31'),
      };

      const result = createPayment(input);

      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.paymentMethod).toBe('auto-debit');
      }
    });

    it('should reject negative amount', () => {
      const input: CreatePaymentInput = {
        contractId: { value: 'LEASE-20260106-001' },
        amount: -5000, // Invalid
        paymentDate: new Date('2026-01-25'),
        paymentMethod: 'bank-transfer',
        paymentPeriod: '2026-01',
        dueDate: new Date('2026-01-31'),
      };

      const result = createPayment(input);

      expect(result.isErr()).toBe(true);
    });

    it('should reject zero amount', () => {
      const input: CreatePaymentInput = {
        contractId: { value: 'LEASE-20260106-001' },
        amount: 0, // Invalid
        paymentDate: new Date('2026-01-25'),
        paymentMethod: 'bank-transfer',
        paymentPeriod: '2026-01',
        dueDate: new Date('2026-01-31'),
      };

      const result = createPayment(input);

      expect(result.isErr()).toBe(true);
      if (result.isErr()) {
        expect(result.error.message).toContain('positive');
      }
    });

    it('should reject invalid payment period format', () => {
      const input: CreatePaymentInput = {
        contractId: { value: 'LEASE-20260106-001' },
        amount: 150000,
        paymentDate: new Date('2026-01-25'),
        paymentMethod: 'bank-transfer',
        paymentPeriod: '2026/01', // Invalid format
        dueDate: new Date('2026-01-31'),
      };

      const result = createPayment(input);

      expect(result.isErr()).toBe(true);
      if (result.isErr()) {
        expect(result.error.message).toContain('YYYY-MM');
      }
    });
  });

  describe('Overdue Payment Detection (REQ-RENTAL-001-F031)', () => {
    it('should have grace period of 5 days', () => {
      expect(PAYMENT_GRACE_PERIOD_DAYS).toBe(5);
    });

    it('should not be overdue when paid on time', () => {
      const dueDate = new Date('2026-01-31');
      const checkDate = new Date('2026-01-31');

      expect(isPaymentOverdue(dueDate, checkDate)).toBe(false);
    });

    it('should not be overdue during grace period', () => {
      const dueDate = new Date('2026-01-31');
      const checkDate = new Date('2026-02-05'); // 5 days after due date

      expect(isPaymentOverdue(dueDate, checkDate)).toBe(false);
    });

    it('should be overdue after grace period', () => {
      const dueDate = new Date('2026-01-31');
      const checkDate = new Date('2026-02-06'); // 6 days after due date

      expect(isPaymentOverdue(dueDate, checkDate)).toBe(true);
    });

    it('should not be overdue before due date', () => {
      const dueDate = new Date('2026-01-31');
      const checkDate = new Date('2026-01-15');

      expect(isPaymentOverdue(dueDate, checkDate)).toBe(false);
    });
  });
});
