/**
 * Payment Entity Tests
 * TSK-029: Payment Entity Unit Tests
 * 
 * @see REQ-RENTAL-001 F040-F043
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createPayment,
  recordPaymentReceived,
  calculateLateFee,
  markAsOverdue,
  resetPaymentCounter,
} from '../src/entities/Payment.js';
import type { RecordPaymentInput } from '../src/types/index.js';

describe('Payment Entity', () => {
  let validInput: RecordPaymentInput;

  beforeEach(() => {
    resetPaymentCounter();
    validInput = {
      contractId: 'LEASE-20250101-001',
      tenantId: 'TEN-20250101-001',
      amount: 100000,
      paymentType: 'rent',
      paymentMethod: 'bank_transfer',
      dueDate: new Date('2025-04-27'),
    };
  });

  describe('createPayment', () => {
    it('should create a payment with valid inputs', () => {
      const payment = createPayment(validInput);

      expect(payment.id).toMatch(/^PAY-\d{8}-\d{3}$/);
      expect(payment.contractId).toBe('LEASE-20250101-001');
      expect(payment.amount.amount).toBe(100000);
      expect(payment.status).toBe('pending');
    });

    it('should throw error for zero amount', () => {
      const invalidInput = { ...validInput, amount: 0 };
      expect(() => createPayment(invalidInput)).toThrow('Payment amount must be greater than 0');
    });

    it('should throw error for negative amount', () => {
      const invalidInput = { ...validInput, amount: -10000 };
      expect(() => createPayment(invalidInput)).toThrow('Payment amount must be greater than 0');
    });

    it('should create paid payment when paidDate provided', () => {
      const inputWithPaid = { ...validInput, paidDate: new Date('2025-04-25') };
      const payment = createPayment(inputWithPaid);
      expect(payment.status).toBe('paid');
      expect(payment.paidDate).toBeDefined();
    });
  });

  describe('recordPaymentReceived', () => {
    it('should record payment as paid', () => {
      const payment = createPayment(validInput);
      const recorded = recordPaymentReceived(payment, new Date('2025-04-25'));

      expect(recorded.status).toBe('paid');
      // receiptNumberは自動生成されるフォーマット
      expect(recorded.receiptNumber).toMatch(/^RCP-\d{8}-\d{4}$/);
    });
  });

  describe('calculateLateFee', () => {
    it('should return zero for payment before due date', () => {
      const payment = createPayment(validInput);
      const checkDate = new Date('2025-04-20');
      const lateFee = calculateLateFee(payment, checkDate);
      expect(lateFee.amount).toBe(0);
    });

    it('should calculate late fee for overdue payment', () => {
      const payment = createPayment(validInput);
      // 10日延滞
      const checkDate = new Date('2025-05-07');
      const lateFee = calculateLateFee(payment, checkDate);
      expect(lateFee.amount).toBeGreaterThan(0);
    });
  });

  describe('markAsOverdue', () => {
    it('should mark pending payment as overdue', () => {
      const payment = createPayment(validInput);
      const overdue = markAsOverdue(payment);
      expect(overdue.status).toBe('overdue');
    });
  });
});
