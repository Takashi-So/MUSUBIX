/**
 * Payment Entity
 * 
 * @requirement REQ-RENTAL-001-F030 (Payment Recording)
 * @requirement REQ-RENTAL-001-F031 (Overdue Payment Detection)
 * @requirement REQ-RENTAL-001-F032 (Payment History Query)
 * @design DES-RENTAL-001-C004
 */

import { Result, ok, err } from 'neverthrow';
import {
  PaymentId,
  LeaseContractId,
  PaymentStatus,
  PaymentMethod,
  Money,
  generatePaymentId,
  createMoney,
  ValidationError,
} from '../types/common.js';

// ============================================================
// Constants
// ============================================================

export const PAYMENT_GRACE_PERIOD_DAYS = 5;

// ============================================================
// Payment Entity
// ============================================================

export interface Payment {
  readonly id: PaymentId;
  readonly contractId: LeaseContractId;
  readonly amount: Money;
  readonly paymentDate: Date;
  readonly paymentMethod: PaymentMethod;
  readonly paymentPeriod: string;  // YYYY-MM format
  readonly status: PaymentStatus;
  readonly dueDate: Date;
  readonly createdAt: Date;
  readonly updatedAt: Date;
}

// ============================================================
// Input DTO (BP-CODE-001)
// ============================================================

export interface CreatePaymentInput {
  contractId: LeaseContractId;
  amount: number;
  paymentDate: Date;
  paymentMethod: PaymentMethod;
  paymentPeriod: string;  // YYYY-MM format
  dueDate: Date;
}

// ============================================================
// Factory Function
// ============================================================

const PAYMENT_PERIOD_REGEX = /^\d{4}-\d{2}$/;

export function createPayment(
  input: CreatePaymentInput,
  date: Date = new Date()
): Result<Payment, ValidationError> {
  // Validate amount
  if (input.amount <= 0) {
    return err(new ValidationError('Payment amount must be positive'));
  }

  const amountResult = createMoney(input.amount);
  if (amountResult.isErr()) {
    return err(amountResult.error);
  }

  // Validate payment period format
  if (!PAYMENT_PERIOD_REGEX.test(input.paymentPeriod)) {
    return err(new ValidationError('Payment period must be in YYYY-MM format'));
  }

  const now = new Date();
  const payment: Payment = {
    id: generatePaymentId(date),
    contractId: input.contractId,
    amount: amountResult.value,
    paymentDate: input.paymentDate,
    paymentMethod: input.paymentMethod,
    paymentPeriod: input.paymentPeriod,
    status: 'paid',
    dueDate: input.dueDate,
    createdAt: now,
    updatedAt: now,
  };

  return ok(payment);
}

// ============================================================
// Overdue Detection (REQ-RENTAL-001-F031)
// ============================================================

export function isPaymentOverdue(dueDate: Date, checkDate: Date = new Date()): boolean {
  const dueDateMs = dueDate.getTime();
  const checkDateMs = checkDate.getTime();
  
  // Grace period: 5 days after due date
  const gracePeriodMs = PAYMENT_GRACE_PERIOD_DAYS * 24 * 60 * 60 * 1000;
  const overdueThreshold = dueDateMs + gracePeriodMs;

  return checkDateMs > overdueThreshold;
}

// ============================================================
// Pending Payment (for tracking expected payments)
// ============================================================

export interface PendingPayment {
  readonly contractId: LeaseContractId;
  readonly expectedAmount: Money;
  readonly paymentPeriod: string;
  readonly dueDate: Date;
  readonly status: 'pending' | 'overdue';
}

export function createPendingPayment(
  contractId: LeaseContractId,
  expectedAmount: number,
  paymentPeriod: string,
  dueDate: Date
): Result<PendingPayment, ValidationError> {
  const amountResult = createMoney(expectedAmount);
  if (amountResult.isErr()) {
    return err(amountResult.error);
  }

  if (!PAYMENT_PERIOD_REGEX.test(paymentPeriod)) {
    return err(new ValidationError('Payment period must be in YYYY-MM format'));
  }

  const status = isPaymentOverdue(dueDate) ? 'overdue' : 'pending';

  return ok({
    contractId,
    expectedAmount: amountResult.value,
    paymentPeriod,
    dueDate,
    status,
  });
}

// ============================================================
// Payment History (REQ-RENTAL-001-F032)
// ============================================================

export interface PaymentHistoryEntry {
  payment: Payment;
  runningBalance: number;
}

export interface PaymentHistory {
  contractId: LeaseContractId;
  entries: PaymentHistoryEntry[];
  totalPaid: number;
  totalDue: number;
  balance: number;
}

export function calculatePaymentHistory(
  contractId: LeaseContractId,
  payments: Payment[],
  totalExpectedAmount: number
): PaymentHistory {
  // Sort payments by date
  const sortedPayments = [...payments].sort(
    (a, b) => a.paymentDate.getTime() - b.paymentDate.getTime()
  );

  let runningBalance = 0;
  const entries: PaymentHistoryEntry[] = sortedPayments.map(payment => {
    runningBalance += payment.amount.amount;
    return {
      payment,
      runningBalance,
    };
  });

  const totalPaid = runningBalance;
  const balance = totalExpectedAmount - totalPaid;

  return {
    contractId,
    entries,
    totalPaid,
    totalDue: totalExpectedAmount,
    balance,
  };
}
