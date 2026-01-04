/**
 * Payment Types
 * @requirement REQ-PAY-001, REQ-PAY-002, REQ-PAY-003
 * @design DES-PARKING-001 Section 4
 */

export type PaymentMethod = 'cash' | 'credit' | 'prepaid';
export type PaymentStatus = 'pending' | 'completed' | 'failed' | 'refunded';

export interface Payment {
  id: string;
  entryId: string;
  amount: number;
  method: PaymentMethod;
  status: PaymentStatus;
  transactionId?: string;
  createdAt: Date;
  completedAt?: Date;
}

export interface Receipt {
  paymentId: string;
  entryId: string;
  plateNumber: string;
  entryTime: Date;
  exitTime: Date;
  durationMinutes: number;
  baseFee: number;
  discountAmount: number;
  totalAmount: number;
  paymentMethod: PaymentMethod;
  issuedAt: Date;
}

export const PAYMENT_ERRORS = {
  INSUFFICIENT_FUNDS: 'insufficient_funds',
  PAYMENT_DECLINED: 'payment_declined',
  INVALID_METHOD: 'invalid_method',
  ENTRY_NOT_FOUND: 'entry_not_found',
} as const;
