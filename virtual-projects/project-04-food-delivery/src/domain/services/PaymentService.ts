/**
 * Payment Domain Service
 * @design DES-DELIVERY-001 §5.3
 * @task TSK-DLV-009
 */

import { Order } from '../order';
import { Money } from '../shared';

// ============================================================
// Payment ID
// ============================================================
export class PaymentId {
  constructor(public readonly value: string) {}

  static generate(): PaymentId {
    return new PaymentId(`pay-${crypto.randomUUID()}`);
  }

  equals(other: PaymentId): boolean {
    return this.value === other.value;
  }
}

// ============================================================
// Payment Status & Method
// ============================================================
export enum PaymentStatus {
  PENDING = 'PENDING',
  COMPLETED = 'COMPLETED',
  FAILED = 'FAILED',
  REFUNDED = 'REFUNDED',
}

export type PaymentMethod = 'CREDIT_CARD' | 'DEBIT_CARD' | 'CASH';

// ============================================================
// Payment Entity
// ============================================================
export class Payment {
  private _status: PaymentStatus = PaymentStatus.PENDING;
  private _transactionId?: string;
  private _processedAt?: Date;
  private _refundedAt?: Date;

  private constructor(
    public readonly id: PaymentId,
    public readonly orderId: string,
    public readonly amount: Money,
    public readonly method: PaymentMethod
  ) {}

  static create(orderId: string, amount: Money, method: PaymentMethod): Payment {
    return new Payment(PaymentId.generate(), orderId, amount, method);
  }

  get status(): PaymentStatus {
    return this._status;
  }
  get transactionId(): string | undefined {
    return this._transactionId;
  }
  get processedAt(): Date | undefined {
    return this._processedAt;
  }

  complete(transactionId?: string): void {
    this._status = PaymentStatus.COMPLETED;
    this._transactionId = transactionId || `TXN-${Date.now()}`;
    this._processedAt = new Date();
  }

  fail(): void {
    this._status = PaymentStatus.FAILED;
    this._processedAt = new Date();
  }

  refund(): void {
    if (this._status !== PaymentStatus.COMPLETED) {
      throw new Error('Can only refund completed payments');
    }
    this._status = PaymentStatus.REFUNDED;
    this._refundedAt = new Date();
  }
}

// ============================================================
// Payment Service
// ============================================================
export interface ProcessPaymentResult {
  success: boolean;
  payment?: Payment;
  error?: string;
}

export interface RefundResult {
  success: boolean;
  error?: string;
}

export class PaymentService {
  processPayment(order: Order, method: PaymentMethod): ProcessPaymentResult {
    try {
      const payment = Payment.create(order.id.value, order.total, method);

      // Simulate payment processing
      if (method === 'CASH') {
        // Cash payments are pending until delivery
        return { success: true, payment };
      }

      // Card payments are processed immediately (simulated)
      payment.complete();
      return { success: true, payment };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Payment processing failed',
      };
    }
  }

  refundPayment(payment: Payment, reason: string): RefundResult {
    try {
      payment.refund();
      // In real implementation, call payment gateway
      console.log(`Refund initiated for payment ${payment.id.value}: ${reason}`);
      return { success: true };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Refund failed',
      };
    }
  }
}
