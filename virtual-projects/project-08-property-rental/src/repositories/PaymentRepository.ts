/**
 * Payment Repository
 * TSK-017: PaymentRepository
 * 
 * @see DES-RENTAL-001 §5.4
 */

import type {
  Payment,
  PaymentId,
  LeaseContractId,
  TenantId,
  PaymentStatus,
  PaymentType,
} from '../types/index.js';
import { isPaymentOverdue } from '../entities/Payment.js';

/**
 * Payment Repository Interface
 */
export interface IPaymentRepository {
  create(payment: Payment): Promise<Payment>;
  createMany(payments: Payment[]): Promise<Payment[]>;
  findById(id: PaymentId): Promise<Payment | null>;
  findByContractId(contractId: LeaseContractId): Promise<Payment[]>;
  findByTenantId(tenantId: TenantId): Promise<Payment[]>;
  findByStatus(status: PaymentStatus): Promise<Payment[]>;
  findOverdue(): Promise<Payment[]>;
  update(payment: Payment): Promise<Payment>;
  delete(id: PaymentId): Promise<boolean>;
  findAll(): Promise<Payment[]>;
}

/**
 * In-Memory Payment Repository Implementation
 */
export class InMemoryPaymentRepository implements IPaymentRepository {
  private payments: Map<PaymentId, Payment> = new Map();

  async create(payment: Payment): Promise<Payment> {
    if (this.payments.has(payment.id)) {
      throw new Error(`Payment with ID ${payment.id} already exists`);
    }
    
    this.payments.set(payment.id, { ...payment });
    return { ...payment };
  }

  async createMany(payments: Payment[]): Promise<Payment[]> {
    const created: Payment[] = [];
    for (const payment of payments) {
      const result = await this.create(payment);
      created.push(result);
    }
    return created;
  }

  async findById(id: PaymentId): Promise<Payment | null> {
    const payment = this.payments.get(id);
    return payment ? { ...payment } : null;
  }

  async findByContractId(contractId: LeaseContractId): Promise<Payment[]> {
    const results: Payment[] = [];
    for (const payment of this.payments.values()) {
      if (payment.contractId === contractId) {
        results.push({ ...payment });
      }
    }
    // Sort by due date
    return results.sort((a, b) => a.dueDate.getTime() - b.dueDate.getTime());
  }

  async findByTenantId(tenantId: TenantId): Promise<Payment[]> {
    const results: Payment[] = [];
    for (const payment of this.payments.values()) {
      if (payment.tenantId === tenantId) {
        results.push({ ...payment });
      }
    }
    // Sort by due date
    return results.sort((a, b) => a.dueDate.getTime() - b.dueDate.getTime());
  }

  async findByStatus(status: PaymentStatus): Promise<Payment[]> {
    const results: Payment[] = [];
    for (const payment of this.payments.values()) {
      if (payment.status === status) {
        results.push({ ...payment });
      }
    }
    return results;
  }

  async findOverdue(): Promise<Payment[]> {
    const results: Payment[] = [];
    for (const payment of this.payments.values()) {
      if (isPaymentOverdue(payment)) {
        results.push({ ...payment });
      }
    }
    // Sort by due date (oldest first)
    return results.sort((a, b) => a.dueDate.getTime() - b.dueDate.getTime());
  }

  async update(payment: Payment): Promise<Payment> {
    if (!this.payments.has(payment.id)) {
      throw new Error(`Payment with ID ${payment.id} not found`);
    }
    
    this.payments.set(payment.id, { ...payment });
    return { ...payment };
  }

  async delete(id: PaymentId): Promise<boolean> {
    return this.payments.delete(id);
  }

  async findAll(): Promise<Payment[]> {
    return Array.from(this.payments.values()).map(p => ({ ...p }));
  }

  /**
   * Find payments by type
   */
  async findByType(type: PaymentType): Promise<Payment[]> {
    const results: Payment[] = [];
    for (const payment of this.payments.values()) {
      if (payment.paymentType === type) {
        results.push({ ...payment });
      }
    }
    return results;
  }

  /**
   * Find payments within date range
   */
  async findByDateRange(from: Date, to: Date): Promise<Payment[]> {
    const results: Payment[] = [];
    for (const payment of this.payments.values()) {
      if (payment.dueDate >= from && payment.dueDate <= to) {
        results.push({ ...payment });
      }
    }
    return results.sort((a, b) => a.dueDate.getTime() - b.dueDate.getTime());
  }

  /**
   * Clear all data (for testing)
   */
  clear(): void {
    this.payments.clear();
  }
}
