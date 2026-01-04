/**
 * Payment Service
 * TSK-023: PaymentService
 * 
 * @see REQ-RENTAL-001 F040-F043
 * @see DES-RENTAL-001 §5.4
 */

import type {
  Payment,
  PaymentId,
  LeaseContractId,
  TenantId,
  PaymentMethod,
  Money,
} from '../types/index.js';
import {
  recordPaymentReceived,
  calculateLateFee,
  markAsOverdue,
  getDaysOverdue,
} from '../entities/Payment.js';
import type { IPaymentRepository } from '../repositories/PaymentRepository.js';
import type { IContractRepository } from '../repositories/ContractRepository.js';

/**
 * Payment Service
 */
export class PaymentService {
  constructor(
    private paymentRepository: IPaymentRepository,
    private contractRepository: IContractRepository
  ) {}

  /**
   * 支払いを記録
   * @see REQ-RENTAL-001 F041
   */
  async recordPayment(
    paymentId: PaymentId,
    paidDate: Date,
    paymentMethod: PaymentMethod,
    receiptNumber?: string
  ): Promise<Payment> {
    const payment = await this.paymentRepository.findById(paymentId);
    if (!payment) {
      throw new Error(`Payment with ID ${paymentId} not found`);
    }

    const recorded = recordPaymentReceived(payment, paidDate, paymentMethod, receiptNumber);
    return this.paymentRepository.update(recorded);
  }

  /**
   * 支払い情報を取得
   */
  async getPayment(id: PaymentId): Promise<Payment | null> {
    return this.paymentRepository.findById(id);
  }

  /**
   * 契約の支払い一覧を取得
   */
  async getPaymentsByContract(contractId: LeaseContractId): Promise<Payment[]> {
    return this.paymentRepository.findByContractId(contractId);
  }

  /**
   * 入居者の支払い一覧を取得
   */
  async getPaymentsByTenant(tenantId: TenantId): Promise<Payment[]> {
    return this.paymentRepository.findByTenantId(tenantId);
  }

  /**
   * 遅延損害金を計算
   * @see REQ-RENTAL-001 F042
   */
  calculateLateFee(payment: Payment, asOfDate?: Date): Money {
    return calculateLateFee(payment, asOfDate);
  }

  /**
   * 延滞支払いを取得
   * @see REQ-RENTAL-001 F042
   */
  async getOverduePayments(): Promise<Payment[]> {
    return this.paymentRepository.findOverdue();
  }

  /**
   * 延滞支払いを延滞ステータスに更新
   */
  async processOverduePayments(): Promise<Payment[]> {
    const overduePayments = await this.paymentRepository.findOverdue();
    const updated: Payment[] = [];

    for (const payment of overduePayments) {
      if (payment.status === 'pending') {
        const marked = markAsOverdue(payment);
        await this.paymentRepository.update(marked);
        updated.push(marked);
      }
    }

    return updated;
  }

  /**
   * 支払い予定を取得（指定期間内）
   */
  async getUpcomingPayments(
    contractId: LeaseContractId,
    days: number = 30
  ): Promise<Payment[]> {
    const payments = await this.paymentRepository.findByContractId(contractId);
    const now = new Date();
    const cutoff = new Date(now.getTime() + days * 24 * 60 * 60 * 1000);

    return payments.filter(
      p => p.status === 'pending' && p.dueDate >= now && p.dueDate <= cutoff
    );
  }

  /**
   * 支払い状況サマリーを取得
   * @see REQ-RENTAL-001 F043
   */
  async getPaymentSummary(contractId: LeaseContractId): Promise<{
    totalDue: Money;
    totalPaid: Money;
    totalOverdue: Money;
    pendingCount: number;
    paidCount: number;
    overdueCount: number;
  }> {
    const payments = await this.paymentRepository.findByContractId(contractId);

    let totalDue = 0;
    let totalPaid = 0;
    let totalOverdue = 0;
    let pendingCount = 0;
    let paidCount = 0;
    let overdueCount = 0;

    for (const payment of payments) {
      totalDue += payment.amount.amount;
      
      if (payment.status === 'paid') {
        totalPaid += payment.amount.amount;
        paidCount++;
      } else if (payment.status === 'overdue') {
        totalOverdue += payment.amount.amount + (payment.lateFee?.amount || 0);
        overdueCount++;
      } else if (payment.status === 'pending') {
        pendingCount++;
      }
    }

    return {
      totalDue: { amount: totalDue, currency: 'JPY' },
      totalPaid: { amount: totalPaid, currency: 'JPY' },
      totalOverdue: { amount: totalOverdue, currency: 'JPY' },
      pendingCount,
      paidCount,
      overdueCount,
    };
  }

  /**
   * 延滞日数を取得
   */
  getDaysOverdue(payment: Payment, asOfDate?: Date): number {
    return getDaysOverdue(payment, asOfDate);
  }

  /**
   * 支払いリマインダー対象を取得
   * @see REQ-RENTAL-001 F043
   */
  async getPaymentsNeedingReminder(daysBeforeDue: number = 7): Promise<Payment[]> {
    const allPayments = await this.paymentRepository.findByStatus('pending');
    const now = new Date();
    const reminderDate = new Date(now.getTime() + daysBeforeDue * 24 * 60 * 60 * 1000);

    return allPayments.filter(
      p => p.dueDate >= now && p.dueDate <= reminderDate
    );
  }

  /**
   * 入居者の延滞情報を取得
   */
  async getTenantOverdueInfo(tenantId: TenantId): Promise<{
    hasOverdue: boolean;
    overduePayments: Payment[];
    totalOverdueAmount: Money;
    maxDaysOverdue: number;
  }> {
    const payments = await this.paymentRepository.findByTenantId(tenantId);
    const overduePayments = payments.filter(p => p.status === 'overdue');

    let totalOverdueAmount = 0;
    let maxDaysOverdue = 0;

    for (const payment of overduePayments) {
      totalOverdueAmount += payment.amount.amount + (payment.lateFee?.amount || 0);
      const days = getDaysOverdue(payment);
      if (days > maxDaysOverdue) {
        maxDaysOverdue = days;
      }
    }

    return {
      hasOverdue: overduePayments.length > 0,
      overduePayments,
      totalOverdueAmount: { amount: totalOverdueAmount, currency: 'JPY' },
      maxDaysOverdue,
    };
  }
}
