/**
 * Payment Entity
 * TSK-009: Payment Entity
 * 
 * @see REQ-RENTAL-001 F040-F043
 * @see DES-RENTAL-001 §4.1.5
 */

import type {
  Payment,
  PaymentId,
  LeaseContractId,
  TenantId,
  Money,
  PaymentType,
  PaymentMethod,
  PaymentStatus,
  RecordPaymentInput,
} from '../types/index.js';
import { createMoney } from './Property.js';

/**
 * ID生成カウンター（インメモリ用）
 */
let paymentCounter = 0;

/**
 * Payment ID生成
 * Format: PAY-YYYYMMDD-NNN
 */
export function generatePaymentId(): PaymentId {
  const now = new Date();
  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, '');
  paymentCounter++;
  const seq = String(paymentCounter).padStart(3, '0');
  return `PAY-${dateStr}-${seq}` as PaymentId;
}

/**
 * ID生成カウンターをリセット（テスト用）
 */
export function resetPaymentCounter(): void {
  paymentCounter = 0;
}

/**
 * 遅延損害金率（年率14.6%、日割り計算）
 */
const LATE_FEE_ANNUAL_RATE = 0.146;

/**
 * Paymentエンティティを作成
 * @see REQ-RENTAL-001 F040
 */
export function createPayment(input: RecordPaymentInput): Payment {
  if (input.amount <= 0) {
    throw new Error('Payment amount must be greater than 0');
  }
  
  const now = new Date();
  
  return {
    id: generatePaymentId(),
    contractId: input.contractId,
    tenantId: input.tenantId,
    amount: createMoney(input.amount),
    paymentType: input.paymentType,
    paymentMethod: input.paymentMethod,
    dueDate: new Date(input.dueDate),
    paidDate: input.paidDate ? new Date(input.paidDate) : undefined,
    status: input.paidDate ? 'paid' : 'pending',
    lateFee: undefined,
    receiptNumber: undefined,
    createdAt: now,
    updatedAt: now,
  };
}

/**
 * 有効なステータス遷移マップ
 */
const validPaymentStatusTransitions: Record<PaymentStatus, PaymentStatus[]> = {
  pending: ['paid', 'overdue', 'cancelled'],
  overdue: ['paid', 'cancelled'],
  paid: [],       // 支払済みは変更不可
  cancelled: [],  // キャンセル済みは変更不可
};

/**
 * Paymentステータスを更新
 */
export function updatePaymentStatus(
  payment: Payment,
  newStatus: PaymentStatus
): Payment {
  const allowedTransitions = validPaymentStatusTransitions[payment.status];
  
  if (!allowedTransitions.includes(newStatus)) {
    throw new Error(
      `Invalid status transition: ${payment.status} -> ${newStatus}. ` +
      `Allowed: ${allowedTransitions.join(', ') || 'none'}`
    );
  }
  
  return {
    ...payment,
    status: newStatus,
    updatedAt: new Date(),
  };
}

/**
 * 支払いを記録
 * @see REQ-RENTAL-001 F041
 */
export function recordPaymentReceived(
  payment: Payment,
  paidDate: Date,
  paymentMethod: PaymentMethod,
  receiptNumber?: string
): Payment {
  if (payment.status === 'paid') {
    throw new Error('Payment has already been recorded');
  }
  if (payment.status === 'cancelled') {
    throw new Error('Cannot record payment for cancelled item');
  }
  
  return {
    ...payment,
    paidDate,
    paymentMethod,
    status: 'paid',
    receiptNumber: receiptNumber || generateReceiptNumber(),
    updatedAt: new Date(),
  };
}

/**
 * 領収書番号を生成
 */
function generateReceiptNumber(): string {
  const now = new Date();
  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, '');
  const random = Math.floor(Math.random() * 10000).toString().padStart(4, '0');
  return `RCP-${dateStr}-${random}`;
}

/**
 * 遅延損害金を計算
 * @see REQ-RENTAL-001 F042
 */
export function calculateLateFee(payment: Payment, asOfDate?: Date): Money {
  const checkDate = asOfDate || new Date();
  
  // 支払済み or キャンセル済みの場合は遅延金なし
  if (payment.status === 'paid' || payment.status === 'cancelled') {
    return createMoney(0);
  }
  
  // 期日前の場合は遅延金なし
  if (checkDate <= payment.dueDate) {
    return createMoney(0);
  }
  
  // 遅延日数を計算
  const daysLate = Math.floor(
    (checkDate.getTime() - payment.dueDate.getTime()) / (24 * 60 * 60 * 1000)
  );
  
  // 遅延損害金 = 元本 × 年率 × 日数 / 365
  const lateFeeAmount = Math.floor(
    payment.amount.amount * LATE_FEE_ANNUAL_RATE * daysLate / 365
  );
  
  return createMoney(lateFeeAmount);
}

/**
 * 支払いを延滞としてマーク
 * @see REQ-RENTAL-001 F042
 */
export function markAsOverdue(payment: Payment): Payment {
  if (payment.status !== 'pending') {
    throw new Error('Only pending payments can be marked as overdue');
  }
  
  const now = new Date();
  if (now <= payment.dueDate) {
    throw new Error('Payment is not yet overdue');
  }
  
  const lateFee = calculateLateFee(payment, now);
  
  return {
    ...payment,
    status: 'overdue',
    lateFee,
    updatedAt: now,
  };
}

/**
 * 支払いをキャンセル
 */
export function cancelPayment(payment: Payment): Payment {
  if (payment.status === 'paid') {
    throw new Error('Cannot cancel a paid payment');
  }
  
  return updatePaymentStatus(payment, 'cancelled');
}

/**
 * 支払いが延滞かチェック
 */
export function isPaymentOverdue(payment: Payment): boolean {
  if (payment.status === 'paid' || payment.status === 'cancelled') {
    return false;
  }
  return new Date() > payment.dueDate;
}

/**
 * 延滞日数を取得
 */
export function getDaysOverdue(payment: Payment, asOfDate?: Date): number {
  const checkDate = asOfDate || new Date();
  
  if (payment.status === 'paid' || payment.status === 'cancelled') {
    return 0;
  }
  
  if (checkDate <= payment.dueDate) {
    return 0;
  }
  
  return Math.floor(
    (checkDate.getTime() - payment.dueDate.getTime()) / (24 * 60 * 60 * 1000)
  );
}

/**
 * 月額支払いスケジュールを生成
 * @see REQ-RENTAL-001 F040
 */
export function generateMonthlyPaymentSchedule(
  contractId: LeaseContractId,
  tenantId: TenantId,
  monthlyRent: number,
  maintenanceFee: number,
  startDate: Date,
  endDate: Date,
  paymentDay: number = 27  // 毎月27日が支払日
): Payment[] {
  const payments: Payment[] = [];
  
  let currentDate = new Date(startDate);
  currentDate.setDate(paymentDay);
  
  // 開始月より前の場合は翌月に調整
  if (currentDate < startDate) {
    currentDate.setMonth(currentDate.getMonth() + 1);
  }
  
  while (currentDate <= endDate) {
    // 家賃
    payments.push(createPayment({
      contractId,
      tenantId,
      amount: monthlyRent,
      paymentType: 'rent',
      paymentMethod: 'bank_transfer',
      dueDate: new Date(currentDate),
    }));
    
    // 管理費（0より大きい場合のみ）
    if (maintenanceFee > 0) {
      payments.push(createPayment({
        contractId,
        tenantId,
        amount: maintenanceFee,
        paymentType: 'maintenance_fee',
        paymentMethod: 'bank_transfer',
        dueDate: new Date(currentDate),
      }));
    }
    
    // 翌月に進む
    currentDate.setMonth(currentDate.getMonth() + 1);
  }
  
  return payments;
}

/**
 * 初期費用の支払いを生成（敷金、礼金など）
 */
export function generateInitialPayments(
  contractId: LeaseContractId,
  tenantId: TenantId,
  deposit: number,
  keyMoney: number,
  firstMonthRent: number,
  maintenanceFee: number,
  dueDate: Date
): Payment[] {
  const payments: Payment[] = [];
  
  // 敷金
  if (deposit > 0) {
    payments.push(createPayment({
      contractId,
      tenantId,
      amount: deposit,
      paymentType: 'deposit',
      paymentMethod: 'bank_transfer',
      dueDate,
    }));
  }
  
  // 礼金
  if (keyMoney > 0) {
    payments.push(createPayment({
      contractId,
      tenantId,
      amount: keyMoney,
      paymentType: 'key_money',
      paymentMethod: 'bank_transfer',
      dueDate,
    }));
  }
  
  // 初月家賃
  if (firstMonthRent > 0) {
    payments.push(createPayment({
      contractId,
      tenantId,
      amount: firstMonthRent,
      paymentType: 'rent',
      paymentMethod: 'bank_transfer',
      dueDate,
    }));
  }
  
  // 初月管理費
  if (maintenanceFee > 0) {
    payments.push(createPayment({
      contractId,
      tenantId,
      amount: maintenanceFee,
      paymentType: 'maintenance_fee',
      paymentMethod: 'bank_transfer',
      dueDate,
    }));
  }
  
  return payments;
}
