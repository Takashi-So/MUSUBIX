/**
 * Payroll Entity
 * REQ-EMPLOYEE-001-F030, F031, F032 対応
 */

import {
  Payroll,
  PayrollId,
  PayrollStatus,
  CreatePayrollInput,
  Money,
  TaxBracket,
} from './types.js';
import { createMoney, zeroMoney } from './money.js';
import { InvalidStatusTransitionError } from './errors.js';

// ID生成カウンター（テスト用リセット対応: BP-TEST-001）
let payrollCounter = 0;

/**
 * 給与IDカウンターリセット（テスト用）
 */
export function resetPayrollCounter(): void {
  payrollCounter = 0;
}

/**
 * 給与ID生成 (BP-CODE-002: Date-based ID Format)
 * Format: PAY-YYYYMMDD-NNN
 */
function generatePayrollId(): PayrollId {
  const now = new Date();
  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, '');
  payrollCounter++;
  const seq = String(payrollCounter).padStart(3, '0');
  return `PAY-${dateStr}-${seq}`;
}

/**
 * 有効なステータス遷移マップ (BP-DESIGN-001)
 * REQ-EMPLOYEE-001-F031 対応
 */
export const payrollStatusTransitions: Record<PayrollStatus, PayrollStatus[]> = {
  draft: ['pending_approval'],
  pending_approval: ['approved', 'draft'],
  approved: ['paid'],
  paid: [],
};

/**
 * 税率区分 (REQ-EMPLOYEE-001-F032)
 * Simplified progressive tax brackets
 */
export const taxBrackets: TaxBracket[] = [
  { minAmount: 0, maxAmount: 300000, rate: 0.05 },
  { minAmount: 300001, maxAmount: 500000, rate: 0.10 },
  { minAmount: 500001, maxAmount: 1000000, rate: 0.20 },
  { minAmount: 1000001, maxAmount: Infinity, rate: 0.30 },
];

/**
 * 給与作成 (REQ-EMPLOYEE-001-F030)
 * @param input 作成入力 (BP-CODE-001: Entity Input DTO)
 */
export function createPayroll(input: CreatePayrollInput): Payroll {
  const now = new Date();

  return {
    id: generatePayrollId(),
    employeeId: input.employeeId,
    payPeriodStart: input.payPeriodStart,
    payPeriodEnd: input.payPeriodEnd,
    baseSalary: input.baseSalary,
    overtimePay: input.overtimePay,
    allowances: input.allowances,
    grossPay: input.grossPay,
    taxDeduction: input.taxDeduction,
    otherDeductions: input.otherDeductions,
    netPay: input.netPay,
    status: 'draft', // Initial status
    createdAt: now,
    updatedAt: now,
  };
}

/**
 * 給与ステータス変更 (REQ-EMPLOYEE-001-F031)
 * @param payroll 給与
 * @param newStatus 新ステータス
 * @throws InvalidStatusTransitionError 無効な遷移の場合
 */
export function changePayrollStatus(
  payroll: Payroll,
  newStatus: PayrollStatus
): Payroll {
  const validTransitions = payrollStatusTransitions[payroll.status];
  
  if (!validTransitions.includes(newStatus)) {
    throw new InvalidStatusTransitionError(payroll.status, newStatus);
  }
  
  return {
    ...payroll,
    status: newStatus,
    updatedAt: new Date(),
  };
}

/**
 * 税金計算 (REQ-EMPLOYEE-001-F032)
 * @param grossPay 総支給額
 */
export function calculateTax(grossPay: Money): Money {
  const amount = grossPay.amount;
  let tax = 0;
  
  for (const bracket of taxBrackets) {
    if (amount >= bracket.minAmount) {
      const taxableInBracket = Math.min(
        amount - bracket.minAmount + 1,
        bracket.maxAmount - bracket.minAmount + 1
      );
      if (amount <= bracket.maxAmount) {
        // 全額がこの区分内
        tax = Math.round(amount * bracket.rate);
        break;
      }
    }
  }
  
  // Simplified: Use single bracket rate for entire amount
  const applicableBracket = taxBrackets.find(
    b => amount >= b.minAmount && amount <= b.maxAmount
  ) || taxBrackets[taxBrackets.length - 1];
  
  tax = Math.round(amount * applicableBracket.rate);
  
  return createMoney(tax, grossPay.currency);
}

/**
 * 時給計算
 * @param monthlySalary 月給
 * @param workingDaysPerMonth 月間勤務日数（デフォルト: 20日）
 * @param hoursPerDay 1日の勤務時間（デフォルト: 8時間）
 */
export function calculateHourlyRate(
  monthlySalary: Money,
  workingDaysPerMonth: number = 20,
  hoursPerDay: number = 8
): number {
  const totalHours = workingDaysPerMonth * hoursPerDay;
  return Math.round(monthlySalary.amount / totalHours);
}

/**
 * 残業代計算
 * @param hourlyRate 時給
 * @param overtimeHours 残業時間
 * @param overtimeMultiplier 残業倍率（デフォルト: 1.25）
 * @param currency 通貨
 */
export function calculateOvertimePay(
  hourlyRate: number,
  overtimeHours: number,
  overtimeMultiplier: number = 1.25,
  currency: Money['currency'] = 'JPY'
): Money {
  const overtimePay = Math.round(hourlyRate * overtimeMultiplier * overtimeHours);
  return createMoney(overtimePay, currency);
}

/**
 * ステータス遷移が有効かチェック
 */
export function isValidPayrollStatusTransition(
  from: PayrollStatus,
  to: PayrollStatus
): boolean {
  return payrollStatusTransitions[from].includes(to);
}
