/**
 * Payroll Repository
 * REQ-EMPLOYEE-001-F030 対応
 */

import {
  Payroll,
  PayrollId,
  EmployeeId,
  PayrollRepository,
} from '../domain/types.js';

/**
 * InMemory Payroll Repository
 * BP-DESIGN-002: Repository Async Pattern
 */
export class InMemoryPayrollRepository implements PayrollRepository {
  private payrolls: Map<PayrollId, Payroll> = new Map();

  async save(payroll: Payroll): Promise<void> {
    this.payrolls.set(payroll.id, payroll);
  }

  async findById(id: PayrollId): Promise<Payroll | null> {
    return this.payrolls.get(id) ?? null;
  }

  async findByEmployeeId(employeeId: EmployeeId): Promise<Payroll[]> {
    const result: Payroll[] = [];
    for (const payroll of this.payrolls.values()) {
      if (payroll.employeeId === employeeId) {
        result.push(payroll);
      }
    }
    return result.sort((a, b) => b.payPeriodStart.getTime() - a.payPeriodStart.getTime());
  }

  async findByPeriod(start: Date, end: Date): Promise<Payroll[]> {
    const result: Payroll[] = [];
    for (const payroll of this.payrolls.values()) {
      if (
        payroll.payPeriodStart >= start &&
        payroll.payPeriodEnd <= end
      ) {
        result.push(payroll);
      }
    }
    return result.sort((a, b) => a.payPeriodStart.getTime() - b.payPeriodStart.getTime());
  }

  async findAll(): Promise<Payroll[]> {
    return Array.from(this.payrolls.values());
  }

  async delete(id: PayrollId): Promise<void> {
    this.payrolls.delete(id);
  }

  /** テスト用: 全データクリア */
  clear(): void {
    this.payrolls.clear();
  }
}
