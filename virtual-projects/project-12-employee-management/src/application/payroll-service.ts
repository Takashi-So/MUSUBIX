/**
 * Payroll Service
 * REQ-EMPLOYEE-001-F030, F031, F032 対応
 * BP-DESIGN-003: Service Layer with DI
 */

import {
  Payroll,
  PayrollId,
  PayrollStatus,
  EmployeeId,
  Money,
  PayrollRepository,
  EmployeeRepository,
  AttendanceRepository,
} from '../domain/types.js';
import {
  createPayroll,
  changePayrollStatus,
  calculateTax,
  calculateHourlyRate,
  calculateOvertimePay,
} from '../domain/payroll.js';
import { createMoney, addMoney, subtractMoney, zeroMoney } from '../domain/money.js';
import { EmployeeNotFoundError, PayrollNotFoundError } from '../domain/errors.js';

export class PayrollService {
  constructor(
    private readonly payrollRepository: PayrollRepository,
    private readonly employeeRepository: EmployeeRepository,
    private readonly attendanceRepository: AttendanceRepository
  ) {}

  /**
   * 給与計算 (REQ-EMPLOYEE-001-F030)
   * @param employeeId 従業員ID
   * @param payPeriodStart 支払期間開始
   * @param payPeriodEnd 支払期間終了
   * @param allowances 手当（オプション）
   * @param otherDeductions その他控除（オプション）
   * @throws EmployeeNotFoundError 従業員が存在しない場合
   */
  async calculatePayroll(
    employeeId: EmployeeId,
    payPeriodStart: Date,
    payPeriodEnd: Date,
    allowances?: Money,
    otherDeductions?: Money
  ): Promise<Payroll> {
    // 従業員取得
    const employee = await this.employeeRepository.findById(employeeId);
    if (!employee) {
      throw new EmployeeNotFoundError(employeeId);
    }

    // 勤怠記録から残業時間を集計
    const year = payPeriodStart.getFullYear();
    const month = payPeriodStart.getMonth() + 1;
    const attendanceRecords = await this.attendanceRepository.findByEmployeeAndMonth(
      employeeId,
      year,
      month
    );

    let totalOvertimeHours = 0;
    for (const record of attendanceRecords) {
      totalOvertimeHours += record.overtimeHours;
    }

    // 給与計算
    const baseSalary = employee.salary;
    const hourlyRate = calculateHourlyRate(baseSalary);
    const overtimePay = calculateOvertimePay(hourlyRate, totalOvertimeHours, 1.25, baseSalary.currency);
    
    const allowanceAmount = allowances ?? zeroMoney(baseSalary.currency);
    const grossPay = addMoney(addMoney(baseSalary, overtimePay), allowanceAmount);
    
    // REQ-EMPLOYEE-001-F032: 税金計算
    const taxDeduction = calculateTax(grossPay);
    const deductionAmount = otherDeductions ?? zeroMoney(baseSalary.currency);
    const totalDeductions = addMoney(taxDeduction, deductionAmount);
    const netPay = subtractMoney(grossPay, totalDeductions);

    const payroll = createPayroll({
      employeeId,
      payPeriodStart,
      payPeriodEnd,
      baseSalary,
      overtimePay,
      allowances: allowanceAmount,
      grossPay,
      taxDeduction,
      otherDeductions: deductionAmount,
      netPay,
    });

    await this.payrollRepository.save(payroll);
    return payroll;
  }

  /**
   * 給与取得
   * @param id 給与ID
   * @throws PayrollNotFoundError 給与が存在しない場合
   */
  async getPayroll(id: PayrollId): Promise<Payroll> {
    const payroll = await this.payrollRepository.findById(id);
    if (!payroll) {
      throw new PayrollNotFoundError(id);
    }
    return payroll;
  }

  /**
   * 給与ステータス更新 (REQ-EMPLOYEE-001-F031)
   * @param id 給与ID
   * @param newStatus 新ステータス
   * @throws PayrollNotFoundError 給与が存在しない場合
   * @throws InvalidStatusTransitionError 無効な遷移の場合
   */
  async updateStatus(id: PayrollId, newStatus: PayrollStatus): Promise<Payroll> {
    const payroll = await this.payrollRepository.findById(id);
    if (!payroll) {
      throw new PayrollNotFoundError(id);
    }

    const updatedPayroll = changePayrollStatus(payroll, newStatus);
    await this.payrollRepository.save(updatedPayroll);
    return updatedPayroll;
  }

  /**
   * 承認申請
   */
  async submitForApproval(id: PayrollId): Promise<Payroll> {
    return this.updateStatus(id, 'pending_approval');
  }

  /**
   * 承認
   */
  async approve(id: PayrollId): Promise<Payroll> {
    return this.updateStatus(id, 'approved');
  }

  /**
   * 支払い完了
   */
  async markAsPaid(id: PayrollId): Promise<Payroll> {
    return this.updateStatus(id, 'paid');
  }

  /**
   * 差し戻し
   */
  async reject(id: PayrollId): Promise<Payroll> {
    return this.updateStatus(id, 'draft');
  }

  /**
   * 従業員の給与履歴取得
   * @param employeeId 従業員ID
   */
  async getPayrollHistory(employeeId: EmployeeId): Promise<Payroll[]> {
    return this.payrollRepository.findByEmployeeId(employeeId);
  }

  /**
   * 期間内の給与一覧取得
   * @param start 開始日
   * @param end 終了日
   */
  async getPayrollsByPeriod(start: Date, end: Date): Promise<Payroll[]> {
    return this.payrollRepository.findByPeriod(start, end);
  }
}
