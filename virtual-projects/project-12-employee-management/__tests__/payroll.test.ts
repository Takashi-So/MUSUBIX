/**
 * Payroll Entity and Service Tests
 * REQ-EMPLOYEE-001-F030, F031, F032
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createPayroll,
  changePayrollStatus,
  calculateTax,
  calculateHourlyRate,
  calculateOvertimePay,
  resetPayrollCounter,
  payrollStatusTransitions,
} from '../src/domain/payroll.js';
import { createMoney, addMoney, subtractMoney, zeroMoney } from '../src/domain/money.js';
import { createEmployee, resetEmployeeCounter, createPersonName } from '../src/domain/employee.js';
import { createDepartment, resetDepartmentCounter } from '../src/domain/department.js';
import { createAttendance, recordClockOut, resetAttendanceCounter } from '../src/domain/attendance.js';
import { InvalidStatusTransitionError, PayrollNotFoundError, EmployeeNotFoundError } from '../src/domain/errors.js';
import { InMemoryPayrollRepository } from '../src/infrastructure/payroll-repository.js';
import { InMemoryEmployeeRepository } from '../src/infrastructure/employee-repository.js';
import { InMemoryAttendanceRepository } from '../src/infrastructure/attendance-repository.js';
import { InMemoryDepartmentRepository } from '../src/infrastructure/department-repository.js';
import { PayrollService } from '../src/application/payroll-service.js';

describe('Payroll Entity', () => {
  beforeEach(() => {
    resetPayrollCounter();
  });

  describe('createPayroll (REQ-EMPLOYEE-001-F030)', () => {
    it('should create payroll with correct ID format', () => {
      const payroll = createPayroll({
        employeeId: 'EMP-001',
        payPeriodStart: new Date('2026-01-01'),
        payPeriodEnd: new Date('2026-01-31'),
        baseSalary: createMoney(500000),
        overtimePay: createMoney(50000),
        allowances: createMoney(20000),
        grossPay: createMoney(570000),
        taxDeduction: createMoney(57000),
        otherDeductions: createMoney(10000),
        netPay: createMoney(503000),
      });

      expect(payroll.id).toMatch(/^PAY-\d{8}-001$/);
      expect(payroll.status).toBe('draft');
      expect(payroll.baseSalary.amount).toBe(500000);
    });
  });

  describe('calculateTax (REQ-EMPLOYEE-001-F032)', () => {
    it('should calculate 5% for income <= 300,000', () => {
      const tax = calculateTax(createMoney(300000));
      expect(tax.amount).toBe(15000); // 300000 * 0.05
    });

    it('should calculate 10% for income 300,001 - 500,000', () => {
      const tax = calculateTax(createMoney(400000));
      expect(tax.amount).toBe(40000); // 400000 * 0.10
    });

    it('should calculate 20% for income 500,001 - 1,000,000', () => {
      const tax = calculateTax(createMoney(800000));
      expect(tax.amount).toBe(160000); // 800000 * 0.20
    });

    it('should calculate 30% for income > 1,000,000', () => {
      const tax = calculateTax(createMoney(1500000));
      expect(tax.amount).toBe(450000); // 1500000 * 0.30
    });
  });

  describe('calculateHourlyRate', () => {
    it('should calculate hourly rate from monthly salary', () => {
      const monthlySalary = createMoney(320000); // 320,000 JPY
      const hourlyRate = calculateHourlyRate(monthlySalary, 20, 8);
      
      // 320000 / (20 * 8) = 2000
      expect(hourlyRate).toBe(2000);
    });
  });

  describe('calculateOvertimePay', () => {
    it('should calculate overtime pay with 1.25 multiplier', () => {
      const overtimePay = calculateOvertimePay(2000, 10, 1.25);
      
      // 2000 * 1.25 * 10 = 25000
      expect(overtimePay.amount).toBe(25000);
    });
  });

  describe('changePayrollStatus (REQ-EMPLOYEE-001-F031)', () => {
    it('should allow valid status transitions', () => {
      let payroll = createPayroll({
        employeeId: 'EMP-001',
        payPeriodStart: new Date('2026-01-01'),
        payPeriodEnd: new Date('2026-01-31'),
        baseSalary: createMoney(500000),
        overtimePay: createMoney(0),
        allowances: createMoney(0),
        grossPay: createMoney(500000),
        taxDeduction: createMoney(50000),
        otherDeductions: createMoney(0),
        netPay: createMoney(450000),
      });

      // draft → pending_approval
      payroll = changePayrollStatus(payroll, 'pending_approval');
      expect(payroll.status).toBe('pending_approval');

      // pending_approval → approved
      payroll = changePayrollStatus(payroll, 'approved');
      expect(payroll.status).toBe('approved');

      // approved → paid
      payroll = changePayrollStatus(payroll, 'paid');
      expect(payroll.status).toBe('paid');
    });

    it('should reject invalid status transitions', () => {
      const payroll = createPayroll({
        employeeId: 'EMP-001',
        payPeriodStart: new Date('2026-01-01'),
        payPeriodEnd: new Date('2026-01-31'),
        baseSalary: createMoney(500000),
        overtimePay: createMoney(0),
        allowances: createMoney(0),
        grossPay: createMoney(500000),
        taxDeduction: createMoney(50000),
        otherDeductions: createMoney(0),
        netPay: createMoney(450000),
      });

      // draft → paid (invalid)
      expect(() => changePayrollStatus(payroll, 'paid'))
        .toThrow(InvalidStatusTransitionError);
    });
  });
});

describe('PayrollService', () => {
  let payrollRepository: InMemoryPayrollRepository;
  let employeeRepository: InMemoryEmployeeRepository;
  let attendanceRepository: InMemoryAttendanceRepository;
  let departmentRepository: InMemoryDepartmentRepository;
  let payrollService: PayrollService;
  let testEmployeeId: string;

  beforeEach(async () => {
    resetPayrollCounter();
    resetEmployeeCounter();
    resetAttendanceCounter();
    resetDepartmentCounter();

    payrollRepository = new InMemoryPayrollRepository();
    employeeRepository = new InMemoryEmployeeRepository();
    attendanceRepository = new InMemoryAttendanceRepository();
    departmentRepository = new InMemoryDepartmentRepository();
    payrollService = new PayrollService(
      payrollRepository,
      employeeRepository,
      attendanceRepository
    );

    // Setup test employee
    const dept = createDepartment({ name: 'Engineering', code: 'ENG' });
    await departmentRepository.save(dept);

    const name = createPersonName('太郎', '山田');
    const employee = createEmployee({
      name,
      email: 'test@example.com',
      hireDate: new Date(),
      departmentId: dept.id,
      position: 'Engineer',
      employmentType: 'full_time',
      salary: createMoney(400000),
    });
    await employeeRepository.save(employee);
    testEmployeeId = employee.id;
  });

  describe('calculatePayroll (REQ-EMPLOYEE-001-F030)', () => {
    it('should calculate payroll correctly', async () => {
      const payroll = await payrollService.calculatePayroll(
        testEmployeeId,
        new Date('2026-01-01'),
        new Date('2026-01-31')
      );

      expect(payroll.employeeId).toBe(testEmployeeId);
      expect(payroll.baseSalary.amount).toBe(400000);
      expect(payroll.status).toBe('draft');
    });

    it('should include overtime pay when there are overtime records', async () => {
      // Add attendance records with overtime
      const clockIn = new Date('2026-01-15T09:00:00');
      const clockOut = new Date('2026-01-15T21:00:00'); // 12 hours - 1 break = 11 hours = 3 overtime

      const attendance = createAttendance({ employeeId: testEmployeeId, clockIn });
      const updatedAttendance = recordClockOut(attendance, clockOut);
      await attendanceRepository.save(updatedAttendance);

      const payroll = await payrollService.calculatePayroll(
        testEmployeeId,
        new Date('2026-01-01'),
        new Date('2026-01-31')
      );

      expect(payroll.overtimePay.amount).toBeGreaterThan(0);
    });

    it('should reject non-existent employee', async () => {
      await expect(payrollService.calculatePayroll(
        'NON-EXISTENT',
        new Date('2026-01-01'),
        new Date('2026-01-31')
      )).rejects.toThrow(EmployeeNotFoundError);
    });
  });

  describe('payroll workflow (REQ-EMPLOYEE-001-F031)', () => {
    it('should complete full workflow: draft → pending → approved → paid', async () => {
      const payroll = await payrollService.calculatePayroll(
        testEmployeeId,
        new Date('2026-01-01'),
        new Date('2026-01-31')
      );
      expect(payroll.status).toBe('draft');

      const pending = await payrollService.submitForApproval(payroll.id);
      expect(pending.status).toBe('pending_approval');

      const approved = await payrollService.approve(payroll.id);
      expect(approved.status).toBe('approved');

      const paid = await payrollService.markAsPaid(payroll.id);
      expect(paid.status).toBe('paid');
    });

    it('should allow rejection (send back to draft)', async () => {
      const payroll = await payrollService.calculatePayroll(
        testEmployeeId,
        new Date('2026-01-01'),
        new Date('2026-01-31')
      );
      await payrollService.submitForApproval(payroll.id);

      const rejected = await payrollService.reject(payroll.id);
      expect(rejected.status).toBe('draft');
    });
  });
});

describe('Money Value Object', () => {
  it('should add money correctly', () => {
    const a = createMoney(100000);
    const b = createMoney(50000);
    const result = addMoney(a, b);
    expect(result.amount).toBe(150000);
  });

  it('should subtract money correctly', () => {
    const a = createMoney(100000);
    const b = createMoney(30000);
    const result = subtractMoney(a, b);
    expect(result.amount).toBe(70000);
  });

  it('should reject negative amounts', () => {
    expect(() => createMoney(-100)).toThrow('Amount cannot be negative');
  });

  it('should reject currency mismatch', () => {
    const jpy = createMoney(100000, 'JPY');
    const usd = createMoney(1000, 'USD');
    expect(() => addMoney(jpy, usd)).toThrow('Currency mismatch');
  });
});
