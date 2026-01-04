/**
 * Employee Management System - Type Definitions
 * REQ-EMPLOYEE-001 v1.1.0 対応
 */

// ============================================
// ID Types (BP-CODE-002: Date-based ID Format)
// ============================================

export type EmployeeId = string;   // Format: EMP-YYYYMMDD-NNN
export type DepartmentId = string; // Format: DEPT-YYYYMMDD-NNN
export type AttendanceId = string; // Format: ATT-YYYYMMDD-NNN
export type PayrollId = string;    // Format: PAY-YYYYMMDD-NNN

// ============================================
// Enums
// ============================================

/** 従業員ステータス (REQ-EMPLOYEE-001-F002) */
export type EmployeeStatus = 'active' | 'on_leave' | 'suspended' | 'terminated';

/** 雇用形態 (REQ-EMPLOYEE-001-F001) */
export type EmploymentType = 'full_time' | 'part_time' | 'contract';

/** 給与ステータス (REQ-EMPLOYEE-001-F031) */
export type PayrollStatus = 'draft' | 'pending_approval' | 'approved' | 'paid';

/** 通貨 */
export type Currency = 'JPY' | 'USD' | 'EUR';

// ============================================
// Value Objects
// ============================================

/** 金額 (REQ-EMPLOYEE-001-F030) */
export interface Money {
  readonly amount: number;
  readonly currency: Currency;
}

/** 人名 (REQ-EMPLOYEE-001-F001) */
export interface PersonName {
  readonly firstName: string;
  readonly lastName: string;
  readonly fullName: string;
}

// ============================================
// Entity Interfaces
// ============================================

/** 従業員エンティティ (REQ-EMPLOYEE-001-F001, F002) */
export interface Employee {
  readonly id: EmployeeId;
  readonly name: PersonName;
  readonly email: string;
  readonly phone?: string;
  readonly hireDate: Date;
  readonly departmentId: DepartmentId;
  readonly position: string;
  readonly employmentType: EmploymentType;
  readonly status: EmployeeStatus;
  readonly salary: Money;
  readonly createdAt: Date;
  readonly updatedAt: Date;
}

/** 部門エンティティ (REQ-EMPLOYEE-001-F010, F011) */
export interface Department {
  readonly id: DepartmentId;
  readonly name: string;
  readonly code: string;
  readonly parentId?: DepartmentId;
  readonly managerId?: EmployeeId;
  readonly description?: string;
  readonly createdAt: Date;
  readonly updatedAt: Date;
}

/** 勤怠記録エンティティ (REQ-EMPLOYEE-001-F020, F021) */
export interface Attendance {
  readonly id: AttendanceId;
  readonly employeeId: EmployeeId;
  readonly date: Date;
  readonly clockIn?: Date;
  readonly clockOut?: Date;
  readonly breakMinutes: number;
  readonly regularHours: number;
  readonly overtimeHours: number;
  readonly createdAt: Date;
  readonly updatedAt: Date;
}

/** 給与エンティティ (REQ-EMPLOYEE-001-F030, F031) */
export interface Payroll {
  readonly id: PayrollId;
  readonly employeeId: EmployeeId;
  readonly payPeriodStart: Date;
  readonly payPeriodEnd: Date;
  readonly baseSalary: Money;
  readonly overtimePay: Money;
  readonly allowances: Money;
  readonly grossPay: Money;
  readonly taxDeduction: Money;
  readonly otherDeductions: Money;
  readonly netPay: Money;
  readonly status: PayrollStatus;
  readonly createdAt: Date;
  readonly updatedAt: Date;
}

/** 月次勤怠サマリー (REQ-EMPLOYEE-001-F022) */
export interface MonthlySummary {
  readonly employeeId: EmployeeId;
  readonly year: number;
  readonly month: number;
  readonly totalWorkedDays: number;
  readonly totalRegularHours: number;
  readonly totalOvertimeHours: number;
}

// ============================================
// DTOs (BP-CODE-001: Entity Input DTO)
// ============================================

/** 従業員作成入力 */
export interface CreateEmployeeInput {
  readonly name: PersonName;
  readonly email: string;
  readonly phone?: string;
  readonly hireDate: Date;
  readonly departmentId: DepartmentId;
  readonly position: string;
  readonly employmentType: EmploymentType;
  readonly salary: Money;
}

/** 部門作成入力 */
export interface CreateDepartmentInput {
  readonly name: string;
  readonly code: string;
  readonly parentId?: DepartmentId;
  readonly managerId?: EmployeeId;
  readonly description?: string;
}

/** 勤怠作成入力 */
export interface CreateAttendanceInput {
  readonly employeeId: EmployeeId;
  readonly clockIn: Date;
}

/** 給与作成入力 */
export interface CreatePayrollInput {
  readonly employeeId: EmployeeId;
  readonly payPeriodStart: Date;
  readonly payPeriodEnd: Date;
  readonly baseSalary: Money;
  readonly overtimePay: Money;
  readonly allowances: Money;
  readonly grossPay: Money;
  readonly taxDeduction: Money;
  readonly otherDeductions: Money;
  readonly netPay: Money;
}

/** 従業員検索条件 (REQ-EMPLOYEE-001-F003) */
export interface EmployeeSearchCriteria {
  readonly name?: string;
  readonly departmentId?: DepartmentId;
  readonly position?: string;
  readonly employmentType?: EmploymentType;
  readonly status?: EmployeeStatus;
}

// ============================================
// Tax Configuration (REQ-EMPLOYEE-001-F032)
// ============================================

/** 税率区分 */
export interface TaxBracket {
  readonly minAmount: number;
  readonly maxAmount: number;
  readonly rate: number;
}

// ============================================
// Repository Interfaces
// ============================================

export interface EmployeeRepository {
  save(employee: Employee): Promise<void>;
  findById(id: EmployeeId): Promise<Employee | null>;
  findByEmail(email: string): Promise<Employee | null>;
  findByDepartmentId(departmentId: DepartmentId): Promise<Employee[]>;
  search(criteria: EmployeeSearchCriteria): Promise<Employee[]>;
  findAll(): Promise<Employee[]>;
  delete(id: EmployeeId): Promise<void>;
}

export interface DepartmentRepository {
  save(department: Department): Promise<void>;
  findById(id: DepartmentId): Promise<Department | null>;
  findByCode(code: string): Promise<Department | null>;
  findByParentId(parentId: DepartmentId): Promise<Department[]>;
  findAll(): Promise<Department[]>;
  delete(id: DepartmentId): Promise<void>;
}

export interface AttendanceRepository {
  save(attendance: Attendance): Promise<void>;
  findById(id: AttendanceId): Promise<Attendance | null>;
  findByEmployeeAndDate(employeeId: EmployeeId, date: Date): Promise<Attendance | null>;
  findByEmployeeAndMonth(employeeId: EmployeeId, year: number, month: number): Promise<Attendance[]>;
  findAll(): Promise<Attendance[]>;
  delete(id: AttendanceId): Promise<void>;
}

export interface PayrollRepository {
  save(payroll: Payroll): Promise<void>;
  findById(id: PayrollId): Promise<Payroll | null>;
  findByEmployeeId(employeeId: EmployeeId): Promise<Payroll[]>;
  findByPeriod(start: Date, end: Date): Promise<Payroll[]>;
  findAll(): Promise<Payroll[]>;
  delete(id: PayrollId): Promise<void>;
}
