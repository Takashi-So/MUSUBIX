/**
 * Domain Errors
 * REQ-EMPLOYEE-001 対応
 */

import { EmployeeId, DepartmentId, PayrollId, EmployeeStatus, PayrollStatus } from './types.js';

/** 従業員が見つからないエラー */
export class EmployeeNotFoundError extends Error {
  constructor(id: EmployeeId) {
    super(`Employee not found: ${id}`);
    this.name = 'EmployeeNotFoundError';
  }
}

/** メールアドレス重複エラー (REQ-EMPLOYEE-001-F040) */
export class DuplicateEmailError extends Error {
  constructor(email: string) {
    super(`Email already registered: ${email}`);
    this.name = 'DuplicateEmailError';
  }
}

/** 無効なステータス遷移エラー (REQ-EMPLOYEE-001-F041) */
export class InvalidStatusTransitionError extends Error {
  constructor(from: string, to: string) {
    super(`Invalid status transition from ${from} to ${to}`);
    this.name = 'InvalidStatusTransitionError';
  }
}

/** 部門が見つからないエラー */
export class DepartmentNotFoundError extends Error {
  constructor(id: DepartmentId) {
    super(`Department not found: ${id}`);
    this.name = 'DepartmentNotFoundError';
  }
}

/** 部門コード重複エラー */
export class DuplicateDepartmentCodeError extends Error {
  constructor(code: string) {
    super(`Department code already exists: ${code}`);
    this.name = 'DuplicateDepartmentCodeError';
  }
}

/** 既にクロックインエラー */
export class AlreadyClockedInError extends Error {
  constructor(employeeId: EmployeeId) {
    super(`Employee ${employeeId} already clocked in today`);
    this.name = 'AlreadyClockedInError';
  }
}

/** クロックインしていないエラー (REQ-EMPLOYEE-001-F042) */
export class NotClockedInError extends Error {
  constructor(employeeId: EmployeeId) {
    super(`Employee ${employeeId} has not clocked in today`);
    this.name = 'NotClockedInError';
  }
}

/** 既にクロックアウトエラー */
export class AlreadyClockedOutError extends Error {
  constructor(employeeId: EmployeeId) {
    super(`Employee ${employeeId} already clocked out today`);
    this.name = 'AlreadyClockedOutError';
  }
}

/** 給与が見つからないエラー */
export class PayrollNotFoundError extends Error {
  constructor(id: PayrollId) {
    super(`Payroll not found: ${id}`);
    this.name = 'PayrollNotFoundError';
  }
}

/** 勤怠記録が見つからないエラー */
export class AttendanceNotFoundError extends Error {
  constructor(id: string) {
    super(`Attendance not found: ${id}`);
    this.name = 'AttendanceNotFoundError';
  }
}
