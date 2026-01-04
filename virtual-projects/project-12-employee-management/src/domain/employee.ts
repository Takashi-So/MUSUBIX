/**
 * Employee Entity
 * REQ-EMPLOYEE-001-F001, F002, F041 対応
 */

import {
  Employee,
  EmployeeId,
  EmployeeStatus,
  CreateEmployeeInput,
  PersonName,
} from './types.js';
import { InvalidStatusTransitionError } from './errors.js';

// ID生成カウンター（テスト用リセット対応: BP-TEST-001）
let employeeCounter = 0;

/**
 * 従業員IDカウンターリセット（テスト用）
 */
export function resetEmployeeCounter(): void {
  employeeCounter = 0;
}

/**
 * 従業員ID生成 (BP-CODE-002: Date-based ID Format)
 * Format: EMP-YYYYMMDD-NNN
 */
function generateEmployeeId(): EmployeeId {
  const now = new Date();
  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, '');
  employeeCounter++;
  const seq = String(employeeCounter).padStart(3, '0');
  return `EMP-${dateStr}-${seq}`;
}

/**
 * 有効なステータス遷移マップ (BP-DESIGN-001)
 * REQ-EMPLOYEE-001-F002 対応
 */
export const employeeStatusTransitions: Record<EmployeeStatus, EmployeeStatus[]> = {
  active: ['on_leave', 'suspended', 'terminated'],
  on_leave: ['active'],
  suspended: ['active', 'terminated'],
  terminated: [],
};

/**
 * PersonName作成
 */
export function createPersonName(firstName: string, lastName: string): PersonName {
  if (!firstName.trim()) {
    throw new Error('First name is required');
  }
  if (!lastName.trim()) {
    throw new Error('Last name is required');
  }
  return {
    firstName: firstName.trim(),
    lastName: lastName.trim(),
    fullName: `${lastName.trim()} ${firstName.trim()}`, // Japanese style
  };
}

/**
 * 従業員作成 (REQ-EMPLOYEE-001-F001)
 * @param input 作成入力 (BP-CODE-001: Entity Input DTO)
 */
export function createEmployee(input: CreateEmployeeInput): Employee {
  const now = new Date();
  
  if (!input.email.trim()) {
    throw new Error('Email is required');
  }
  if (!input.position.trim()) {
    throw new Error('Position is required');
  }

  return {
    id: generateEmployeeId(),
    name: input.name,
    email: input.email.trim().toLowerCase(),
    phone: input.phone?.trim(),
    hireDate: input.hireDate,
    departmentId: input.departmentId,
    position: input.position.trim(),
    employmentType: input.employmentType,
    status: 'active', // Initial status
    salary: input.salary,
    createdAt: now,
    updatedAt: now,
  };
}

/**
 * 従業員ステータス変更 (REQ-EMPLOYEE-001-F002, F041)
 * @param employee 従業員
 * @param newStatus 新ステータス
 * @throws InvalidStatusTransitionError 無効な遷移の場合
 */
export function changeEmployeeStatus(
  employee: Employee,
  newStatus: EmployeeStatus
): Employee {
  const validTransitions = employeeStatusTransitions[employee.status];
  
  if (!validTransitions.includes(newStatus)) {
    throw new InvalidStatusTransitionError(employee.status, newStatus);
  }
  
  return {
    ...employee,
    status: newStatus,
    updatedAt: new Date(),
  };
}

/**
 * 従業員情報更新
 */
export function updateEmployee(
  employee: Employee,
  updates: Partial<Pick<Employee, 'name' | 'email' | 'phone' | 'position' | 'departmentId' | 'salary'>>
): Employee {
  return {
    ...employee,
    ...updates,
    updatedAt: new Date(),
  };
}

/**
 * ステータス遷移が有効かチェック
 */
export function isValidStatusTransition(
  from: EmployeeStatus,
  to: EmployeeStatus
): boolean {
  return employeeStatusTransitions[from].includes(to);
}
