/**
 * Employee Service
 * REQ-EMPLOYEE-001-F001, F002, F003, F040, F041 対応
 * BP-DESIGN-003: Service Layer with DI
 */

import {
  Employee,
  EmployeeId,
  EmployeeStatus,
  CreateEmployeeInput,
  EmployeeSearchCriteria,
  EmployeeRepository,
  DepartmentRepository,
} from '../domain/types.js';
import { createEmployee, changeEmployeeStatus, updateEmployee } from '../domain/employee.js';
import {
  EmployeeNotFoundError,
  DuplicateEmailError,
  DepartmentNotFoundError,
} from '../domain/errors.js';

export class EmployeeService {
  constructor(
    private readonly employeeRepository: EmployeeRepository,
    private readonly departmentRepository: DepartmentRepository
  ) {}

  /**
   * 従業員登録 (REQ-EMPLOYEE-001-F001)
   * @param input 登録入力
   * @throws DuplicateEmailError メールアドレスが重複する場合
   * @throws DepartmentNotFoundError 部門が存在しない場合
   */
  async registerEmployee(input: CreateEmployeeInput): Promise<Employee> {
    // REQ-EMPLOYEE-001-F040: 重複メールチェック
    const existingEmployee = await this.employeeRepository.findByEmail(input.email);
    if (existingEmployee) {
      throw new DuplicateEmailError(input.email);
    }

    // 部門存在チェック
    const department = await this.departmentRepository.findById(input.departmentId);
    if (!department) {
      throw new DepartmentNotFoundError(input.departmentId);
    }

    const employee = createEmployee(input);
    await this.employeeRepository.save(employee);
    return employee;
  }

  /**
   * 従業員取得
   * @param id 従業員ID
   * @throws EmployeeNotFoundError 従業員が存在しない場合
   */
  async getEmployee(id: EmployeeId): Promise<Employee> {
    const employee = await this.employeeRepository.findById(id);
    if (!employee) {
      throw new EmployeeNotFoundError(id);
    }
    return employee;
  }

  /**
   * 従業員ステータス変更 (REQ-EMPLOYEE-001-F002, F041)
   * @param id 従業員ID
   * @param newStatus 新ステータス
   * @throws EmployeeNotFoundError 従業員が存在しない場合
   * @throws InvalidStatusTransitionError 無効な遷移の場合
   */
  async changeStatus(id: EmployeeId, newStatus: EmployeeStatus): Promise<Employee> {
    const employee = await this.employeeRepository.findById(id);
    if (!employee) {
      throw new EmployeeNotFoundError(id);
    }

    const updatedEmployee = changeEmployeeStatus(employee, newStatus);
    await this.employeeRepository.save(updatedEmployee);
    return updatedEmployee;
  }

  /**
   * 従業員情報更新
   * @param id 従業員ID
   * @param updates 更新内容
   * @throws EmployeeNotFoundError 従業員が存在しない場合
   * @throws DuplicateEmailError メールアドレスが重複する場合
   */
  async updateEmployeeInfo(
    id: EmployeeId,
    updates: Partial<Pick<Employee, 'name' | 'email' | 'phone' | 'position' | 'departmentId' | 'salary'>>
  ): Promise<Employee> {
    const employee = await this.employeeRepository.findById(id);
    if (!employee) {
      throw new EmployeeNotFoundError(id);
    }

    // メールアドレス変更の場合、重複チェック
    if (updates.email && updates.email !== employee.email) {
      const existingEmployee = await this.employeeRepository.findByEmail(updates.email);
      if (existingEmployee) {
        throw new DuplicateEmailError(updates.email);
      }
    }

    // 部門変更の場合、存在チェック
    if (updates.departmentId && updates.departmentId !== employee.departmentId) {
      const department = await this.departmentRepository.findById(updates.departmentId);
      if (!department) {
        throw new DepartmentNotFoundError(updates.departmentId);
      }
    }

    const updatedEmployee = updateEmployee(employee, updates);
    await this.employeeRepository.save(updatedEmployee);
    return updatedEmployee;
  }

  /**
   * 従業員検索 (REQ-EMPLOYEE-001-F003)
   * @param criteria 検索条件
   */
  async searchEmployees(criteria: EmployeeSearchCriteria): Promise<Employee[]> {
    return this.employeeRepository.search(criteria);
  }

  /**
   * 全従業員取得
   */
  async getAllEmployees(): Promise<Employee[]> {
    return this.employeeRepository.findAll();
  }
}
