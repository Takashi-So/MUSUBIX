/**
 * Employee Repository
 * REQ-EMPLOYEE-001-F001, F003, F040 対応
 */

import {
  Employee,
  EmployeeId,
  DepartmentId,
  EmployeeRepository,
  EmployeeSearchCriteria,
} from '../domain/types.js';

/**
 * InMemory Employee Repository
 * BP-DESIGN-002: Repository Async Pattern
 */
export class InMemoryEmployeeRepository implements EmployeeRepository {
  private employees: Map<EmployeeId, Employee> = new Map();

  async save(employee: Employee): Promise<void> {
    this.employees.set(employee.id, employee);
  }

  async findById(id: EmployeeId): Promise<Employee | null> {
    return this.employees.get(id) ?? null;
  }

  async findByEmail(email: string): Promise<Employee | null> {
    const normalizedEmail = email.toLowerCase();
    for (const employee of this.employees.values()) {
      if (employee.email === normalizedEmail) {
        return employee;
      }
    }
    return null;
  }

  async findByDepartmentId(departmentId: DepartmentId): Promise<Employee[]> {
    const result: Employee[] = [];
    for (const employee of this.employees.values()) {
      if (employee.departmentId === departmentId) {
        result.push(employee);
      }
    }
    return result;
  }

  async search(criteria: EmployeeSearchCriteria): Promise<Employee[]> {
    const result: Employee[] = [];
    
    for (const employee of this.employees.values()) {
      let matches = true;
      
      if (criteria.name) {
        const searchName = criteria.name.toLowerCase();
        const fullName = employee.name.fullName.toLowerCase();
        matches = matches && fullName.includes(searchName);
      }
      
      if (criteria.departmentId) {
        matches = matches && employee.departmentId === criteria.departmentId;
      }
      
      if (criteria.position) {
        matches = matches && employee.position.toLowerCase().includes(criteria.position.toLowerCase());
      }
      
      if (criteria.employmentType) {
        matches = matches && employee.employmentType === criteria.employmentType;
      }
      
      if (criteria.status) {
        matches = matches && employee.status === criteria.status;
      }
      
      if (matches) {
        result.push(employee);
      }
    }
    
    return result;
  }

  async findAll(): Promise<Employee[]> {
    return Array.from(this.employees.values());
  }

  async delete(id: EmployeeId): Promise<void> {
    this.employees.delete(id);
  }

  /** テスト用: 全データクリア */
  clear(): void {
    this.employees.clear();
  }
}
