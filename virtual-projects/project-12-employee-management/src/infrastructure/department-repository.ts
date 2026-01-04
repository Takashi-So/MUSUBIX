/**
 * Department Repository
 * REQ-EMPLOYEE-001-F010, F011, F012 対応
 */

import {
  Department,
  DepartmentId,
  DepartmentRepository,
} from '../domain/types.js';

/**
 * InMemory Department Repository
 * BP-DESIGN-002: Repository Async Pattern
 */
export class InMemoryDepartmentRepository implements DepartmentRepository {
  private departments: Map<DepartmentId, Department> = new Map();

  async save(department: Department): Promise<void> {
    this.departments.set(department.id, department);
  }

  async findById(id: DepartmentId): Promise<Department | null> {
    return this.departments.get(id) ?? null;
  }

  async findByCode(code: string): Promise<Department | null> {
    const normalizedCode = code.toUpperCase();
    for (const department of this.departments.values()) {
      if (department.code === normalizedCode) {
        return department;
      }
    }
    return null;
  }

  async findByParentId(parentId: DepartmentId): Promise<Department[]> {
    const result: Department[] = [];
    for (const department of this.departments.values()) {
      if (department.parentId === parentId) {
        result.push(department);
      }
    }
    return result;
  }

  async findAll(): Promise<Department[]> {
    return Array.from(this.departments.values());
  }

  async delete(id: DepartmentId): Promise<void> {
    this.departments.delete(id);
  }

  /** テスト用: 全データクリア */
  clear(): void {
    this.departments.clear();
  }
}
