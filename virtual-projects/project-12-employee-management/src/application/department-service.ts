/**
 * Department Service
 * REQ-EMPLOYEE-001-F010, F011, F012 対応
 * BP-DESIGN-003: Service Layer with DI
 */

import {
  Department,
  DepartmentId,
  Employee,
  CreateDepartmentInput,
  DepartmentRepository,
  EmployeeRepository,
} from '../domain/types.js';
import { createDepartment, updateDepartment, hasCircularReference } from '../domain/department.js';
import { DepartmentNotFoundError, DuplicateDepartmentCodeError } from '../domain/errors.js';

export class DepartmentService {
  constructor(
    private readonly departmentRepository: DepartmentRepository,
    private readonly employeeRepository: EmployeeRepository
  ) {}

  /**
   * 部門作成 (REQ-EMPLOYEE-001-F010)
   * @param input 作成入力
   * @throws DuplicateDepartmentCodeError コードが重複する場合
   * @throws DepartmentNotFoundError 親部門が存在しない場合
   */
  async createDepartment(input: CreateDepartmentInput): Promise<Department> {
    // コード重複チェック
    const existingDepartment = await this.departmentRepository.findByCode(input.code);
    if (existingDepartment) {
      throw new DuplicateDepartmentCodeError(input.code);
    }

    // 親部門存在チェック
    if (input.parentId) {
      const parentDepartment = await this.departmentRepository.findById(input.parentId);
      if (!parentDepartment) {
        throw new DepartmentNotFoundError(input.parentId);
      }
    }

    const department = createDepartment(input);
    await this.departmentRepository.save(department);
    return department;
  }

  /**
   * 部門取得
   * @param id 部門ID
   * @throws DepartmentNotFoundError 部門が存在しない場合
   */
  async getDepartment(id: DepartmentId): Promise<Department> {
    const department = await this.departmentRepository.findById(id);
    if (!department) {
      throw new DepartmentNotFoundError(id);
    }
    return department;
  }

  /**
   * 部門メンバー取得 (REQ-EMPLOYEE-001-F012)
   * @param departmentId 部門ID
   * @throws DepartmentNotFoundError 部門が存在しない場合
   */
  async getDepartmentMembers(departmentId: DepartmentId): Promise<Employee[]> {
    const department = await this.departmentRepository.findById(departmentId);
    if (!department) {
      throw new DepartmentNotFoundError(departmentId);
    }

    return this.employeeRepository.findByDepartmentId(departmentId);
  }

  /**
   * 部門階層取得 (REQ-EMPLOYEE-001-F011)
   * @param departmentId 起点部門ID
   * @returns 子部門のリスト
   */
  async getChildDepartments(departmentId: DepartmentId): Promise<Department[]> {
    return this.departmentRepository.findByParentId(departmentId);
  }

  /**
   * 部門階層ツリー取得 (REQ-EMPLOYEE-001-F011)
   * @param departmentId 起点部門ID（省略時はルートから）
   */
  async getDepartmentTree(departmentId?: DepartmentId): Promise<DepartmentTreeNode[]> {
    const allDepartments = await this.departmentRepository.findAll();
    
    // ルート部門を取得（parentIdがないもの、または指定されたdepartmentIdの子）
    const rootDepartments = allDepartments.filter(d => 
      departmentId ? d.parentId === departmentId : !d.parentId
    );

    const buildTree = (departments: Department[]): DepartmentTreeNode[] => {
      return departments.map(dept => ({
        department: dept,
        children: buildTree(allDepartments.filter(d => d.parentId === dept.id)),
      }));
    };

    return buildTree(rootDepartments);
  }

  /**
   * 部門更新
   * @param id 部門ID
   * @param updates 更新内容
   * @throws DepartmentNotFoundError 部門が存在しない場合
   */
  async updateDepartmentInfo(
    id: DepartmentId,
    updates: Partial<Pick<Department, 'name' | 'parentId' | 'managerId' | 'description'>>
  ): Promise<Department> {
    const department = await this.departmentRepository.findById(id);
    if (!department) {
      throw new DepartmentNotFoundError(id);
    }

    // 親部門変更の場合、循環参照チェック
    if (updates.parentId && updates.parentId !== department.parentId) {
      const allDepartments = await this.departmentRepository.findAll();
      if (hasCircularReference(allDepartments, id, updates.parentId)) {
        throw new Error('Circular reference detected in department hierarchy');
      }
    }

    const updatedDepartment = updateDepartment(department, updates);
    await this.departmentRepository.save(updatedDepartment);
    return updatedDepartment;
  }

  /**
   * 全部門取得
   */
  async getAllDepartments(): Promise<Department[]> {
    return this.departmentRepository.findAll();
  }
}

/** 部門ツリーノード */
export interface DepartmentTreeNode {
  department: Department;
  children: DepartmentTreeNode[];
}
