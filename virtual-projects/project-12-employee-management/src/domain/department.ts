/**
 * Department Entity
 * REQ-EMPLOYEE-001-F010, F011 対応
 */

import {
  Department,
  DepartmentId,
  CreateDepartmentInput,
} from './types.js';

// ID生成カウンター（テスト用リセット対応: BP-TEST-001）
let departmentCounter = 0;

/**
 * 部門IDカウンターリセット（テスト用）
 */
export function resetDepartmentCounter(): void {
  departmentCounter = 0;
}

/**
 * 部門ID生成 (BP-CODE-002: Date-based ID Format)
 * Format: DEPT-YYYYMMDD-NNN
 */
function generateDepartmentId(): DepartmentId {
  const now = new Date();
  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, '');
  departmentCounter++;
  const seq = String(departmentCounter).padStart(3, '0');
  return `DEPT-${dateStr}-${seq}`;
}

/**
 * 部門作成 (REQ-EMPLOYEE-001-F010)
 * @param input 作成入力 (BP-CODE-001: Entity Input DTO)
 */
export function createDepartment(input: CreateDepartmentInput): Department {
  const now = new Date();
  
  if (!input.name.trim()) {
    throw new Error('Department name is required');
  }
  if (!input.code.trim()) {
    throw new Error('Department code is required');
  }
  if (!/^[A-Za-z0-9]+$/.test(input.code.trim())) {
    throw new Error('Department code must be alphanumeric');
  }

  return {
    id: generateDepartmentId(),
    name: input.name.trim(),
    code: input.code.trim().toUpperCase(),
    parentId: input.parentId,
    managerId: input.managerId,
    description: input.description?.trim(),
    createdAt: now,
    updatedAt: now,
  };
}

/**
 * 部門情報更新
 */
export function updateDepartment(
  department: Department,
  updates: Partial<Pick<Department, 'name' | 'parentId' | 'managerId' | 'description'>>
): Department {
  return {
    ...department,
    ...updates,
    updatedAt: new Date(),
  };
}

/**
 * 循環参照チェック
 * @param departments 全部門リスト
 * @param departmentId チェック対象部門ID
 * @param newParentId 新しい親部門ID
 * @returns true: 循環参照あり, false: なし
 */
export function hasCircularReference(
  departments: Department[],
  departmentId: DepartmentId,
  newParentId: DepartmentId
): boolean {
  const departmentMap = new Map(departments.map(d => [d.id, d]));
  
  let currentId: DepartmentId | undefined = newParentId;
  const visited = new Set<DepartmentId>();
  
  while (currentId) {
    if (currentId === departmentId) {
      return true; // 循環参照検出
    }
    if (visited.has(currentId)) {
      return true; // 既存の循環
    }
    visited.add(currentId);
    const current = departmentMap.get(currentId);
    currentId = current?.parentId;
  }
  
  return false;
}
