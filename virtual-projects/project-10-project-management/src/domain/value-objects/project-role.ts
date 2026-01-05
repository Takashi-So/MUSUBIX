/**
 * Project Role Value Object
 * 
 * @see REQ-PM-MEM-001, MEM-002, MEM-003 - メンバー管理
 * @see DES-PM-001 Section 3.2.2
 * @see TSK-PM-001 - Value Objects実装
 */

export type ProjectRole = 'owner' | 'admin' | 'member' | 'viewer';

/**
 * Role hierarchy (higher number = more permissions)
 */
export const roleHierarchy: Record<ProjectRole, number> = {
  owner: 4,
  admin: 3,
  member: 2,
  viewer: 1,
};

/**
 * Check if role has admin privileges (owner or admin)
 */
export function hasAdminPrivilege(role: ProjectRole): boolean {
  return roleHierarchy[role] >= roleHierarchy.admin;
}

/**
 * Check if role can manage members (owner or admin)
 */
export function canManageMembers(role: ProjectRole): boolean {
  return hasAdminPrivilege(role);
}

/**
 * Check if role can edit project settings
 */
export function canEditProject(role: ProjectRole): boolean {
  return roleHierarchy[role] >= roleHierarchy.member;
}

/**
 * Check if role A has higher or equal privilege than role B
 */
export function hasHigherOrEqualPrivilege(roleA: ProjectRole, roleB: ProjectRole): boolean {
  return roleHierarchy[roleA] >= roleHierarchy[roleB];
}
