/**
 * AgentRole Value Object
 * 
 * Represents the role of a subagent in task execution
 * 
 * @see REQ-SDD-002 - Subagent Decomposition
 * @see DES-SDD-002 - SubagentDispatcher
 */

/**
 * Available agent role names
 */
export type AgentRoleName = 
  | 'requirements'
  | 'design'
  | 'implementation'
  | 'test'
  | 'review';

/**
 * Immutable agent role value object
 */
export interface AgentRole {
  /** Role name */
  readonly name: AgentRoleName;
  /** Role capabilities */
  readonly capabilities: readonly string[];
  /** Role constraints */
  readonly constraints: readonly string[];
  /** Role description */
  readonly description: string;
}

/**
 * Default role definitions
 */
export const DEFAULT_ROLES: ReadonlyMap<AgentRoleName, AgentRole> = new Map([
  ['requirements', {
    name: 'requirements',
    capabilities: ['EARS analysis', 'requirement decomposition', 'priority assessment'],
    constraints: ['must follow EARS format', 'must include traceability IDs'],
    description: '要件分析・EARS形式変換を担当',
  }],
  ['design', {
    name: 'design',
    capabilities: ['C4 modeling', 'pattern selection', 'interface design'],
    constraints: ['must maintain REQ traceability', 'must follow SOLID principles'],
    description: '設計・C4モデル作成を担当',
  }],
  ['implementation', {
    name: 'implementation',
    capabilities: ['code generation', 'refactoring', 'optimization'],
    constraints: ['must follow design specs', 'must include tests'],
    description: 'コード実装を担当',
  }],
  ['test', {
    name: 'test',
    capabilities: ['test generation', 'coverage analysis', 'edge case identification'],
    constraints: ['must achieve 80%+ coverage', 'must test edge cases'],
    description: 'テスト作成・検証を担当',
  }],
  ['review', {
    name: 'review',
    capabilities: ['code review', 'quality assessment', 'improvement suggestions'],
    constraints: ['must check constitution compliance', 'must verify traceability'],
    description: 'レビュー・品質チェックを担当',
  }],
]);

/**
 * Get agent role by name
 * 
 * @param name - Role name
 * @returns AgentRole or undefined
 */
export function getAgentRole(name: AgentRoleName): AgentRole | undefined {
  return DEFAULT_ROLES.get(name);
}

/**
 * Get all available role names
 * 
 * @returns Array of role names
 */
export function getAllRoleNames(): AgentRoleName[] {
  return Array.from(DEFAULT_ROLES.keys());
}

/**
 * Create a custom agent role
 * 
 * @param name - Role name
 * @param capabilities - Role capabilities
 * @param constraints - Role constraints
 * @param description - Role description
 * @returns AgentRole
 */
export function createAgentRole(
  name: AgentRoleName,
  capabilities: string[],
  constraints: string[],
  description: string
): AgentRole {
  return Object.freeze({
    name,
    capabilities: Object.freeze([...capabilities]),
    constraints: Object.freeze([...constraints]),
    description,
  });
}
