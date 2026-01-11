/**
 * SubagentDispatcher Application Service
 * 
 * Dispatches tasks to specialized subagents
 * 
 * @see REQ-SDD-002 - Subagent Decomposition
 * @see DES-SDD-002 - SubagentDispatcher
 */

import type { Task } from '../domain/entities/Task.js';
import type { ExecutionContext } from '../domain/entities/ExecutionContext.js';
import {
  type SubagentSpec,
  type SubagentResult,
  createSubagentSpec,
} from '../domain/entities/SubagentSpec.js';
import {
  type AgentRole,
  type AgentRoleName,
  getAgentRole,
  getAllRoleNames,
} from '../domain/value-objects/AgentRole.js';
import type { ComplexityScore } from '../domain/value-objects/ComplexityScore.js';

/**
 * Subagent dispatcher interface
 */
export interface ISubagentDispatcher {
  /**
   * Decompose task into subagent specs
   * @param task - Task to decompose
   * @param score - Complexity score
   * @param context - Execution context
   * @returns Subagent specifications
   */
  decompose(
    task: Task,
    score: ComplexityScore,
    context: ExecutionContext
  ): SubagentSpec[];

  /**
   * Generate prompt for a role
   * @param role - Agent role
   * @param task - Task to execute
   * @param context - Execution context
   * @returns Generated prompt
   */
  generatePrompt(
    role: AgentRole,
    task: Task,
    context: ExecutionContext
  ): string;

  /**
   * Get available roles
   * @returns All available role names
   */
  getAvailableRoles(): AgentRoleName[];
}

/**
 * Aggregated result from multiple subagents
 */
export interface AggregatedResult {
  /** All results */
  readonly results: readonly SubagentResult[];
  /** Success status (all succeeded) */
  readonly success: boolean;
  /** Combined content */
  readonly combinedContent: string;
  /** Failed results */
  readonly failures: readonly SubagentResult[];
  /** Total duration */
  readonly totalDurationMs: number;
}

/**
 * Dispatcher configuration
 */
export interface SubagentDispatcherConfig {
  /** Default timeout per subagent (ms) */
  defaultTimeoutMs?: number;
  /** Role selection strategy */
  roleStrategy?: 'all' | 'minimal' | 'custom';
  /** Custom roles to use (if roleStrategy is 'custom') */
  customRoles?: AgentRoleName[];
}

/**
 * Create a subagent dispatcher
 * 
 * @param config - Optional configuration
 * @returns ISubagentDispatcher implementation
 */
export function createSubagentDispatcher(
  config: SubagentDispatcherConfig = {}
): ISubagentDispatcher {
  const defaultTimeoutMs = config.defaultTimeoutMs ?? 300000; // 5 minutes
  const roleStrategy = config.roleStrategy ?? 'minimal';

  /**
   * Select roles based on task and strategy
   */
  function selectRoles(task: Task, _score: ComplexityScore): AgentRoleName[] {
    if (roleStrategy === 'custom' && config.customRoles) {
      return config.customRoles;
    }

    if (roleStrategy === 'all') {
      return getAllRoleNames();
    }

    // Minimal strategy: select based on task properties
    const roles: AgentRoleName[] = [];

    // Always need implementation
    roles.push('implementation');

    // Need tests if coverage required
    if (task.testCoverageRequired > 0) {
      roles.push('test');
    }

    // Need design if complex or has many dependencies
    if (task.dependencyCount > 3 || task.estimatedScope > 3) {
      roles.push('design');
    }

    // Need requirements if related requirements exist
    if (task.relatedRequirements.length > 0) {
      roles.push('requirements');
    }

    // Need review for high complexity
    if (task.uncertaintyLevel > 5) {
      roles.push('review');
    }

    return roles;
  }

  /**
   * Generate spec ID
   */
  function generateSpecId(taskId: string, role: AgentRoleName, index: number): string {
    return `${taskId}-${role}-${index.toString().padStart(3, '0')}`;
  }

  /**
   * Determine dependencies between roles
   */
  function getRoleDependencies(role: AgentRoleName, allRoles: AgentRoleName[]): AgentRoleName[] {
    const deps: AgentRoleName[] = [];

    switch (role) {
      case 'design':
        if (allRoles.includes('requirements')) deps.push('requirements');
        break;
      case 'implementation':
        if (allRoles.includes('design')) deps.push('design');
        else if (allRoles.includes('requirements')) deps.push('requirements');
        break;
      case 'test':
        if (allRoles.includes('implementation')) deps.push('implementation');
        break;
      case 'review':
        if (allRoles.includes('implementation')) deps.push('implementation');
        if (allRoles.includes('test')) deps.push('test');
        break;
    }

    return deps;
  }

  return {
    decompose(
      task: Task,
      score: ComplexityScore,
      context: ExecutionContext
    ): SubagentSpec[] {
      const selectedRoles = selectRoles(task, score);
      const specs: SubagentSpec[] = [];
      const specIdMap = new Map<AgentRoleName, string>();

      // First pass: create specs and map IDs
      selectedRoles.forEach((roleName, idx) => {
        const specId = generateSpecId(task.id, roleName, idx);
        specIdMap.set(roleName, specId);
      });

      // Second pass: create specs with dependencies
      selectedRoles.forEach((roleName) => {
        const role = getAgentRole(roleName);
        if (!role) return;

        const specId = specIdMap.get(roleName)!;
        const prompt = this.generatePrompt(role, task, context);
        
        // Map role dependencies to spec IDs
        const roleDeps = getRoleDependencies(roleName, selectedRoles);
        const dependencies = roleDeps
          .map((depRole) => specIdMap.get(depRole))
          .filter((id): id is string => id !== undefined);

        specs.push(
          createSubagentSpec({
            id: specId,
            role,
            prompt,
            inputContext: context,
            outputExpectation: getOutputExpectation(roleName),
            timeoutMs: defaultTimeoutMs,
            dependencies,
          })
        );
      });

      return specs;
    },

    generatePrompt(
      role: AgentRole,
      task: Task,
      context: ExecutionContext
    ): string {
      const basePrompt = `
## Task Information
- **ID**: ${task.id}
- **Title**: ${task.title}
- **Description**: ${task.description}
- **Priority**: ${task.priority.label}

## Your Role: ${role.name}
${role.description}

### Capabilities
${role.capabilities.map((c) => `- ${c}`).join('\n')}

### Constraints
${role.constraints.map((c) => `- ${c}`).join('\n')}

## Context
- Project Path: ${context.metadata.projectPath ?? 'Not specified'}
- Related Files: ${context.metadata.relatedFiles.join(', ') || 'None'}
- Tags: ${context.metadata.tags.join(', ') || 'None'}

## Related Traceability
- Requirements: ${task.relatedRequirements.join(', ') || 'None'}
- Designs: ${task.relatedDesigns.join(', ') || 'None'}

## Instructions
Please execute your role for this task following the capabilities and constraints above.
Ensure all outputs include appropriate traceability IDs.
`;

      return basePrompt.trim();
    },

    getAvailableRoles(): AgentRoleName[] {
      return getAllRoleNames();
    },
  };
}

/**
 * Get expected output description for a role
 */
function getOutputExpectation(role: AgentRoleName): string {
  switch (role) {
    case 'requirements':
      return 'EARS-format requirements with REQ-* IDs';
    case 'design':
      return 'C4 model design with DES-* IDs';
    case 'implementation':
      return 'TypeScript code with traceability comments';
    case 'test':
      return 'Vitest test files with 80%+ coverage';
    case 'review':
      return 'Review report with findings and recommendations';
    default:
      return 'Task output';
  }
}

/**
 * Aggregate results from multiple subagents
 * 
 * @param results - Subagent results
 * @returns Aggregated result
 */
export function aggregateResults(results: SubagentResult[]): AggregatedResult {
  const failures = results.filter((r) => !r.success);
  const success = failures.length === 0;
  const totalDurationMs = results.reduce((sum, r) => sum + r.durationMs, 0);
  
  const combinedContent = results
    .filter((r) => r.success)
    .map((r) => `## ${r.specId}\n\n${r.content}`)
    .join('\n\n---\n\n');

  return Object.freeze({
    results: Object.freeze([...results]),
    success,
    combinedContent,
    failures: Object.freeze(failures),
    totalDurationMs,
  });
}
