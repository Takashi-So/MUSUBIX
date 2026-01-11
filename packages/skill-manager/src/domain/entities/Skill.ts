/**
 * Skill Entity
 * 
 * Represents a skill that can be executed
 * 
 * @see REQ-SKILL-001 - Skill Loading
 * @see DES-SKILL-001 - SkillManager
 */

import type { SkillMetadata } from '../value-objects/index.js';

/**
 * Skill execution context
 */
export interface SkillContext {
  readonly workflowId?: string;
  readonly phaseType?: string;
  readonly taskId?: string;
  readonly parameters: Record<string, unknown>;
}

/**
 * Skill execution result
 */
export interface SkillResult {
  readonly success: boolean;
  readonly data?: unknown;
  readonly error?: string;
  readonly duration: number;
  readonly timestamp: Date;
}

/**
 * Skill executor function type
 */
export type SkillExecutor = (context: SkillContext) => Promise<SkillResult>;

/**
 * Skill entity
 */
export interface Skill {
  readonly metadata: SkillMetadata;
  readonly executor: SkillExecutor;
  readonly enabled: boolean;
}

/**
 * Create a skill
 * 
 * @param metadata - Skill metadata
 * @param executor - Skill executor
 * @param enabled - Whether skill is enabled
 * @returns Skill entity
 */
export function createSkill(
  metadata: SkillMetadata,
  executor: SkillExecutor,
  enabled: boolean = true
): Skill {
  return Object.freeze({
    metadata,
    executor,
    enabled,
  });
}

/**
 * Execute a skill
 * 
 * @param skill - Skill to execute
 * @param context - Execution context
 * @returns Execution result
 */
export async function executeSkill(
  skill: Skill,
  context: SkillContext
): Promise<SkillResult> {
  if (!skill.enabled) {
    return {
      success: false,
      error: `Skill ${skill.metadata.id} is disabled`,
      duration: 0,
      timestamp: new Date(),
    };
  }
  
  const startTime = Date.now();
  
  try {
    const result = await skill.executor(context);
    return {
      ...result,
      duration: Date.now() - startTime,
      timestamp: new Date(),
    };
  } catch (error) {
    return {
      success: false,
      error: error instanceof Error ? error.message : String(error),
      duration: Date.now() - startTime,
      timestamp: new Date(),
    };
  }
}

/**
 * Enable a skill
 * 
 * @param skill - Skill to enable
 * @returns Enabled skill
 */
export function enableSkill(skill: Skill): Skill {
  return Object.freeze({
    ...skill,
    enabled: true,
  });
}

/**
 * Disable a skill
 * 
 * @param skill - Skill to disable
 * @returns Disabled skill
 */
export function disableSkill(skill: Skill): Skill {
  return Object.freeze({
    ...skill,
    enabled: false,
  });
}

/**
 * Check if skill matches filter
 * 
 * @param skill - Skill to check
 * @param filter - Filter criteria
 * @returns true if matches
 */
export function skillMatchesFilter(
  skill: Skill,
  filter: {
    type?: string;
    tags?: string[];
    enabledOnly?: boolean;
  }
): boolean {
  if (filter.enabledOnly && !skill.enabled) {
    return false;
  }
  
  if (filter.type && skill.metadata.type !== filter.type) {
    return false;
  }
  
  if (filter.tags && filter.tags.length > 0) {
    const hasAllTags = filter.tags.every(tag =>
      skill.metadata.tags.includes(tag)
    );
    if (!hasAllTags) {
      return false;
    }
  }
  
  return true;
}

/**
 * Create a no-op skill result
 * 
 * @param message - Message
 * @returns Skill result
 */
export function createNoOpResult(message: string): SkillResult {
  return {
    success: true,
    data: message,
    duration: 0,
    timestamp: new Date(),
  };
}

/**
 * Create an error result
 * 
 * @param error - Error message
 * @param duration - Duration in ms
 * @returns Skill result
 */
export function createErrorResult(error: string, duration: number = 0): SkillResult {
  return {
    success: false,
    error,
    duration,
    timestamp: new Date(),
  };
}
