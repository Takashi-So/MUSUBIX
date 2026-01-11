/**
 * SkillRegistry Entity
 * 
 * Registry of available skills
 * 
 * @see REQ-SKILL-001 - Skill Loading
 * @see REQ-SKILL-002 - Skill Validation
 */

import type { Skill, SkillContext, SkillResult } from './Skill.js';
import { executeSkill, skillMatchesFilter } from './Skill.js';
import type { SkillType } from '../value-objects/index.js';

/**
 * Skill filter criteria
 */
export interface SkillFilter {
  readonly type?: SkillType;
  readonly tags?: readonly string[];
  readonly enabledOnly?: boolean;
  readonly query?: string;
}

/**
 * Skill registry entity
 */
export interface SkillRegistry {
  readonly skills: ReadonlyMap<string, Skill>;
  readonly updatedAt: Date;
}

/**
 * Create an empty skill registry
 * 
 * @returns Empty registry
 */
export function createSkillRegistry(): SkillRegistry {
  return Object.freeze({
    skills: new Map(),
    updatedAt: new Date(),
  });
}

/**
 * Add skill to registry
 * 
 * @param registry - Registry to update
 * @param skill - Skill to add
 * @returns Updated registry
 */
export function addSkillToRegistry(
  registry: SkillRegistry,
  skill: Skill
): SkillRegistry {
  const skills = new Map(registry.skills);
  skills.set(skill.metadata.id, skill);
  
  return Object.freeze({
    skills,
    updatedAt: new Date(),
  });
}

/**
 * Remove skill from registry
 * 
 * @param registry - Registry to update
 * @param skillId - Skill ID to remove
 * @returns Updated registry
 */
export function removeSkillFromRegistry(
  registry: SkillRegistry,
  skillId: string
): SkillRegistry {
  const skills = new Map(registry.skills);
  skills.delete(skillId);
  
  return Object.freeze({
    skills,
    updatedAt: new Date(),
  });
}

/**
 * Get skill by ID
 * 
 * @param registry - Registry to search
 * @param skillId - Skill ID
 * @returns Skill or undefined
 */
export function getSkillById(
  registry: SkillRegistry,
  skillId: string
): Skill | undefined {
  return registry.skills.get(skillId);
}

/**
 * Find skills by filter
 * 
 * @param registry - Registry to search
 * @param filter - Filter criteria
 * @returns Matching skills
 */
export function findSkills(
  registry: SkillRegistry,
  filter: SkillFilter
): Skill[] {
  const results: Skill[] = [];
  
  for (const skill of registry.skills.values()) {
    if (!skillMatchesFilter(skill, {
      type: filter.type,
      tags: filter.tags ? [...filter.tags] : undefined,
      enabledOnly: filter.enabledOnly,
    })) {
      continue;
    }
    
    // Query search (if provided)
    if (filter.query) {
      const query = filter.query.toLowerCase();
      const matches =
        skill.metadata.name.toLowerCase().includes(query) ||
        skill.metadata.description.toLowerCase().includes(query) ||
        skill.metadata.tags.some(tag => tag.toLowerCase().includes(query));
      
      if (!matches) {
        continue;
      }
    }
    
    results.push(skill);
  }
  
  return results;
}

/**
 * Get all skills from registry
 * 
 * @param registry - Registry
 * @returns All skills
 */
export function getAllSkills(registry: SkillRegistry): Skill[] {
  return Array.from(registry.skills.values());
}

/**
 * Get skills by type
 * 
 * @param registry - Registry
 * @param type - Skill type
 * @returns Skills of the specified type
 */
export function getSkillsByType(
  registry: SkillRegistry,
  type: SkillType
): Skill[] {
  return findSkills(registry, { type, enabledOnly: true });
}

/**
 * Execute a skill from registry
 * 
 * @param registry - Registry
 * @param skillId - Skill ID
 * @param context - Execution context
 * @returns Execution result
 */
export async function executeSkillFromRegistry(
  registry: SkillRegistry,
  skillId: string,
  context: SkillContext
): Promise<SkillResult> {
  const skill = getSkillById(registry, skillId);
  
  if (!skill) {
    return {
      success: false,
      error: `Skill not found: ${skillId}`,
      duration: 0,
      timestamp: new Date(),
    };
  }
  
  return executeSkill(skill, context);
}

/**
 * Get registry statistics
 * 
 * @param registry - Registry
 * @returns Statistics
 */
export function getRegistryStats(registry: SkillRegistry): {
  total: number;
  enabled: number;
  disabled: number;
  byType: Record<string, number>;
} {
  let enabled = 0;
  let disabled = 0;
  const byType: Record<string, number> = {};
  
  for (const skill of registry.skills.values()) {
    if (skill.enabled) {
      enabled++;
    } else {
      disabled++;
    }
    
    const type = skill.metadata.type;
    byType[type] = (byType[type] ?? 0) + 1;
  }
  
  return {
    total: registry.skills.size,
    enabled,
    disabled,
    byType,
  };
}
