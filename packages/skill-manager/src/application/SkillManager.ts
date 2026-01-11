/**
 * SkillManager - Application Service
 * 
 * Main service for managing skills
 * 
 * @see TSK-SKILL-002 - SkillManager
 * @see REQ-SKILL-001 - Skill Loading
 * @see DES-SKILL-001 - SkillManager Component
 */

import {
  type Skill,
  type SkillContext,
  type SkillResult,
  type SkillRegistry,
  type SkillFilter,
  type SkillType,
  type SkillExecutor,
  createSkillRegistry,
  addSkillToRegistry,
  removeSkillFromRegistry,
  getSkillById,
  findSkills,
  getAllSkills,
  executeSkillFromRegistry,
  getRegistryStats,
  createSkill,
  createSkillMetadata,
  enableSkill,
  disableSkill,
} from '../domain/index.js';
import { type ValidationResult, SkillValidator } from './SkillValidator.js';

/**
 * Skill manager configuration
 */
export interface SkillManagerConfig {
  /** Auto-validate skills on registration */
  autoValidate?: boolean;
  /** Allow registering invalid skills */
  allowInvalid?: boolean;
}

/**
 * Skill registration result
 */
export interface SkillRegistrationResult {
  readonly success: boolean;
  readonly skillId?: string;
  readonly error?: string;
  readonly validation?: ValidationResult;
}

/**
 * Skill Manager
 * 
 * Manages skill lifecycle and execution
 */
export class SkillManager {
  private registry: SkillRegistry;
  private readonly validator: SkillValidator;
  private readonly config: SkillManagerConfig;

  constructor(config: SkillManagerConfig = {}) {
    this.registry = createSkillRegistry();
    this.validator = new SkillValidator();
    this.config = {
      autoValidate: true,
      allowInvalid: false,
      ...config,
    };
  }

  /**
   * Register a skill
   * 
   * @param skill - Skill to register
   * @returns Registration result
   */
  registerSkill(skill: Skill): SkillRegistrationResult {
    // Validate if configured
    if (this.config.autoValidate) {
      const validation = this.validator.validateSkill(skill);
      
      if (!validation.valid && !this.config.allowInvalid) {
        return {
          success: false,
          error: `Skill validation failed: ${validation.errors.join(', ')}`,
          validation,
        };
      }
      
      this.registry = addSkillToRegistry(this.registry, skill);
      
      return {
        success: true,
        skillId: skill.metadata.id,
        validation,
      };
    }
    
    this.registry = addSkillToRegistry(this.registry, skill);
    
    return {
      success: true,
      skillId: skill.metadata.id,
    };
  }

  /**
   * Create and register a skill
   * 
   * @param metadata - Skill metadata params
   * @param executor - Skill executor
   * @returns Registration result
   */
  createAndRegister(
    metadata: Parameters<typeof createSkillMetadata>[0],
    executor: SkillExecutor
  ): SkillRegistrationResult {
    const skillMetadata = createSkillMetadata(metadata);
    const skill = createSkill(skillMetadata, executor);
    return this.registerSkill(skill);
  }

  /**
   * Unregister a skill
   * 
   * @param skillId - Skill ID
   * @returns true if removed
   */
  unregisterSkill(skillId: string): boolean {
    const skill = getSkillById(this.registry, skillId);
    if (!skill) {
      return false;
    }
    
    this.registry = removeSkillFromRegistry(this.registry, skillId);
    return true;
  }

  /**
   * Get a skill by ID
   * 
   * @param skillId - Skill ID
   * @returns Skill or undefined
   */
  getSkill(skillId: string): Skill | undefined {
    return getSkillById(this.registry, skillId);
  }

  /**
   * Find skills by filter
   * 
   * @param filter - Filter criteria
   * @returns Matching skills
   */
  findSkills(filter: SkillFilter): Skill[] {
    return findSkills(this.registry, filter);
  }

  /**
   * Get all skills
   * 
   * @returns All skills
   */
  getAllSkills(): Skill[] {
    return getAllSkills(this.registry);
  }

  /**
   * Execute a skill
   * 
   * @param skillId - Skill ID
   * @param context - Execution context
   * @returns Execution result
   */
  async executeSkill(
    skillId: string,
    context: SkillContext
  ): Promise<SkillResult> {
    const skill = getSkillById(this.registry, skillId);
    
    if (!skill) {
      return {
        success: false,
        error: `Skill not found: ${skillId}`,
        duration: 0,
        timestamp: new Date(),
      };
    }
    
    // Validate parameters if configured
    if (this.config.autoValidate) {
      const paramValidation = this.validator.validateParameters(skill, context);
      
      if (!paramValidation.valid) {
        return {
          success: false,
          error: `Parameter validation failed: ${paramValidation.errors.join(', ')}`,
          duration: 0,
          timestamp: new Date(),
        };
      }
    }
    
    return executeSkillFromRegistry(this.registry, skillId, context);
  }

  /**
   * Enable a skill
   * 
   * @param skillId - Skill ID
   * @returns true if enabled
   */
  enableSkill(skillId: string): boolean {
    const skill = getSkillById(this.registry, skillId);
    if (!skill) {
      return false;
    }
    
    const enabled = enableSkill(skill);
    this.registry = addSkillToRegistry(this.registry, enabled);
    return true;
  }

  /**
   * Disable a skill
   * 
   * @param skillId - Skill ID
   * @returns true if disabled
   */
  disableSkill(skillId: string): boolean {
    const skill = getSkillById(this.registry, skillId);
    if (!skill) {
      return false;
    }
    
    const disabled = disableSkill(skill);
    this.registry = addSkillToRegistry(this.registry, disabled);
    return true;
  }

  /**
   * Get registry statistics
   * 
   * @returns Statistics
   */
  getStats(): ReturnType<typeof getRegistryStats> {
    return getRegistryStats(this.registry);
  }

  /**
   * Validate a skill without registering
   * 
   * @param skill - Skill to validate
   * @returns Validation result
   */
  validateSkill(skill: Skill): ValidationResult {
    return this.validator.validateSkill(skill);
  }

  /**
   * Clear all skills
   */
  clearAll(): void {
    this.registry = createSkillRegistry();
  }

  /**
   * Get skills by type
   * 
   * @param type - Skill type
   * @returns Skills of the specified type
   */
  getSkillsByType(type: SkillType): Skill[] {
    return this.findSkills({ type, enabledOnly: true });
  }

  /**
   * Check if a skill exists
   * 
   * @param skillId - Skill ID
   * @returns true if exists
   */
  hasSkill(skillId: string): boolean {
    return getSkillById(this.registry, skillId) !== undefined;
  }
}

/**
 * Create a skill manager instance
 * 
 * @param config - Configuration
 * @returns SkillManager instance
 */
export function createSkillManager(config?: SkillManagerConfig): SkillManager {
  return new SkillManager(config);
}
