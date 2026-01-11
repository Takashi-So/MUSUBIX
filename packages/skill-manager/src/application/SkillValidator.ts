/**
 * SkillValidator - Application Service
 * 
 * Validates skill definitions and execution
 * 
 * @see TSK-SKILL-001 - SkillValidator
 * @see REQ-SKILL-002 - Skill Validation
 * @see DES-SKILL-002 - SkillValidator
 */

import {
  type Skill,
  type SkillContext,
  type SkillMetadata,
  type SkillParameter,
  validateSkillMetadata,
} from '../domain/index.js';

/**
 * Validation result
 */
export interface ValidationResult {
  readonly valid: boolean;
  readonly errors: readonly string[];
  readonly warnings: readonly string[];
}

/**
 * Parameter validation result
 */
export interface ParameterValidationResult extends ValidationResult {
  readonly missing: readonly string[];
  readonly invalid: readonly string[];
}

/**
 * Skill Validator
 * 
 * Validates skill definitions and parameters
 */
export class SkillValidator {
  /**
   * Validate skill definition
   * 
   * @param skill - Skill to validate
   * @returns Validation result
   */
  validateSkill(skill: Skill): ValidationResult {
    const errors: string[] = [];
    const warnings: string[] = [];
    
    // Validate metadata
    const metadataResult = validateSkillMetadata(skill.metadata);
    if (!metadataResult.valid) {
      errors.push(...metadataResult.errors);
    }
    
    // Validate executor
    if (typeof skill.executor !== 'function') {
      errors.push('Skill executor must be a function');
    }
    
    // Check for common issues
    if (skill.metadata.parameters.length > 10) {
      warnings.push('Skill has many parameters, consider simplifying');
    }
    
    if (skill.metadata.description.length < 10) {
      warnings.push('Skill description is very short');
    }
    
    return {
      valid: errors.length === 0,
      errors: Object.freeze(errors),
      warnings: Object.freeze(warnings),
    };
  }

  /**
   * Validate execution context against skill parameters
   * 
   * @param skill - Skill
   * @param context - Execution context
   * @returns Parameter validation result
   */
  validateParameters(
    skill: Skill,
    context: SkillContext
  ): ParameterValidationResult {
    const errors: string[] = [];
    const warnings: string[] = [];
    const missing: string[] = [];
    const invalid: string[] = [];
    
    for (const param of skill.metadata.parameters) {
      const value = context.parameters[param.name];
      
      // Check required parameters
      if (param.required && value === undefined) {
        missing.push(param.name);
        errors.push(`Required parameter missing: ${param.name}`);
        continue;
      }
      
      // Skip validation if not provided and not required
      if (value === undefined) {
        continue;
      }
      
      // Type validation
      if (!this.validateParameterType(value, param.type)) {
        invalid.push(param.name);
        errors.push(
          `Parameter ${param.name} has invalid type. ` +
          `Expected ${param.type}, got ${typeof value}`
        );
      }
    }
    
    // Check for unknown parameters
    const paramNames = new Set(skill.metadata.parameters.map(p => p.name));
    for (const key of Object.keys(context.parameters)) {
      if (!paramNames.has(key)) {
        warnings.push(`Unknown parameter: ${key}`);
      }
    }
    
    return {
      valid: errors.length === 0,
      errors: Object.freeze(errors),
      warnings: Object.freeze(warnings),
      missing: Object.freeze(missing),
      invalid: Object.freeze(invalid),
    };
  }

  /**
   * Validate parameter type
   * 
   * @param value - Value to check
   * @param expectedType - Expected type
   * @returns true if valid
   */
  private validateParameterType(
    value: unknown,
    expectedType: SkillParameter['type']
  ): boolean {
    switch (expectedType) {
      case 'string':
        return typeof value === 'string';
      case 'number':
        return typeof value === 'number' && !isNaN(value);
      case 'boolean':
        return typeof value === 'boolean';
      case 'array':
        return Array.isArray(value);
      case 'object':
        return typeof value === 'object' && value !== null && !Array.isArray(value);
      default:
        return false;
    }
  }

  /**
   * Create validation error message
   * 
   * @param result - Validation result
   * @returns Formatted error message
   */
  formatValidationResult(result: ValidationResult): string {
    const lines: string[] = [];
    
    if (result.valid) {
      lines.push('✅ Validation passed');
    } else {
      lines.push('❌ Validation failed');
      lines.push('');
      lines.push('**Errors:**');
      for (const error of result.errors) {
        lines.push(`- ${error}`);
      }
    }
    
    if (result.warnings.length > 0) {
      lines.push('');
      lines.push('**Warnings:**');
      for (const warning of result.warnings) {
        lines.push(`- ⚠️ ${warning}`);
      }
    }
    
    return lines.join('\n');
  }

  /**
   * Validate skill metadata only
   * 
   * @param metadata - Metadata to validate
   * @returns Validation result
   */
  validateMetadata(metadata: SkillMetadata): ValidationResult {
    const result = validateSkillMetadata(metadata);
    return {
      valid: result.valid,
      errors: Object.freeze(result.errors),
      warnings: Object.freeze([]),
    };
  }
}

/**
 * Create a skill validator instance
 * 
 * @returns SkillValidator instance
 */
export function createSkillValidator(): SkillValidator {
  return new SkillValidator();
}
