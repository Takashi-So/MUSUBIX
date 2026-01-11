/**
 * SkillMetadata Value Object
 * 
 * Represents metadata about a skill
 * 
 * @see REQ-SKILL-001 - Skill Loading
 * @see DES-SKILL-001 - SkillManager
 */

import type { SkillType } from './SkillType.js';

/**
 * Skill parameter definition
 */
export interface SkillParameter {
  readonly name: string;
  readonly type: 'string' | 'number' | 'boolean' | 'array' | 'object';
  readonly required: boolean;
  readonly description: string;
  readonly default?: unknown;
}

/**
 * Skill metadata
 */
export interface SkillMetadata {
  readonly id: string;
  readonly name: string;
  readonly description: string;
  readonly type: SkillType;
  readonly version: string;
  readonly author: string;
  readonly parameters: readonly SkillParameter[];
  readonly tags: readonly string[];
  readonly createdAt: Date;
  readonly updatedAt: Date;
}

/**
 * Create skill metadata
 * 
 * @param params - Metadata parameters
 * @returns SkillMetadata
 */
export function createSkillMetadata(params: {
  id: string;
  name: string;
  description: string;
  type: SkillType;
  version?: string;
  author?: string;
  parameters?: SkillParameter[];
  tags?: string[];
}): SkillMetadata {
  const now = new Date();
  
  return Object.freeze({
    id: params.id,
    name: params.name,
    description: params.description,
    type: params.type,
    version: params.version ?? '1.0.0',
    author: params.author ?? 'MUSUBIX',
    parameters: Object.freeze(params.parameters ?? []),
    tags: Object.freeze(params.tags ?? []),
    createdAt: now,
    updatedAt: now,
  });
}

/**
 * Generate skill ID
 * 
 * @param type - Skill type
 * @param name - Skill name (optional)
 * @returns Skill ID
 */
export function generateSkillId(type: SkillType, name?: string): string {
  const timestamp = Date.now().toString(36);
  const prefix = type.substring(0, 3).toUpperCase();
  const suffix = name
    ? name.substring(0, 4).toUpperCase().replace(/[^A-Z]/g, 'X')
    : 'SKL';
  return `SKILL-${prefix}-${suffix}-${timestamp}`;
}

/**
 * Validate skill metadata
 * 
 * @param metadata - Metadata to validate
 * @returns Validation result
 */
export function validateSkillMetadata(metadata: SkillMetadata): {
  valid: boolean;
  errors: string[];
} {
  const errors: string[] = [];
  
  if (!metadata.id || metadata.id.trim() === '') {
    errors.push('Skill ID is required');
  }
  
  if (!metadata.name || metadata.name.trim() === '') {
    errors.push('Skill name is required');
  }
  
  if (!metadata.description || metadata.description.trim() === '') {
    errors.push('Skill description is required');
  }
  
  if (!metadata.type) {
    errors.push('Skill type is required');
  }
  
  // Validate parameters
  for (const param of metadata.parameters) {
    if (!param.name || param.name.trim() === '') {
      errors.push('Parameter name is required');
    }
    if (!param.type) {
      errors.push(`Parameter ${param.name} requires a type`);
    }
  }
  
  return {
    valid: errors.length === 0,
    errors,
  };
}

/**
 * Create parameter definition
 * 
 * @param params - Parameter definition
 * @returns SkillParameter
 */
export function createSkillParameter(params: {
  name: string;
  type: SkillParameter['type'];
  required?: boolean;
  description: string;
  default?: unknown;
}): SkillParameter {
  return Object.freeze({
    name: params.name,
    type: params.type,
    required: params.required ?? false,
    description: params.description,
    default: params.default,
  });
}
