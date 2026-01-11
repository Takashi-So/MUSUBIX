/**
 * @nahisaho/musubix-skill-manager
 * 
 * Skill Manager for MUSUBIX - Skill Loading, Validation and Registry
 * 
 * @packageDocumentation
 * @module skill-manager
 * 
 * @see REQ-SKILL-001 - Skill Loading
 * @see REQ-SKILL-002 - Skill Validation
 */

// Domain Layer
export * from './domain/index.js';

// Application Layer
export * from './application/index.js';

// Re-export key types for convenience
export type {
  SkillType,
  SkillMetadata,
  SkillParameter,
  Skill,
  SkillContext,
  SkillResult,
  SkillExecutor,
  SkillRegistry,
  SkillFilter,
} from './domain/index.js';

export type {
  ValidationResult,
  ParameterValidationResult,
  SkillManagerConfig,
  SkillRegistrationResult,
} from './application/index.js';