/**
 * @fileoverview Remediation Module Exports
 * @module @nahisaho/musubix-security/remediation
 */

// Auto-Fixer
export {
  AutoFixer,
  createAutoFixer,
  getBuiltInTemplates,
  createFixTemplate,
  type FixTemplate,
  type CodeTransformation,
  type ImportSpec,
  type FixApplicationResult,
  type FixGenerationOptions,
  type AutoFixerOptions,
} from './auto-fixer.js';

// Fix Validator
export {
  FixValidator,
  createFixValidator,
  quickValidate,
  type ValidationResult,
  type ValidationCheck,
  type SyntaxValidationResult,
  type RegressionTestResult,
  type SecurityRescanResult,
  type FixValidatorOptions,
  type CustomValidationRule,
} from './fix-validator.js';

// Patch Generator
export {
  PatchGenerator,
  createPatchGenerator,
  generateQuickPatch,
  type Patch,
  type PatchFormat,
  type PatchFile,
  type PatchHunk,
  type PatchLine,
  type PatchMetadata,
  type PatchGenerationOptions,
  type PatchApplicationResult,
  type PatchGeneratorOptions,
} from './patch-generator.js';

// Remediation Planner
export {
  RemediationPlanner,
  createRemediationPlanner,
  quickCreatePlan,
  type RemediationPlan,
  type PlanStatus,
  type RemediationPhase,
  type PlannedFix,
  type FixStatus,
  type FixDependency,
  type DependencyType,
  type EffortEstimate,
  type Duration,
  type RiskReduction,
  type RiskLevel,
  type PlanMetadata,
  type PrioritizationStrategy,
  type RemediationPlannerOptions,
  type PlanningOptions,
} from './remediation-planner.js';

// Secure Code Transformer
export {
  SecureCodeTransformer,
  createSecureCodeTransformer,
  quickTransform,
  getBuiltInTransformations,
  type CodeTransformation as TransformationDefinition,
  type TransformationCategory,
  type CodePattern,
  type PatternContext,
  type ReplacementPattern,
  type ImportSpec as TransformImportSpec,
  type TransformationResult,
  type AppliedTransformation,
  type SecureCodeTransformerOptions,
  type TransformOptions,
} from './secure-code-transformer.js';
