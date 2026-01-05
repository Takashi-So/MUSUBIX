/**
 * @musubix/core - MUSUBIX Core Library
 * 
 * Neuro-Symbolic AI Integration Engine
 * 
 * @packageDocumentation
 * @module @musubix/core
 * 
 * @see REQ-ARC-001 - Library-First Architecture
 * @see DES-MUSUBIX-001 Section 3.1 - Project Structure
 */

// Version
export { VERSION } from './version.js';

// Export types
export * from './types/index.js';

// Export utilities
export * from './utils/index.js';

// Export CLI
export * from './cli/index.js';

// Export validators
export * from './validators/index.js';

// Export traceability
export * from './traceability/index.js';

// Export design
export * from './design/index.js';

// Export code generation
export * from './codegen/index.js';

// Export explanation
export * from './explanation/index.js';

// Export error recovery
export * from './error/index.js';

// Export learning system
export * from './learning/index.js';

// Export symbolic reasoning (Neuro-Symbolic Integration)
// Use namespace import to avoid name collisions with existing types
import * as symbolic from './symbolic/index.js';
export { symbolic };

// Re-export key symbolic functions at top level for convenience
export {
  createSymbolicPipeline,
  processSymbolic,
  SemanticCodeFilterPipeline,
  HallucinationDetector,
  ProjectSymbolIndex,
  ConstitutionRuleRegistry,
  ConfidenceEstimator,
  ConfidenceBasedRouter,
  ErrorHandler,
  DEFAULT_CONSTITUTION_RULES,
  checkArticleI,
  checkArticleII,
  checkArticleIII,
  checkArticleIV,
  checkArticleV,
  checkArticleVI,
  checkArticleVII,
  checkArticleVIII,
  checkArticleIX,
  // Phase 2: Formal Verification
  EarsToFormalSpecConverter,
  VerificationConditionGenerator,
  Z3Adapter,
  PreconditionVerifier,
  PostconditionVerifier,
  InvariantVerifier,
} from './symbolic/index.js';

// Re-export symbolic types for MCP tools
export type {
  FilterInput,
  FilterOutput,
  CodeCandidate,
  ProjectContext,
  SymbolInfo,
  HallucinationItem,
  HallucinationResult,
  ConstitutionRule,
  ConstitutionCheckInput,
  ConstitutionCheckResult,
  ConstitutionReport,
  ConfidenceEstimation,
  ConfidenceBreakdown,
  RiskFactor,
  RoutingResult,
  RoutingDecision,
  VerificationRequirement,
  RecoveryResult,
  ErrorClassification,
  FallbackAction,
  AuditLogEntry,
  // Phase 2: Formal Verification Types
  EarsRequirement,
  EarsPatternType,
  EarsAstNode,
  SmtLibOutput,
  FormalSpecification,
  VerificationCondition,
  VcGenerationResult,
  Z3Result,
  FormalVerificationResult,
} from './symbolic/index.js';

// Re-export modules (will be implemented in subsequent tasks)
// export * from './integrator/index.js';
// export * from './requirements/index.js';
// export * from './testing/index.js';

/**
 * Core Library Entry Point
 * 
 * This module exports all public APIs of the MUSUBIX core library.
 * 
 * @example
 * ```typescript
 * import { VERSION } from '@musubix/core';
 * console.log(`MUSUBIX Core v${VERSION}`);
 * ```
 */
