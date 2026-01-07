/**
 * @fileoverview Main entry point for @nahisaho/musubix-lean
 * @module @nahisaho/musubix-lean
 * @version 2.0.0-alpha.1
 */

// ============================================================================
// Types
// ============================================================================
export type {
  // Core types
  LeanConfig,
  LeanVersion,
  LeanTheorem,
  LeanProof,
  LeanHypothesis,
  LeanExpression,
  LeanEnvironmentInfo,
  
  // Verification types
  VerificationResult,
  VerificationReport,
  ReportFormat,
  ReportStatistics,
  ProofFeedback,
  ProofGoal,
  ProofState,
  
  // Conversion types
  EarsRequirement,
  EarsPattern,
  EarsParsedComponents,
  TypeScriptSpec,
  TypeScriptFunction,
  TypeScriptParameter,
  Precondition,
  Postcondition,
  Invariant,
  
  // Traceability types
  TraceabilityLink,
  TraceabilityArtifact,
  ArtifactType,
  LinkType,
  
  // Hybrid verification types
  HybridVerificationResult,
} from './types.js';

// ============================================================================
// Errors
// ============================================================================
export {
  LeanError,
  LeanNotFoundError,
  LeanVersionError,
  LeanEnvironmentError,
  LeanConversionError,
  LeanVerificationError,
  LeanProofError,
  LeanIntegrationError,
  ReProverError,
  EarsConversionError,
  EarsParseError,
  TypeScriptSpecificationError,
  ProofTimeoutError,
  ProofGenerationError,
  ReProverConnectionError,
  LeanFileGenerationError,
  LeanExecutionError,
} from './errors.js';

// ============================================================================
// Environment
// ============================================================================
export {
  LeanEnvironmentDetector,
} from './environment/LeanEnvironmentDetector.js';

export {
  LeanProjectInitializer,
} from './environment/LeanProjectInitializer.js';

// ============================================================================
// Converters
// ============================================================================
export {
  EarsToLeanConverter,
} from './converters/EarsToLeanConverter.js';

export {
  TypeScriptSpecifier,
} from './converters/TypeScriptSpecifier.js';

// ============================================================================
// Proof Generation
// ============================================================================
export {
  ProofGenerator,
} from './proof/ProofGenerator.js';

export {
  ReProverClient,
} from './proof/ReProverClient.js';

// ============================================================================
// Infrastructure
// ============================================================================
export {
  LeanRunner,
} from './infrastructure/LeanRunner.js';

export {
  LeanFileGenerator,
} from './infrastructure/LeanFileGenerator.js';

// ============================================================================
// Reporting
// ============================================================================
export {
  VerificationReporter,
  type VerificationResultEntry,
  type VerificationStatus,
} from './reporting/VerificationReporter.js';

// ============================================================================
// Traceability
// ============================================================================
export {
  TraceabilityManager,
  type TraceabilityCoverage,
} from './traceability/TraceabilityManager.js';

// ============================================================================
// Hybrid Verification
// ============================================================================
export {
  HybridVerifier,
  type RuntimeTestResult,
  type FormalVerificationResult,
  type HybridCoverage,
  type VerificationStrategy,
} from './hybrid/HybridVerifier.js';

// ============================================================================
// Main Integration
// ============================================================================
export {
  LeanIntegration,
  createLeanIntegration,
  type IntegrationStatus,
  type VerificationOptions,
} from './integration/LeanIntegration.js';

// ============================================================================
// Default Export
// ============================================================================
export { LeanIntegration as default } from './integration/LeanIntegration.js';
