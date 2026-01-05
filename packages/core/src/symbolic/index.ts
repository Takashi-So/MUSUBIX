/**
 * Symbolic Module - Public API
 *
 * Neuro-symbolic AI integration capabilities:
 * - Semantic code filtering (LLM output validation)
 * - Hallucination detection (API/import verification)
 * - Constitution enforcement (9 articles validation)
 * - Confidence estimation and routing
 * - Error handling with graceful degradation
 *
 * @packageDocumentation
 * @module symbolic
 *
 * @see REQ-SYMB-001 - Symbolic Reasoning Requirements
 * @see DES-SYMB-001 - Symbolic Reasoning Design
 */

// === Types ===
export type {
  // Core types (re-exported from common)
  Confidence,
  // Symbolic-specific types
  Explanation,
  Evidence,
  ArtifactRef,
  SymbolInfo,
  EarsRequirement,
  ProjectContext,
  CodeCandidate,
  FilterInput,
  FilterOutput,
  HallucinationResult,
  HallucinationItem,
  ConstitutionArticle,
  ConstitutionRule,
  ConstitutionCheckInput,
  ConstitutionCheckContext,
  ConstitutionCheckResult,
  ConstitutionViolation,
  ConstitutionReport,
  ConfidenceEstimation,
  ConfidenceBreakdown,
  RiskFactor,
  RoutingDecision,
  RoutingResult,
  VerificationRequirement,
  ErrorHandlingStrategy,
  FallbackAction,
  AuditLogEntry,
} from './types.js';

// === Semantic Filter ===
export { SemanticCodeFilterPipeline, createSemanticCodeFilterPipeline } from './semantic-filter.js';
export type { SemanticCodeFilterConfig } from './semantic-filter.js';

// === Hallucination Detector ===
export {
  HallucinationDetector,
  ProjectSymbolIndex,
  createHallucinationDetector,
} from './hallucination-detector.js';
export type { HallucinationDetectorConfig } from './hallucination-detector.js';

// === Constitution Registry ===
export {
  ConstitutionRuleRegistry,
  createConstitutionRuleRegistry,
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
} from './constitution-registry.js';
export type { ConstitutionRegistryConfig } from './constitution-registry.js';

// === Confidence Estimator ===
export {
  ConfidenceEstimator,
  createConfidenceEstimator,
  DEFAULT_CONFIDENCE_CONFIG,
} from './confidence-estimator.js';
export type { ConfidenceEstimatorConfig } from './confidence-estimator.js';

// === Confidence Router ===
export {
  ConfidenceBasedRouter,
  createConfidenceBasedRouter,
  DEFAULT_ROUTER_CONFIG,
} from './confidence-router.js';
export type { ConfidenceRouterConfig, RoutingThresholds } from './confidence-router.js';

// === Error Handler ===
export {
  ErrorHandler,
  createErrorHandler,
  withErrorHandling,
  DEFAULT_ERROR_HANDLER_CONFIG,
} from './error-handler.js';
export type {
  ErrorHandlerConfig,
  ErrorSeverity,
  ErrorClassification,
  RecoveryResult,
} from './error-handler.js';

// === EARS to Formal Spec Converter (Phase 2) ===
export {
  EarsToFormalSpecConverter,
  createEarsToFormalSpecConverter,
  parseEarsRequirement,
  generateSmtLib,
  DEFAULT_EARS_TO_FORMAL_CONFIG,
} from './ears-to-formal.js';
export type {
  EarsPatternType,
  EarsAstNode,
  SmtLibOutput,
  SmtVariable,
  SmtAssertion,
  FormalSpecification,
  EarsToFormalConfig,
} from './ears-to-formal.js';

// === Verification Condition Generator (Phase 2) ===
export {
  VerificationConditionGenerator,
  createVerificationConditionGenerator,
  resetVcCounter,
  DEFAULT_VC_GENERATOR_CONFIG,
} from './vc-generator.js';
export type {
  VcType,
  VcStatus,
  CodeElementRef,
  VerificationCondition,
  VcGenerationResult,
  DomainConstraint,
  FunctionContract,
  VcGeneratorConfig,
} from './vc-generator.js';

// === Z3 Adapter (Phase 2) ===
export {
  Z3Adapter,
  createZ3Adapter,
  PreconditionVerifier,
  PostconditionVerifier,
  InvariantVerifier,
  createPreconditionVerifier,
  createPostconditionVerifier,
  createInvariantVerifier,
  DEFAULT_Z3_CONFIG,
} from './z3-adapter.js';
export type {
  Z3Verdict,
  Z3Result,
  VcVerificationResult,
  FormalVerificationResult,
  Z3AdapterConfig,
} from './z3-adapter.js';

// === Security Scanner (Phase 2) ===
export {
  SecurityScanner,
  SecuritySandbox,
  SECRET_PATTERNS,
  OWASP_PATTERNS,
  DEFAULT_SECURITY_SCANNER_CONFIG,
} from './security-scanner.js';
export type {
  SecretType,
  OwaspCategory,
  SecuritySeverity,
  DetectedSecret,
  OwaspFinding,
  SecurityScanResult,
  RedactionPolicy,
  RedactionOptions,
  SecurityScannerConfig,
  SecurityEventType,
  SecurityEvent,
  SecurityAuditEntry,
} from './security-scanner.js';

// === Candidate Ranker (Phase 3) ===
export {
  CandidateRanker,
  createCandidateRanker,
  calculateScore,
  DEFAULT_RANKER_CONFIG,
} from './candidate-ranker.js';
export type {
  CandidateMetrics,
  ScoreBreakdown,
  RankedCandidate,
  CandidateRankingResult,
  CandidateInput,
  CandidateRankerConfig,
} from './candidate-ranker.js';

// === Result Blender (Phase 3) ===
export {
  ResultBlender,
  createResultBlender,
  blendResults,
  DEFAULT_BLENDER_CONFIG,
} from './result-blender.js';
export type {
  BlendStrategy,
  SymbolicVerdict,
  NeuralResult,
  SymbolicResult,
  ConfidenceEstimate,
  Attribution,
  BlendedResult,
  ResultBlenderConfig,
} from './result-blender.js';

// === Rule Config (Phase 3) ===
export {
  ExtensibleRuleConfig,
  createRuleConfig,
  loadRuleConfig,
  DEFAULT_CONFIG_PATHS,
} from './rule-config.js';
export type {
  RuleSeverity,
  CodeLanguage,
  ConstitutionEnforcement,
  ConstitutionStage,
  SemanticFilterRuleConfig,
  ConstitutionRuleConfig,
  RuleConfigBundle,
  ArtifactRef as RuleArtifactRef,
  ConfigLoadResult,
  ConfigValidationError,
  RuleConfigLoaderOptions,
} from './rule-config.js';

// === Audit Logger (Phase 3) ===
export {
  AuditLogger,
  createAuditLogger,
  getDefaultAuditLogger,
  auditLog,
  DEFAULT_AUDIT_CONFIG,
} from './audit-logger.js';
export type {
  AuditEventType,
  AuditResult,
  AuditLogEntry as AuditLogEntryFull,
  Checkpoint,
  IntegrityVerificationResult,
  ArchiveResult,
  AuditLoggerConfig,
} from './audit-logger.js';

// === Performance Budget (Phase 3) ===
export {
  PerformanceBudget,
  createPerformanceBudget,
  withBudget,
  DEFAULT_BUDGET_CONFIG,
} from './performance-budget.js';
export type {
  BudgetStep,
  TimeoutKind,
  TimeoutInfo,
  StepMeasurement,
  PerformanceMeasurement,
  PartialResultMetadata,
  PerformanceBudgetConfig,
  SloMetrics,
} from './performance-budget.js';

// === Quality Gate (Phase 3 - TSK-SYMB-019) ===
export {
  QualityGateValidator,
  createComponentValidation,
} from './quality-gate.js';
export type {
  QualityCheckResult,
  QualityGateResult,
  TraceabilityCoverage,
  QualityGateConfig,
  ComponentValidation,
} from './quality-gate.js';

// === Convenience Functions ===

import { SemanticCodeFilterPipeline } from './semantic-filter.js';
import { HallucinationDetector } from './hallucination-detector.js';
import { ConstitutionRuleRegistry, DEFAULT_CONSTITUTION_RULES } from './constitution-registry.js';
import { ConfidenceEstimator } from './confidence-estimator.js';
import { ConfidenceBasedRouter } from './confidence-router.js';
import { ErrorHandler } from './error-handler.js';
import type { FilterInput, FilterOutput, RoutingResult } from './types.js';

/**
 * Create a complete symbolic reasoning pipeline with all components
 */
export function createSymbolicPipeline(): {
  filter: SemanticCodeFilterPipeline;
  hallucinationDetector: HallucinationDetector;
  constitutionRegistry: ConstitutionRuleRegistry;
  confidenceEstimator: ConfidenceEstimator;
  router: ConfidenceBasedRouter;
  errorHandler: ErrorHandler;
} {
  const hallucinationDetector = new HallucinationDetector();
  const constitutionRegistry = new ConstitutionRuleRegistry({
    rules: DEFAULT_CONSTITUTION_RULES,
  });
  const filter = new SemanticCodeFilterPipeline({
    hallucinationDetector,
    constitutionRegistry,
  });
  const confidenceEstimator = new ConfidenceEstimator();
  const router = new ConfidenceBasedRouter();
  const errorHandler = new ErrorHandler();

  return {
    filter,
    hallucinationDetector,
    constitutionRegistry,
    confidenceEstimator,
    router,
    errorHandler,
  };
}

/**
 * Process code through the complete symbolic pipeline
 */
export async function processSymbolic(
  input: FilterInput,
): Promise<{ filterOutput: FilterOutput; routingResults: RoutingResult[] }> {
  const { filter, confidenceEstimator, router } = createSymbolicPipeline();

  const filterOutput = await filter.filter(input);

  const routingResults: RoutingResult[] = [];
  for (const candidate of input.candidates) {
    const hallucinationCount = filterOutput.hallucinationReport?.items.length ?? 0;
    const estimation = await confidenceEstimator.estimate(
      candidate,
      input.projectContext,
      hallucinationCount,
    );
    const routingResult = router.route(estimation, filterOutput);
    routingResults.push(routingResult);
  }

  return { filterOutput, routingResults };
}
