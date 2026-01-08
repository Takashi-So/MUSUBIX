/**
 * @fileoverview Type definitions entry point
 * @module @nahisaho/musubix-security/types
 */

// Vulnerability types
export type {
  OWASPCategory,
  VulnerabilityType,
  Severity,
  SourceLocation,
  Vulnerability,
  ScanOptions,
  ScanResult,
  SecurityRule,
} from './vulnerability.js';

// Taint analysis types
export type {
  TaintSourceCategory,
  TaintSource,
  TaintSinkCategory,
  TaintSink,
  TaintFlowStep,
  TaintPath,
  TaintResult,
  TaintAnalysisOptions,
  SanitizerDefinition,
} from './taint.js';

export { BUILTIN_SANITIZERS } from './taint.js';

// Fix types
export type {
  FixStrategy,
  CodeEdit,
  ImportEdit,
  Fix,
  FixGenerationOptions,
  VerificationStatus,
  VerificationResult,
  ApplyStatus,
  ApplyResult,
  FixBatch,
  FixTemplate,
} from './fix.js';

// Secret types
export type {
  SecretType,
  SecretContext,
  Secret,
  SecretPattern,
  SecretScanOptions,
  SecretScanResult,
  SecretVerification,
} from './secret.js';

export { BUILTIN_SECRET_PATTERNS } from './secret.js';

// Dependency types
export type {
  DependencyType,
  VulnerabilitySource,
  VulnerableDependency,
  DependencyVulnerability,
  UpgradeSuggestion,
  AuditResult,
  AuditOptions,
  SBOMEntry,
  SBOM,
  SBOMOptions,
  LicenseCheckResult,
  LicensePolicy,
} from './dependency.js';

// Config types
export type {
  ReportFormat,
  KnowledgeGraphMode,
  CacheStrategy,
  ReportConfig,
  KnowledgeGraphConfig,
  AIConfig,
  CacheConfig,
  CIConfig,
  SecurityConfig,
} from './config.js';

export {
  DEFAULT_CONFIG,
  CONFIG_FILE_LOCATIONS,
  ENV_PREFIX,
  CONFIG_SCHEMA_VERSION,
} from './config.js';

// Pipeline types (v2.0)
export type {
  StageId,
  StageStatus,
  AnalyzerType,
  PipelineStage,
  PipelineConfig,
  ProgressCallback,
  PipelineProgress,
  StageResult,
  PipelineResult,
  IPipelineManager,
  Pipeline,
  AnalyzerFactory,
  AnalyzerInstance,
} from './pipeline.js';

// Neuro-Symbolic types (v2.0)
export type {
  EvidenceType,
  Evidence,
  NeuralResult,
  SymbolicResult,
  KnowledgeGraphMatch,
  FinalDecision,
  NeuroSymbolicResult,
  IntegrationOptions,
  INeuroSymbolicCore,
  ILLMAnalyzer,
  IKnowledgeQuery,
} from './neuro-symbolic.js';

// Zero-day detection types (v2.0)
export type {
  DeviationType,
  LLMRecommendation,
  LLMAnalysisResult,
  RiskFactor,
  RiskAssessment,
  ZeroDayCandidate,
  ZeroDayDetectionOptions,
  ZeroDayResult,
  IZeroDayDetector,
} from './zero-day.js';

// Interprocedural analysis types (v2.0)
export type {
  DataFlowOperation,
  ParameterInfo,
  CallGraphNode,
  ArgumentMapping,
  CallGraphEdge,
  CallGraph,
  CycleInfo,
  DataFlowStep,
  DataFlowPath,
  InterproceduralOptions,
  InterproceduralResult,
  IInterproceduralAnalyzer,
} from './interprocedural.js';

// Result aggregation types (v2.0)
export type {
  DetectionSource,
  AggregatedVulnerability,
  AnalysisResult,
  AggregatedResult,
  DeduplicationRule,
  PrioritizationCriteria,
  IResultAggregator,
} from './result.js';

export {
  DEFAULT_PRIORITIZATION,
  SEVERITY_SCORES,
} from './result.js';

// CVE types (v2.1.0)
export type {
  CVSSScore,
  CVSSSeverity,
  CVEStatus,
  CVEReference,
  CPEMatch,
  CVE,
  CVEFinding,
  CVESearchQuery,
  CVESyncResult,
  CVEDatabaseOptions,
  NpmCPEMapping,
  NVDVulnerability,
  NVDAPIResponse,
} from './cve.js';

// Security rule types (v2.1.0)
export type {
  RuleCategory,
  OWASPTopTenCategory,
  ASTPattern,
  ASTPatternMatcher,
  ASTPatternAnyOf,
  ASTPatternAllOf,
  PatternConstraint,
  RuleFixTemplate,
  RuleFixImport,
  SecurityRuleDefinition,
  RuleMatch,
  RuleMatchContext,
  RuleFilter,
  RuleSetConfig,
  BuiltinRuleSet,
  RuleMatchOptions,
  RuleYAMLEntry,
  RuleYAMLFile,
} from './rule.js';
