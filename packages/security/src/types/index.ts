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
