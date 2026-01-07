/**
 * @fileoverview MUSUBIX Security Package - Main Entry Point
 * @module @nahisaho/musubix-security
 * @version 1.8.0
 * 
 * Static analysis and vulnerability detection for TypeScript/JavaScript applications.
 * 
 * Features:
 * - Vulnerability scanning (SQL Injection, XSS, Command Injection, etc.)
 * - Taint analysis (data flow tracking)
 * - Secret detection (API keys, passwords, tokens)
 * - Dependency auditing (npm audit integration)
 * - Fix generation and verification
 * - Multiple report formats (JSON, SARIF, Markdown, HTML)
 * 
 * @example
 * ```typescript
 * import { runSecurityScan, createSecurityService } from '@nahisaho/musubix-security';
 * 
 * // Quick scan
 * const result = await runSecurityScan('./src');
 * console.log(`Found ${result.summary.totalVulnerabilities} vulnerabilities`);
 * 
 * // Full service usage
 * const service = createSecurityService();
 * const scanResult = await service.scan({
 *   target: './src',
 *   vulnerabilities: true,
 *   taint: true,
 *   secrets: true,
 *   dependencies: true,
 *   generateFixes: true,
 * });
 * ```
 */

// ============================================================================
// Types
// ============================================================================

export {
  // Vulnerability types
  type Vulnerability,
  type SourceLocation,
  type ScanResult,
  type SecurityRule,
  type Severity,
  type OWASPCategory,
  
  // Taint analysis types
  type TaintSource,
  type TaintSink,
  type TaintPath,
  type TaintResult,
  type SanitizerDefinition,
  BUILTIN_SANITIZERS,
  
  // Fix types
  type Fix,
  type CodeEdit,
  type ImportEdit,
  type VerificationResult,
  type VerificationStatus,
  type ApplyResult,
  type FixBatch,
  type FixStrategy,
  
  // Secret types
  type Secret,
  type SecretPattern,
  type SecretScanResult,
  BUILTIN_SECRET_PATTERNS,
  
  // Dependency types
  type AuditResult,
  type VulnerableDependency,
  type DependencyVulnerability,
  type SBOM,
  type SBOMEntry,
  type LicensePolicy,
  
  // Config types
  type SecurityConfig,
  type ReportConfig,
  type CacheConfig,
  type CIConfig,
  DEFAULT_CONFIG,
} from './types/index.js';

// ============================================================================
// Analysis
// ============================================================================

export {
  VulnerabilityScanner,
  TaintAnalyzer,
  SecretDetector,
  DependencyAuditor,
} from './analysis/index.js';

// ============================================================================
// Infrastructure
// ============================================================================

export {
  ASTParser,
  FileScanner,
  loadConfig,
  loadConfigSync,
  MemoryCache,
  FileCache,
  NoopCache,
  cacheKey,
  contentHash,
  type ICache,
} from './infrastructure/index.js';

// ============================================================================
// Core (v2.0)
// ============================================================================

export {
  // Pipeline Manager
  PipelineManager,
  createPipelineManager,
  createStandardPipeline,
  
  // Result Aggregator
  ResultAggregator,
  createResultAggregator,
  mergeSimilarByLocation,
} from './core/index.js';

// ============================================================================
// Phase 2 Analyzers (v2.0)
// ============================================================================

// Container Security
export {
  ImageScanner,
  createImageScanner,
  type ImageScanOptions,
  type ImageScanResult,
  type DockerfileAnalysis,
  type DockerfileIssue,
  type BestPracticeViolation,
  type ContainerVulnerability,
} from './analyzers/container/image-scanner.js';

// Infrastructure as Code Security
export {
  IaCChecker,
  createIaCChecker,
  type IaCCheckOptions,
  type IaCAnalysisResult,
  type IaCIssue,
  type IaCType,
} from './analyzers/iac/iac-checker.js';

// AI Security
export {
  PromptInjectionDetector,
  createPromptInjectionDetector,
  type PromptInjectionOptions,
  type PromptInjectionResult,
  type PromptInjectionVulnerability,
} from './analyzers/ai/prompt-injection-detector.js';

// SAST - Zero Day Detection
export {
  ZeroDayDetector,
  createZeroDayDetector,
  type ZeroDayOptions,
  type ZeroDayResult,
  type ZeroDayVulnerability,
} from './analyzers/sast/zero-day-detector.js';

// SAST - Interprocedural Analysis
export {
  InterproceduralAnalyzer,
  createInterproceduralAnalyzer,
  type InterproceduralOptions,
  type InterproceduralResult,
  type CallGraphNode,
  type DataFlowPath,
} from './analyzers/sast/interprocedural-analyzer.js';

// ============================================================================
// Phase 3 Analyzers (v2.0)
// ============================================================================

// Compliance Checker
export {
  ComplianceChecker,
  createComplianceChecker,
  type ComplianceStandard,
  type ComplianceRequirement,
  type ComplianceCheckResult,
  type ComplianceFinding,
  type ComplianceReport,
  type ComplianceSummary,
  type ComplianceCheckerOptions,
} from './analyzers/compliance/compliance-checker.js';

// Dependency Scanner (SCA)
export {
  DependencyScanner,
  createDependencyScanner,
  type DependencyScannerOptions,
  type DependencyInfo,
  type DependencyScanResult,
  type LicenseRisk,
  type SBOMComponent,
  type SBOMDocument,
  type OutdatedPackage,
  type DependencySummary,
} from './analyzers/sca/dependency-scanner.js';

// API Security Analyzer
export {
  APISecurityAnalyzer,
  createAPISecurityAnalyzer,
  type APISecurityOptions,
  type APISecurityResult,
  type APISecurityIssue,
  type APISecurityCategory,
  type APIEndpoint,
  type OpenAPISpec,
  type SecurityCoverage,
  type APISecuritySummary,
} from './analyzers/api/api-security-analyzer.js';

// Realtime Monitor
export {
  RealtimeMonitor,
  createRealtimeMonitor,
  createSecurityMonitor,
  type MonitorConfig,
  type MonitorEvent,
  type MonitorEventType,
  type MonitorState,
  type ScannerFunction,
} from './analyzers/monitor/realtime-monitor.js';

// Security Dashboard
export {
  SecurityDashboard,
  createSecurityDashboard,
  type DashboardConfig,
  type DashboardReport,
  type SecurityMetrics,
  type SecurityTrend,
  type SecurityRecommendation,
  type ExecutiveSummary,
  type TopVulnerability,
  type ComponentRisk,
} from './analyzers/dashboard/security-dashboard.js';

// ============================================================================
// Intelligence (v2.0 - Neuro-Symbolic)
// ============================================================================

export {
  NeuroSymbolicCore,
  createNeuroSymbolicCore,
  StubLLMAnalyzer,
  StubKnowledgeQuery,
} from './intelligence/index.js';

// ============================================================================
// Services
// ============================================================================

export {
  // Main service
  SecurityService,
  createSecurityService,
  scanForVulnerabilities,
  runSecurityScan,
  type ScanOptions,
  type CompleteScanResult,
  
  // Fix services
  FixGenerator,
  createFixGenerator,
  FixVerifier,
  createFixVerifier,
  type VerificationOptions,
  
  // Report services
  ReportGenerator,
  createReportGenerator,
  type ReportFormat,
  type CombinedResults,
  type ReportMetadata,
} from './services/index.js';

// ============================================================================
// CLI
// ============================================================================

export { createSecurityCLI, runCLI } from './cli/index.js';

// ============================================================================
// MCP
// ============================================================================

export {
  SecurityMCPServer,
  startMCPServer,
  runMCPServer,
  SecurityToolHandler,
  createToolHandler,
  getToolSchemas,
  SECURITY_TOOLS,
  type ToolSchema,
  type ToolResult,
} from './mcp/index.js';

// ============================================================================
// Phase 4: Integrations (v2.0)
// ============================================================================

export {
  // CI/CD Integration
  CIIntegration,
  createCIIntegration,
  isCI,
  detectCIPlatform,
  type CIPlatform,
  type CIEnvironment,
  type CIIntegrationOptions,
  type CIScanResult,
  type GitHubAnnotation,
  type CISummary,
  
  // Report Aggregator
  ReportAggregator,
  createReportAggregator,
  type AggregatedReport,
  type AggregatedFinding,
  type TrendData,
  type ReportComparison,
  type ReportAggregatorOptions,
  
  // Git Hooks
  GitHooksManager,
  createGitHooks,
  installPreCommitHook,
  installRecommendedHooks,
  type HookType,
  type GitHooksConfig,
  type HookResult,
  type InstallResult,
  
  // VS Code Integration
  VSCodeIntegration,
  createVSCodeIntegration,
  DiagnosticSeverity,
  type VSCodeIntegrationOptions,
  type Diagnostic,
  type CodeAction,
  type TreeItem,
  type HoverContent,
  type StatusBarItem,
  type Decoration,
} from './integrations/index.js';

// ============================================================================
// Phase 4: Policy Engine (v2.0)
// ============================================================================

export {
  PolicyEngine,
  createPolicyEngine,
  getBuiltInPolicy,
  type SecurityPolicy,
  type PolicyRule,
  type PolicyCondition,
  type PolicyEvaluationResult,
  type PolicyEngineOptions,
  type PolicyAction,
} from './policy/index.js';

// ============================================================================
// Phase 5: Remediation (v2.0)
// ============================================================================

export {
  // Auto-Fixer
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
  
  // Fix Validator
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
  
  // Patch Generator
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
  
  // Remediation Planner
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
  
  // Secure Code Transformer
  SecureCodeTransformer,
  createSecureCodeTransformer,
  quickTransform,
  getBuiltInTransformations,
  type TransformationDefinition,
  type TransformationCategory,
  type CodePattern,
  type PatternContext,
  type ReplacementPattern,
  type TransformImportSpec,
  type TransformationResult,
  type AppliedTransformation,
  type SecureCodeTransformerOptions,
  type TransformOptions,
} from './remediation/index.js';
