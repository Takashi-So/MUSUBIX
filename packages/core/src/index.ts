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
export { 
  VERSION, 
  collectDependencyVersions, 
  checkVersionMismatch, 
  formatVerboseVersion,
} from './version.js';
export type { DependencyVersions, VersionMismatchResult } from './version.js';

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

// Export requirements (context clarification, decomposition)
export * from './requirements/index.js';

// Export error recovery
// Note: ErrorCode, ErrorSeverity are already exported from ./types/index.js
// so we use selective re-exports to avoid conflicts
export {
  GracefulDegradation,
  createGracefulDegradation,
  retryWithBackoff,
  CircuitBreaker,
  MemoryCacheProvider,
  MemoryQueueProvider,
  DEFAULT_DEGRADATION_CONFIG,
  DataPersistence,
  createDataPersistence,
  WriteAheadLog,
  MemoryStorageAdapter,
  FileStorageAdapter,
  DEFAULT_PERSISTENCE_CONFIG,
  ActionableError,
  ErrorFormatter,
  ErrorCodes,
  CommonErrors,
} from './error/index.js';
export type {
  DegradationLevel,
  ServiceStatus,
  FallbackStrategy,
  HealthCheckResult,
  ServiceConfig,
  // FallbackAction - exported from symbolic/index.js
  DegradationEvent,
  DegradedResult,
  GracefulDegradationConfig,
  CacheProvider,
  QueueProvider,
  StorageBackend,
  DataState,
  Checkpoint,
  Transaction,
  TransactionOperation,
  // RecoveryResult - exported from symbolic/index.js
  PersistenceStatistics,
  DataPersistenceConfig,
  StorageAdapter,
  ErrorSuggestion,
  ErrorContext,
  ActionableErrorOptions,
} from './error/index.js';

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

// Export testing utilities (REQ-E2E-v1.5.2)
export * from './testing/index.js';

// Export performance utilities (REQ-PERF-v1.5.1)
// Note: Some types (CacheOptions, CacheStats, LRUCache, memoize, memoizeAsync) are already
// exported from ./learning/index.js, so we use selective re-exports to avoid conflicts
export {
  LazyNotLoadedError,
  lazyImport,
  lazyLoad,
  ensureLoaded,
  isLoaded,
  preloadModules,
  clearModuleCache,
  getModuleCacheStats,
  createLazyModule,
  MemoryMonitor,
  getMemoryMonitor,
  formatBytes,
  formatMemoryStats,
  formatMemoryReport,
  measureMemory,
  isMemoryHigh,
  getMemoryUsagePercent,
  parallelMap,
  parallelFilter,
  parallelRace,
  parallelSettle,
  chunk,
  batchProcess,
  ParallelExecutor,
  throttle,
  debounce,
  benchmark,
  benchmarkSuite,
  measure,
  time,
  formatBenchmarkResult,
  formatBenchmarkSuiteResult,
  runStandardBenchmarks,
} from './perf/index.js';
export type { MemoryStats, MemoryReport, ParallelOptions, BenchmarkResult, BenchmarkSuiteResult, BenchmarkOptions } from './perf/index.js';

// Pipeline Configuration (v2.2.0 NEW!)
export type {
  PipelineConfig,
  PipelineStage,
  PipelineInput,
  PipelineOutput,
  PipelineExecutionResult,
  PipelineConfigOptions,
  PipelineConfigJSON,
  ParallelGroup,
} from './pipeline/PipelineConfig.js';
export { createPipelineConfig, DefaultPipelineConfig } from './pipeline/PipelineConfig.js';

// Synthesis Orchestrator (v2.2.0 NEW!)
export type {
  SynthesisOrchestrator,
  OrchestratorConfig,
  PipelinePreset,
  SynthesisRequest,
  SynthesisResponse,
  SynthesisTiming,
  SynthesisStatus,
  OrchestratorStatistics,
  IOExample,
  LibraryPattern,
} from './synthesis/index.js';
export { createSynthesisOrchestrator, DefaultSynthesisOrchestrator } from './synthesis/index.js';

// Watch Module (v3.1.0 NEW!)
export {
  FileWatcher,
  TaskScheduler,
  ResultReporter,
  LintRunner,
  TestRunner,
  SecurityRunner,
  EARSRunner,
  createWatchCommand,
  createLintRunner,
  createTestRunner,
  createSecurityRunner,
  createEARSRunner,
} from './watch/index.js';
export type {
  WatchConfig,
  FileChangeEvent,
  ScheduledTask,
  TaskResult,
  TaskType,
  ReportConfig,
  WatchReport,
  TaskRunner,
  Issue,
} from './watch/index.js';

// CodeQL Module (v3.1.0 NEW!)
export {
  SARIFParser,
  ResultAggregator,
  createSARIFParser,
  createResultAggregator,
  parseSARIFFile,
  parseSARIF,
  mapCWE,
  getAllCWEs,
  getCWEsByCategory,
  getCWEsBySeverity,
  extractCWEIds,
  isCWEKnown,
  getCWESeverity,
  getCWEExplanation,
  CWE_CATEGORIES,
} from './codeql/index.js';
export type {
  SARIFLog,
  SARIFRun,
  SARIFResult,
  SARIFRule,
  CodeQLFinding,
  CodeQLScanResult,
  CodeFlowStep,
  CWEInfo,
  CWECategory,
  SARIFParserConfig,
  AggregatedReport,
  AggregatorConfig,
} from './codeql/index.js';

// Team Module (v3.1.0 NEW!)
export {
  GitClient,
  PatternSharer,
  TeamKnowledge,
  createPatternSharer,
  createTeamKnowledge,
} from './team/index.js';
export type {
  TeamMember,
  TeamConfig,
  SharedPattern,
  TeamKnowledgeEntry,
  SyncStatus,
  GitResult,
  CommitInfo,
  BranchInfo,
  FileStatus,
  PullResult,
  PushResult,
  PatternSharerConfig,
  TeamKnowledgeConfig,
  KnowledgeQueryOptions,
  KnowledgeStats,
} from './team/index.js';

// Spaces Module (v3.1.0 NEW!)
export {
  ContextManager,
  SpaceStorage,
  SpaceContext_,
  createContextManager,
  createSpaceStorage,
  createSpaceContext,
} from './spaces/index.js';
export type {
  Space,
  SpaceType,
  SpaceContext,
  SpaceSettings,
  SpaceActivationResult,
  CreateSpaceInput,
  UpdateSpaceInput,
  ContextQuery,
  ContextSuggestion,
  SpaceStats,
  SpaceWatchSettings,
  SpaceCodeQLSettings,
  ContextManagerConfig,
  SpaceStorageConfig,
  SpaceContextConfig,
} from './spaces/index.js';

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

