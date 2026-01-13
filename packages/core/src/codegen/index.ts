/**
 * Code Generation Module
 * 
 * Exports all code generation, testing, and quality analysis components
 * 
 * @packageDocumentation
 * @module codegen
 */

// Code Generator
export {
  CodeGenerator,
  createCodeGenerator,
  type TargetLanguage,
  type TemplateType,
  type CodeStructureDefinition,
  type PropertyDefinition,
  type MethodDefinition,
  type GeneratedCode,
  type CodeGeneratorOptions,
} from './generator.js';

// Static Analyzer
export {
  StaticAnalyzer,
  createStaticAnalyzer,
  type IssueSeverity,
  type IssueCategory,
  type AnalysisRule,
  type AnalysisResult,
  type StaticAnalyzerConfig,
} from './static-analyzer.js';

// Quality Metrics Calculator
export {
  QualityMetricsCalculator,
  createQualityMetricsCalculator,
  type MetricType,
  type FileMetrics,
  type FunctionMetrics,
  type ClassMetrics,
  type ProjectMetrics,
  type QualityMetricsConfig,
} from './quality-metrics.js';

// Security Scanner
export {
  SecurityScanner,
  createSecurityScanner,
  type VulnerabilitySeverity,
  type VulnerabilityCategory,
  type SecurityVulnerability,
  type SecurityScanResult,
  type SecurityRule,
  type SecurityScannerConfig,
} from './security-scanner.js';

// Pattern Conformance Checker
export {
  PatternConformanceChecker,
  createPatternConformanceChecker,
  type ConformanceLevel,
  type PatternConformanceResult,
  type ConformanceElement,
  type ConformanceViolation,
  type PatternSpecification,
  type ParticipantSpec,
  type RelationshipSpec,
  type PatternConformanceConfig,
} from './pattern-conformance.js';

// Dependency Analyzer
export {
  DependencyAnalyzer,
  createDependencyAnalyzer,
  type DependencyType,
  type DependencyStrength,
  type ModuleType,
  type DependencyInfo,
  type ModuleInfo,
  type ExportInfo,
  type DependencyGraph,
  type DependencyAnalysisResult,
  type DependencyMetrics,
  type DependencyIssue,
  type DependencyAnalyzerConfig,
} from './dependency-analyzer.js';

// Unit Test Generator
export {
  UnitTestGenerator,
  createUnitTestGenerator,
  EarsTestGenerator,
  createEarsTestGenerator,
  type TestFramework,
  type AssertionStyle,
  type TestTargetType,
  type TestCaseInfo,
  type TestInput,
  type TestOutput,
  type TestMock,
  type TestSuiteInfo,
  type FunctionToTest,
  type GeneratedTestResult,
  type UnitTestGeneratorConfig,
  type EarsRequirement,
  type EarsTestCase,
} from './unit-test-generator.js';

// Integration Test Generator
export {
  IntegrationTestGenerator,
  createIntegrationTestGenerator,
  type IntegrationTestType,
  type TestFixture,
  type IntegrationTestScenario,
  type TestStep,
  type ExpectedOutcome,
  type ApiEndpointInfo,
  type ServiceInteractionInfo,
  type IntegrationTestSuite,
  type GeneratedIntegrationTest,
  type IntegrationTestGeneratorConfig,
} from './integration-test-generator.js';

// Coverage Reporter
export {
  CoverageReporter,
  createCoverageReporter,
  type CoverageMetricType,
  type ThresholdStatus,
  type FileCoverage,
  type CoverageMetric,
  type BranchInfo,
  type CoverageSummary,
  type CoverageThreshold,
  type CoverageReport,
  type ThresholdResult,
  type CoverageTrend,
  type ReportFormat,
  type CoverageReporterConfig,
} from './coverage-reporter.js';

// Mock Generator (v1.1.4 - PAT-004 self-learning improvement)
export {
  MockGenerator,
  createMockGenerator,
  mockGenerator,
  type GeneratedMock,
  type MockGeneratorOptions,
  type MockInterfaceDefinition,
  type MockMethodDefinition,
} from './mock-generator.js';

// Base Repository (v1.1.4 - PAT-005 self-learning improvement)
export {
  InMemoryRepository,
  SearchableInMemoryRepository,
  type IRepository,
  type ISearchableRepository,
  type IPaginatedRepository,
  type PaginationOptions,
  type PaginatedResult,
} from './base-repository.js';

// Adapter Naming Helper (v1.1.4 - PAT-006 self-learning improvement)
export {
  AdapterNamingHelper,
  createAdapterNamingHelper,
  adapterNamingHelper,
  ADAPTER_TEMPLATES,
  type AdapterType,
  type AdapterNamingRule,
} from './adapter-naming.js';

// Enhanced Code Generator (v1.7.0 NEW!)
// @see REQ-YI-GEN-001, REQ-YI-GEN-002, REQ-YI-GEN-003
export {
  EnhancedCodeGenerator,
  createEnhancedCodeGenerator,
  DEFAULT_CODEGEN_CONFIG,
  type CodeGenConfig,
  type GeneratedFile,
  type TraceabilityEntry,
  type GenerationResult,
  type C4Component,
  type C4Design,
  // EARSRequirement is exported from types with different structure
} from './enhanced-generator.js';
export type { EARSRequirement as EnhancedEARSRequirement } from './enhanced-generator.js';

// Test File Decorator (v3.1.0 NEW!)
// @see REQ-TST-002, TSK-TST-002
export {
  TestFileDecorator,
  decorateTestFile,
  needsCounterReset,
  type CounterResetFunction,
  type TestFileDecoratorOptions,
  type DecorationResult,
} from './test-file-decorator.js';

// Value Object Generator (v3.1.0 NEW!)
// @see REQ-VO-001, TSK-GEN-001
export {
  ValueObjectGenerator,
  generateValueObject,
  parseVOSpec,
  type ValueObjectSpec,
  type VOProperty,
  type VOValidation,
  type VOGeneratorOptions,
  type VOGenerationResult,
} from './value-object-generator.js';

// Status Transition Generator (v3.1.0 NEW!)
// @see BP-DESIGN-001, TSK-GEN-002
export {
  StatusTransitionGenerator,
  generateStatusTransitions,
  parseStatusMachineSpec,
  type StatusTransition as StatusTransitionSpec, // Renamed to avoid conflict with utils
  type StatusDefinition,
  type StatusMachineSpec,
  type StatusGeneratorOptions,
  type StatusGenerationResult,
} from './status-transition-generator.js';

// Status Transition Test Generator (v3.1.0 NEW!)
// @see BP-TEST-005, TSK-TST-001
export {
  StatusTransitionTestGenerator,
  generateStatusTransitionTests,
  type StatusTestGeneratorOptions,
  type StatusTestGenerationResult,
} from './status-transition-test-generator.js';
