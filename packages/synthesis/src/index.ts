/**
 * MUSUBIX Synthesis
 * @module @nahisaho/musubix-synthesis
 * @description Program synthesis with DSL and PBE
 */

// Types
export * from './types.js';

// Errors
export * from './errors.js';

// DSL
export {
  DSLBuilder,
  DSL,
  TypeSystem,
  createDSLExtender,
} from './dsl/index.js';
export type {
  DSLExtender,
  DSLExtenderConfig,
  DSLGap,
  OperatorSuggestion,
  OperatorValidationResult,
  Example as DSLExample,
} from './dsl/index.js';

// Synthesis
export {
  Enumerator,
  PBESynthesizer,
  WitnessEngine,
  VersionSpace,
} from './synthesis/index.js';

// Rules
export {
  RuleExtractor,
  RuleLibrary,
  MetaLearner,
  resetRuleIdCounter,
} from './rules/index.js';

// Witness (v2.2.0 NEW!)
export {
  EnhancedWitnessEngine,
  createEnhancedWitnessEngine,
  BUILTIN_WITNESSES,
} from './witness/index.js';
export type {
  EnhancedWitnessConfig,
  WitnessCategory,
  ExtendedWitnessFunction,
  WitnessListItem,
} from './witness/index.js';

// Version Space (v2.2.0 NEW!)
export {
  createEnhancedVersionSpace,
  DefaultEnhancedVersionSpace,
} from './versionspace/index.js';
export type {
  EnhancedVersionSpace,
  VersionSpaceConfig,
  VersionSpacePoint,
  VersionSpaceStatistics,
  MergeStrategy,
  Example,
} from './versionspace/index.js';

// Enhanced PBE Synthesizer (v2.2.0 NEW!)
export {
  createEnhancedPBESynthesizer,
  DefaultEnhancedPBESynthesizer,
} from './EnhancedPBESynthesizer.js';
export type {
  EnhancedPBESynthesizer,
  EnhancedPBESynthesizerConfig,
  SynthesisRequest,
  TypedSynthesisRequest,
  SynthesisResponse,
  CustomWitness,
  SearchStats,
  SynthesisHistoryEntry,
  EnhancedSynthesisStats,
} from './EnhancedPBESynthesizer.js';

// Meta Learning (v2.2.0 NEW!)
export {
  createMetaLearningEngine,
} from './meta/index.js';
export type {
  MetaLearningEngine,
  MetaLearningConfig,
  MetaLearningStatistics,
  TaskFeatures,
  SynthesisStrategy,
  SynthesisTask,
  RecordedTask,
  SimilarTaskResult,
} from './meta/index.js';

// Analysis (v2.2.0 NEW!)
export {
  createExampleAnalyzer,
} from './analysis/index.js';
export type {
  ExampleAnalyzer,
  ExampleAnalyzerConfig,
  ExampleQuality,
  Ambiguity,
  ExampleSuggestion,
  ExampleCoverage,
  Example as AnalysisExample,
} from './analysis/index.js';

// Explanation (v2.2.0 NEW!)
export {
  createExplanationGenerator,
} from './explain/index.js';
export type {
  ExplanationGenerator,
  SynthesizedProgram,
  Explanation,
  DetailedExplanation,
  Example as ExplanationExample,
  ExampleWalkthrough,
} from './explain/index.js';
