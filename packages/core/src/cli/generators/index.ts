/**
 * CLI Generators
 *
 * Exports all code generation utilities for scaffold commands
 *
 * @packageDocumentation
 * @module cli/generators
 */

export {
  ValueObjectGenerator,
  createValueObjectGenerator,
  type ValueObjectSpec,
  type ValueObjectField,
  type ValueObjectGeneratorConfig,
  type ValidationRule,
  type GeneratedFile,
} from './value-object-generator.js';

export {
  StatusMachineGenerator,
  createStatusMachineGenerator,
  type StatusMachineSpec,
  type StatusTransition,
  type StatusMachineGeneratorConfig,
  type ParsedStatusOption,
} from './status-machine-generator.js';

export {
  ResultAggregator,
  createResultAggregator,
  type AggregatedResult,
  type ResultAggregatorConfig,
} from './result-aggregator.js';

export {
  PatternAutoExtractor,
  createPatternExtractor,
  type ExtractedPattern,
  type PatternVariable,
  type ExtractionResult,
  type PatternExtractorConfig,
} from './pattern-extractor.js';

export {
  PatternMerger,
  createPatternMerger,
  type MergedPattern,
  type MergeResult,
  type PatternMergerConfig,
} from './pattern-merger.js';

export {
  ExpertIntegration,
  createExpertIntegration,
  DEFAULT_EXPERT_CONFIG,
  type ExpertConsultationRequest,
  type ExpertConsultationResult,
  type ExpertRecommendation,
  type ExpertIntegrationConfig,
} from './expert-integration.js';

export {
  PatternLearningService,
  createPatternLearningService,
  DEFAULT_PATTERN_LEARNING_CONFIG,
  type PatternLearningConfig,
  type PatternSuggestion,
  type PatternLearningResult,
  type PatternLibraryEntry,
} from './pattern-learning-service.js';
