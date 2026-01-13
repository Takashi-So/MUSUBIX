/**
 * Validators Module
 * 
 * @packageDocumentation
 * @module validators
 */

export {
  EARSValidator,
  createEARSValidator,
  type EARSPatternType,
  type EARSPatternMatch,
  type EARSValidatorOptions,
  type EARSBatchValidationResult,
  DEFAULT_EARS_OPTIONS,
} from './ears-validator.js';

export {
  MarkdownEARSParser,
  parseMarkdownEARS,
  extractValidEARS,
  type ExtractedEARS,
  type MarkdownEARSResult,
  type MarkdownEARSParserOptions,
} from './markdown-ears-parser.js';

export {
  TraceabilityValidator,
  validateTraceability,
  type ArtifactRef,
  type TraceLink as ValidatorTraceLink, // Renamed to avoid conflict with traceability/manager
  type TraceabilityValidationResult,
  type TraceabilityIssue,
  type TraceabilityValidatorOptions,
} from './traceability-validator.js';

// Note: EARSComponents and EARSValidationResult are exported from types module
