/**
 * Design module
 * 
 * Design validation and optimization tools
 * 
 * @packageDocumentation
 * @module design
 */

export {
  PatternDetector,
  createPatternDetector,
  DESIGN_PATTERNS,
  DEFAULT_DETECTOR_CONFIG,
  type DesignPattern,
  type PatternIndicator,
  type PatternParticipant,
  type PatternDetectionResult,
  type PatternSuggestion,
  type PatternLocation,
  type MatchedIndicator,
  type CodeStructure,
  type ClassInfo,
  type FunctionInfo,
  type RelationshipInfo,
  type PatternDetectorConfig,
} from './pattern-detector.js';

// Note: PatternCategory is exported from types module

export * from './solid-validator.js';
export * from './framework-optimizer.js';
