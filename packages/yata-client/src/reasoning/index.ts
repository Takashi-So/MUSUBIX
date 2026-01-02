/**
 * Reasoning Module
 * 
 * Neuro-symbolic reasoning capabilities
 * 
 * @packageDocumentation
 * @module reasoning
 */

// Neuro-Symbolic Integrator
export {
  NeuroSymbolicIntegrator,
  createNeuroSymbolicIntegrator,
  type IntegrationMode,
  type IntegratorConfig,
  type NeuralInput,
  type SymbolicConstraints,
  type ValidationRule,
  type ValidationContext,
  type ValidationResult,
  type ValidationIssue,
  type IntegrationResult,
  DEFAULT_INTEGRATOR_CONFIG,
} from './integrator.js';

// Confidence Evaluator
export {
  ConfidenceEvaluator,
  createConfidenceEvaluator,
  combineConfidence,
  type ConfidenceSource,
  type ConfidenceScore,
  type CombinedConfidence,
  type CombinationMethod,
  type ConfidenceEvaluatorConfig,
  type CalibrationData,
  type CalibrationStats,
  DEFAULT_EVALUATOR_CONFIG,
} from './confidence.js';

// Contradiction Detector
export {
  ContradictionDetector,
  createContradictionDetector,
  type ContradictionType,
  type ContradictionSeverity,
  type Contradiction,
  type ConflictingElement,
  type Resolution,
  type ResolutionStrategy,
  type DetectionRule,
  type DetectionContext,
  type DetectionHelpers,
  type ContradictionDetectorConfig,
  type DetectionReport,
  DEFAULT_DETECTOR_CONFIG,
} from './contradiction.js';
