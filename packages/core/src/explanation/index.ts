/**
 * Explanation Module
 * 
 * Provides reasoning chain recording and explanation generation
 * 
 * @packageDocumentation
 * @module explanation
 */

export {
  // Reasoning Chain Recorder
  ReasoningChainRecorder,
  createReasoningChainRecorder,
  
  // Types - renamed to avoid collision with types/common.ts
  type ReasoningStepType as RecorderStepType,
  type ConfidenceLevel,
  type ReasoningStep as RecorderStep,
  type Evidence,
  type Alternative,
  type ReasoningChain as RecorderChain,
  type ChainOutcome,
  type ChainQuery,
  type ChainStatistics,
  type ReasoningChainRecorderConfig,
  
  // Constants
  DEFAULT_RECORDER_CONFIG,
} from './reasoning-chain.js';

export {
  // Explanation Generator
  ExplanationGenerator,
  createExplanationGenerator,
  
  // Types
  type ExplanationLevel,
  type ExplanationFormat,
  type AudienceType,
  type ExplanationSection,
  type Explanation,
  type ExplanationGeneratorOptions,
  
  // Constants
  DEFAULT_GENERATOR_OPTIONS,
} from './explanation-generator.js';
