/**
 * MCP Prompts Module
 * 
 * @packageDocumentation
 * @module prompts
 */

export {
  requirementsAnalysisPrompt,
  requirementsReviewPrompt,
  designGenerationPrompt,
  designReviewPrompt,
  taskDecompositionPrompt,
  projectSteeringPrompt,
  sddPrompts,
  getSddPrompts,
} from './sdd-prompts.js';

export {
  synthesisGuidancePrompt,
  patternExplanationPrompt,
  SYNTHESIS_PROMPTS,
  getSynthesisPrompts,
} from './synthesis-prompts.js';
