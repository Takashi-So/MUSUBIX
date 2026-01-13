/**
 * @nahisaho/musubix-expert-delegation
 * Experts Module
 */

// Expert Manager
export { ExpertManager, createExpertManager } from './expert-manager.js';

// Individual Experts
export { architectExpert } from './architect.js';
export { securityAnalystExpert } from './security-analyst.js';
export { codeReviewerExpert } from './code-reviewer.js';
export { planReviewerExpert } from './plan-reviewer.js';
export { earsAnalystExpert } from './ears-analyst.js';
export { formalVerifierExpert } from './formal-verifier.js';
export { ontologyReasonerExpert } from './ontology-reasoner.js';

// Types
export type {
  Expert,
  ExpertType,
  ExpertCapability,
  TriggerPattern,
} from './expert-interface.js';
export { createExpert } from './expert-interface.js';

/**
 * 全デフォルトエキスパートの配列
 */
export const defaultExperts = [
  'architect',
  'security-analyst',
  'code-reviewer',
  'plan-reviewer',
  'ears-analyst',
  'formal-verifier',
  'ontology-reasoner',
] as const;
