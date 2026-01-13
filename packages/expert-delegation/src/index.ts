/**
 * @nahisaho/musubix-expert-delegation
 *
 * Expert Delegation System for MUSUBIX
 * VS Code Language Model API based AI expert delegation
 *
 * @version 3.2.0
 * @license MIT
 */

// Types
export type {
  ExpertType,
  ExecutionMode,
  Expert,
  TriggerPattern,
  ExpertCapability,
  DelegationTask,
  DelegationContext,
  DelegationResult,
  TraceLink,
  ConstitutionViolation,
  LMProvider,
  RequestOptions,
  ProviderResponse,
  ModelInfo,
  ModelCriteria,
  IntentResult,
  ModelStats,
} from './types/index.js';
export {
  DelegationError,
  type DelegationErrorCode,
  type EscalationResult,
} from './types/errors.js';

// Providers
export {
  VSCodeLMProvider,
  createVSCodeLMProvider,
} from './providers/vscode-lm-provider.js';
export { ModelSelector, createModelSelector } from './providers/model-selector.js';
export {
  UsageStatistics,
  createUsageStatistics,
} from './providers/usage-statistics.js';

// Experts
export { ExpertManager, createExpertManager } from './experts/expert-manager.js';
export { architectExpert } from './experts/architect.js';
export { securityAnalystExpert } from './experts/security-analyst.js';
export { codeReviewerExpert } from './experts/code-reviewer.js';
export { planReviewerExpert } from './experts/plan-reviewer.js';
export { earsAnalystExpert } from './experts/ears-analyst.js';
export { formalVerifierExpert } from './experts/formal-verifier.js';
export { ontologyReasonerExpert } from './experts/ontology-reasoner.js';

// Triggers
export { SemanticRouter, createSemanticRouter } from './triggers/semantic-router.js';
export {
  ProactiveDelegation,
  createProactiveDelegation,
  type SecurityPatternMatch,
  type NonEarsMatch,
} from './triggers/proactive-delegation.js';
export {
  triggerPatterns,
  getAllTriggerPatterns,
  getTriggerPatterns,
} from './triggers/trigger-patterns.js';

// Delegation
export {
  DelegationEngine,
  createDelegationEngine,
  type DelegationEngineConfig,
} from './delegation/delegation-engine.js';
export { PromptBuilder, createPromptBuilder } from './delegation/prompt-builder.js';
export { AdvisoryMode, createAdvisoryMode } from './delegation/advisory-mode.js';
export {
  ImplementationMode,
  createImplementationMode,
} from './delegation/implementation-mode.js';
export {
  RetryHandler,
  createRetryHandler,
  DEFAULT_RETRY_CONFIG,
  DEFAULT_ESCALATION_CONFIG,
  type RetryConfig,
  type EscalationConfig,
} from './delegation/retry-handler.js';

// MCP
export {
  MCPToolHandlers,
  createMCPToolHandlers,
  type MCPToolResponse,
} from './mcp/handlers.js';
export {
  allSchemas,
  getSchema,
  expertDelegateSchema,
  expertArchitectSchema,
  expertSecuritySchema,
  expertReviewSchema,
  expertPlanSchema,
  expertEarsSchema,
  expertFormalSchema,
  expertOntologySchema,
  triggerDetectSchema,
  delegationRetrySchema,
  providerSelectSchema,
  type MCPToolSchema,
} from './mcp/schemas.js';

/**
 * Version
 */
export const VERSION = '3.2.0';
