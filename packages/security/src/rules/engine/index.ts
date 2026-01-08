/**
 * @fileoverview Rule Engine Module Exports
 * @module @nahisaho/musubix-security/rules/engine
 */

// Types
export type {
  RuleEngineOptions,
  RuleEngineProgress,
  RuleEngineResult,
  RuleEngineError,
  RuleEngineSummary,
} from './rule-engine.js';

export type {
  RuleContextBuildOptions,
} from './rule-context.js';

// Classes
export { RuleEngine, createRuleEngine } from './rule-engine.js';
export { RuleContextBuilder, createContextBuilder } from './rule-context.js';
export { RuleRegistry, getGlobalRegistry, createRegistry } from './rule-registry.js';
