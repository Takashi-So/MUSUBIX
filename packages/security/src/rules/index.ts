/**
 * @fileoverview Rules Module Exports
 * @module @nahisaho/musubix-security/rules
 */

// Core Types
export type {
  SecurityRule,
  RuleContext,
  RuleFinding,
  RuleResult,
  RuleConfig,
  RuleSettings,
  FixSuggestion,
  SourceLocation,
  DetectionMethod,
  RuleSeverity,
  AnalysisProgress,
  AnalysisReport,
  AnalysisSummary,
  RuleEngineOptions as RuleEngineOptionsBase,
} from './types.js';

export {
  SEVERITY_ORDER,
  DEFAULT_RULE_CONFIG,
  meetsSeverityThreshold,
} from './types.js';

// Engine
export {
  RuleEngine,
  createRuleEngine,
  RuleRegistry,
  getGlobalRegistry,
  createRegistry,
  RuleContextBuilder,
  createContextBuilder,
} from './engine/index.js';

export type {
  RuleEngineOptions,
  RuleEngineProgress,
  RuleEngineResult,
  RuleEngineError,
  RuleEngineSummary,
  RuleContextBuildOptions,
} from './engine/index.js';

// Config
export {
  parseConfig,
  loadConfigFile,
  findConfigFile,
  loadProjectConfig,
  createConfigBuilder,
  validateConfig,
  writeConfigFile,
  ConfigBuilder,
  DEFAULT_CONFIG,
  getProfile,
  getProfileNames,
  hasProfile,
  getProfileRuleIds,
  mergeProfileConfig,
  PROFILES,
  PROFILE_MINIMAL,
  PROFILE_STANDARD,
  PROFILE_STRICT,
  PROFILE_OWASP,
  PROFILE_CWE,
} from './config/index.js';

export type {
  RawRuleConfig,
  RawRuleSettings,
  ParseResult,
  ConfigFormat,
  RuleProfile,
  ProfileRuleConfig,
} from './config/index.js';

// OWASP A01-A05 Rules (TSK-RULE-003)
export {
  owaspA01BrokenAccessControl,
  owaspA02CryptographicFailures,
  owaspA03Injection,
  owaspA04InsecureDesign,
  owaspA05SecurityMisconfiguration,
  owaspRulesA01A05,
} from './owasp/index.js';

// OWASP A06-A10 Rules (TSK-RULE-004)
export {
  owaspA06VulnerableComponents,
  owaspA07AuthFailures,
  owaspA08IntegrityFailures,
  owaspA09LoggingFailures,
  owaspA10SSRF,
  owaspRulesA06A10,
  owaspTop10Rules,
} from './owasp/index.js';

// CWE Top 25 Rules (1-13) (TSK-RULE-005)
export {
  cwe787OutOfBoundsWrite,
  cwe79XSS,
  cwe89SQLInjection,
  cwe416UseAfterFree,
  cwe78CommandInjection,
  cwe20InputValidation,
  cwe125OutOfBoundsRead,
  cwe22PathTraversal,
  cwe352CSRF,
  cwe434FileUpload,
  cwe862MissingAuth,
  cwe476NullDeref,
  cwe287ImproperAuth,
  cweTop25Rules1to13,
  cweTop25Rules,
} from './cwe/index.js';
