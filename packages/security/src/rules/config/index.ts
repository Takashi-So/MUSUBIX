/**
 * @fileoverview Rule Configuration Module
 * @module @nahisaho/musubix-security/rules/config
 * @trace TSK-RULE-002
 */

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
  type RawRuleConfig,
  type RawRuleSettings,
  type ParseResult,
  type ConfigFormat,
} from './config-parser.js';

export {
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
  type RuleProfile,
  type ProfileRuleConfig,
} from './profiles.js';
