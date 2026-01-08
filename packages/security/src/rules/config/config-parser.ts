/**
 * @fileoverview Rule Configuration Parser
 * @module @nahisaho/musubix-security/rules/config/config-parser
 * @trace TSK-RULE-002
 */

import * as fs from 'node:fs';
import * as path from 'node:path';
import type { RuleConfig, RuleSeverity } from '../types.js';
import { getProfile, PROFILE_STANDARD, type RuleProfile } from './profiles.js';

/**
 * Configuration file formats
 */
export type ConfigFormat = 'json' | 'yaml' | 'js' | 'ts';

/**
 * Raw configuration from file
 */
export interface RawRuleConfig {
  /** Profile name or 'custom' */
  profile?: string;
  /** Extends another config */
  extends?: string | string[];
  /** Rule-specific settings */
  rules?: Record<string, boolean | RuleSeverity | RawRuleSettings>;
  /** Include patterns */
  include?: string[];
  /** Exclude patterns */
  exclude?: string[];
  /** Severity threshold */
  severityThreshold?: RuleSeverity;
  /** Enable taint analysis */
  enableTaintAnalysis?: boolean;
  /** Enable DFG analysis */
  enableDFG?: boolean;
}

/**
 * Raw rule settings
 */
export interface RawRuleSettings {
  enabled?: boolean;
  severity?: RuleSeverity;
  options?: Record<string, unknown>;
}

/**
 * Configuration file names to search
 */
const CONFIG_FILE_NAMES = [
  'musubix-security.config.json',
  'musubix-security.config.js',
  '.musubixsecurity.json',
  '.musubixsecurityrc',
  '.musubixsecurityrc.json',
];

/**
 * Default configuration
 */
export const DEFAULT_CONFIG: RuleConfig = {
  profile: 'standard',
  rules: {},
  include: ['**/*.ts', '**/*.tsx', '**/*.js', '**/*.jsx'],
  exclude: [
    '**/node_modules/**',
    '**/dist/**',
    '**/build/**',
    '**/*.test.ts',
    '**/*.spec.ts',
    '**/*.d.ts',
  ],
  severityThreshold: 'info',
  enableTaintAnalysis: false,
  enableDFG: false,
};

/**
 * Configuration parser result
 */
export interface ParseResult {
  config: RuleConfig;
  configPath?: string;
  errors: string[];
  warnings: string[];
}

/**
 * Parse and normalize rule configuration
 */
export function parseConfig(raw: RawRuleConfig): RuleConfig {
  const profile = raw.profile ? getProfile(raw.profile) : PROFILE_STANDARD;

  // Start with defaults
  const config: RuleConfig = {
    profile: raw.profile ?? 'standard',
    rules: {},
    include: raw.include ?? DEFAULT_CONFIG.include,
    exclude: raw.exclude ?? DEFAULT_CONFIG.exclude,
    severityThreshold: raw.severityThreshold ?? profile?.severityThreshold ?? 'info',
    enableTaintAnalysis: raw.enableTaintAnalysis ?? profile?.enableTaintAnalysis ?? false,
    enableDFG: raw.enableDFG ?? profile?.enableDFG ?? false,
  };

  // Apply profile rules
  if (profile) {
    for (const rule of profile.rules) {
      config.rules[rule.id] = {
        enabled: rule.enabled ?? true,
        severity: rule.severity,
      };
    }
  }

  // Apply raw rule settings
  if (raw.rules) {
    for (const [ruleId, settings] of Object.entries(raw.rules)) {
      const normalized = normalizeRuleSettings(settings);
      config.rules[ruleId] = {
        ...config.rules[ruleId],
        ...normalized,
      };
    }
  }

  return config;
}

/**
 * Normalize rule settings from various formats
 */
function normalizeRuleSettings(
  settings: boolean | RuleSeverity | RawRuleSettings
): { enabled?: boolean; severity?: RuleSeverity; options?: Record<string, unknown> } {
  if (typeof settings === 'boolean') {
    return { enabled: settings };
  }
  if (typeof settings === 'string') {
    // It's a severity level
    return { enabled: true, severity: settings as RuleSeverity };
  }
  return {
    enabled: settings.enabled,
    severity: settings.severity,
    options: settings.options,
  };
}

/**
 * Load configuration from file
 */
export async function loadConfigFile(filePath: string): Promise<ParseResult> {
  const errors: string[] = [];
  const warnings: string[] = [];

  try {
    const content = await fs.promises.readFile(filePath, 'utf-8');
    const ext = path.extname(filePath).toLowerCase();

    let raw: RawRuleConfig;

    if (ext === '.json' || filePath.endsWith('rc')) {
      raw = JSON.parse(content);
    } else if (ext === '.js' || ext === '.ts') {
      // Dynamic import for JS/TS configs
      const module = await import(filePath);
      raw = module.default ?? module;
    } else {
      errors.push(`Unsupported config file format: ${ext}`);
      return { config: DEFAULT_CONFIG, configPath: filePath, errors, warnings };
    }

    // Handle extends
    if (raw.extends) {
      const extendsList = Array.isArray(raw.extends) ? raw.extends : [raw.extends];
      for (const extend of extendsList) {
        const extendedResult = await loadExtendedConfig(extend, path.dirname(filePath));
        if (extendedResult.errors.length > 0) {
          errors.push(...extendedResult.errors);
        }
        // Merge extended config
        raw = mergeRawConfigs(extendedResult.raw, raw);
      }
    }

    const config = parseConfig(raw);

    return { config, configPath: filePath, errors, warnings };
  } catch (error) {
    errors.push(
      `Failed to load config from ${filePath}: ${error instanceof Error ? error.message : String(error)}`
    );
    return { config: DEFAULT_CONFIG, configPath: filePath, errors, warnings };
  }
}

/**
 * Load extended configuration
 */
async function loadExtendedConfig(
  extend: string,
  basePath: string
): Promise<{ raw: RawRuleConfig; errors: string[] }> {
  const errors: string[] = [];

  // Check if it's a built-in preset
  if (extend.startsWith('musubix:')) {
    const presetName = extend.replace('musubix:', '');
    const profile = getProfile(presetName);
    if (profile) {
      return {
        raw: profileToRawConfig(profile),
        errors: [],
      };
    }
    errors.push(`Unknown preset: ${extend}`);
    return { raw: {}, errors };
  }

  // It's a file path
  const extendPath = path.isAbsolute(extend)
    ? extend
    : path.resolve(basePath, extend);

  try {
    const content = await fs.promises.readFile(extendPath, 'utf-8');
    const raw = JSON.parse(content) as RawRuleConfig;
    return { raw, errors: [] };
  } catch (error) {
    errors.push(
      `Failed to load extended config from ${extendPath}: ${error instanceof Error ? error.message : String(error)}`
    );
    return { raw: {}, errors };
  }
}

/**
 * Convert profile to raw config
 */
function profileToRawConfig(profile: RuleProfile): RawRuleConfig {
  const rules: Record<string, RawRuleSettings> = {};
  for (const rule of profile.rules) {
    rules[rule.id] = {
      enabled: rule.enabled ?? true,
      severity: rule.severity,
    };
  }

  return {
    profile: profile.name,
    rules,
    severityThreshold: profile.severityThreshold,
    enableTaintAnalysis: profile.enableTaintAnalysis,
    enableDFG: profile.enableDFG,
  };
}

/**
 * Merge two raw configurations
 */
function mergeRawConfigs(base: RawRuleConfig, override: RawRuleConfig): RawRuleConfig {
  return {
    profile: override.profile ?? base.profile,
    rules: { ...base.rules, ...override.rules },
    include: override.include ?? base.include,
    exclude: override.exclude ?? base.exclude,
    severityThreshold: override.severityThreshold ?? base.severityThreshold,
    enableTaintAnalysis: override.enableTaintAnalysis ?? base.enableTaintAnalysis,
    enableDFG: override.enableDFG ?? base.enableDFG,
  };
}

/**
 * Find configuration file in project
 */
export async function findConfigFile(projectRoot: string): Promise<string | undefined> {
  // Check project root
  for (const fileName of CONFIG_FILE_NAMES) {
    const filePath = path.join(projectRoot, fileName);
    try {
      await fs.promises.access(filePath);
      return filePath;
    } catch {
      // File doesn't exist
    }
  }

  // Check package.json for "musubix-security" field
  const packageJsonPath = path.join(projectRoot, 'package.json');
  try {
    const content = await fs.promises.readFile(packageJsonPath, 'utf-8');
    const pkg = JSON.parse(content);
    if (pkg['musubix-security']) {
      return packageJsonPath;
    }
  } catch {
    // No package.json or no config field
  }

  return undefined;
}

/**
 * Load configuration from project directory
 */
export async function loadProjectConfig(projectRoot: string): Promise<ParseResult> {
  const configPath = await findConfigFile(projectRoot);

  if (!configPath) {
    return {
      config: DEFAULT_CONFIG,
      errors: [],
      warnings: ['No configuration file found, using defaults'],
    };
  }

  // Handle package.json embedded config
  if (configPath.endsWith('package.json')) {
    try {
      const content = await fs.promises.readFile(configPath, 'utf-8');
      const pkg = JSON.parse(content);
      const raw = pkg['musubix-security'] as RawRuleConfig;
      const config = parseConfig(raw);
      return { config, configPath, errors: [], warnings: [] };
    } catch (error) {
      return {
        config: DEFAULT_CONFIG,
        configPath,
        errors: [`Failed to parse package.json config: ${error instanceof Error ? error.message : String(error)}`],
        warnings: [],
      };
    }
  }

  return loadConfigFile(configPath);
}

/**
 * Create configuration builder
 */
export function createConfigBuilder(): ConfigBuilder {
  return new ConfigBuilder();
}

/**
 * Configuration builder for programmatic config creation
 */
export class ConfigBuilder {
  private config: RuleConfig = { ...DEFAULT_CONFIG };

  /**
   * Set profile
   */
  withProfile(profileName: string): this {
    const profile = getProfile(profileName);
    if (profile) {
      this.config.profile = profileName;
      this.config.severityThreshold = profile.severityThreshold;
      this.config.enableTaintAnalysis = profile.enableTaintAnalysis;
      this.config.enableDFG = profile.enableDFG;
      
      // Add profile rules
      for (const rule of profile.rules) {
        this.config.rules[rule.id] = {
          enabled: rule.enabled ?? true,
          severity: rule.severity,
        };
      }
    }
    return this;
  }

  /**
   * Set include patterns
   */
  withInclude(patterns: string[]): this {
    this.config.include = patterns;
    return this;
  }

  /**
   * Set exclude patterns
   */
  withExclude(patterns: string[]): this {
    this.config.exclude = patterns;
    return this;
  }

  /**
   * Set severity threshold
   */
  withSeverityThreshold(severity: RuleSeverity): this {
    this.config.severityThreshold = severity;
    return this;
  }

  /**
   * Enable/disable a rule
   */
  withRule(ruleId: string, enabled: boolean, severity?: RuleSeverity): this {
    this.config.rules[ruleId] = { enabled, severity };
    return this;
  }

  /**
   * Enable taint analysis
   */
  withTaintAnalysis(enabled: boolean = true): this {
    this.config.enableTaintAnalysis = enabled;
    return this;
  }

  /**
   * Enable DFG analysis
   */
  withDFG(enabled: boolean = true): this {
    this.config.enableDFG = enabled;
    return this;
  }

  /**
   * Build the configuration
   */
  build(): RuleConfig {
    return { ...this.config };
  }
}

/**
 * Validate configuration
 */
export function validateConfig(config: RuleConfig): string[] {
  const errors: string[] = [];

  // Validate profile
  if (config.profile && !getProfile(config.profile)) {
    errors.push(`Unknown profile: ${config.profile}`);
  }

  // Validate severity threshold
  const validSeverities: RuleSeverity[] = ['critical', 'high', 'medium', 'low', 'info'];
  if (config.severityThreshold && !validSeverities.includes(config.severityThreshold)) {
    errors.push(`Invalid severity threshold: ${config.severityThreshold}`);
  }

  // Validate rule severities
  for (const [ruleId, ruleConfig] of Object.entries(config.rules)) {
    if (ruleConfig.severity && !validSeverities.includes(ruleConfig.severity)) {
      errors.push(`Invalid severity for rule ${ruleId}: ${ruleConfig.severity}`);
    }
  }

  return errors;
}

/**
 * Write configuration to file
 */
export async function writeConfigFile(
  filePath: string,
  config: RuleConfig
): Promise<void> {
  const content = JSON.stringify(
    {
      profile: config.profile,
      rules: config.rules,
      include: config.include,
      exclude: config.exclude,
      severityThreshold: config.severityThreshold,
      enableTaintAnalysis: config.enableTaintAnalysis,
      enableDFG: config.enableDFG,
    },
    null,
    2
  );

  await fs.promises.writeFile(filePath, content, 'utf-8');
}
