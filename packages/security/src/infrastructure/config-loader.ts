/**
 * @fileoverview Configuration loader using cosmiconfig
 * @module @nahisaho/musubix-security/infrastructure/config-loader
 * @trace REQ-SEC-CONFIG-001, REQ-SEC-CONFIG-002
 */

import { cosmiconfig, cosmiconfigSync } from 'cosmiconfig';
import { z } from 'zod';
import type { SecurityConfig } from '../types/index.js';
import { DEFAULT_CONFIG, CONFIG_FILE_LOCATIONS, ENV_PREFIX } from '../types/config.js';

/**
 * Zod schema for severity
 */
const SeveritySchema = z.enum(['critical', 'high', 'medium', 'low']);

/**
 * Zod schema for scan options
 */
const ScanOptionsSchema = z.object({
  severityFilter: z.array(SeveritySchema).optional(),
  rulesets: z.array(z.enum(['owasp-top-10', 'cwe-top-25', 'custom'])).optional(),
  excludePatterns: z.array(z.string()).optional(),
  maxFileSize: z.number().positive().optional(),
  incremental: z.boolean().optional(),
  customRulesDir: z.string().optional(),
}).optional();

/**
 * Zod schema for taint options
 */
const TaintOptionsSchema = z.object({
  customSources: z.array(z.object({
    pattern: z.string(),
    category: z.string(),
    description: z.string(),
  })).optional(),
  customSinks: z.array(z.object({
    pattern: z.string(),
    category: z.string(),
    severity: SeveritySchema,
    description: z.string(),
  })).optional(),
  additionalSanitizers: z.array(z.object({
    functionName: z.string(),
    sinkCategories: z.array(z.string()),
  })).optional(),
  maxPathDepth: z.number().positive().optional(),
  interprocedural: z.boolean().optional(),
  trackAsync: z.boolean().optional(),
  excludePatterns: z.array(z.string()).optional(),
}).optional();

/**
 * Zod schema for fix options
 */
const FixOptionsSchema = z.object({
  preferredStrategies: z.array(z.string()).optional(),
  useAI: z.boolean().optional(),
  aiModel: z.string().optional(),
  generateAlternatives: z.boolean().optional(),
  maxAlternatives: z.number().positive().optional(),
  preserveStyle: z.boolean().optional(),
  targetFramework: z.string().optional(),
}).optional();

/**
 * Zod schema for secret options
 */
const SecretOptionsSchema = z.object({
  customPatterns: z.array(z.any()).optional(),
  disablePatterns: z.array(z.string()).optional(),
  excludePatterns: z.array(z.string()).optional(),
  ignoreTestValues: z.boolean().optional(),
  maxFileSize: z.number().positive().optional(),
  verify: z.boolean().optional(),
  entropyThreshold: z.number().min(0).max(8).optional(),
}).optional();

/**
 * Zod schema for audit options
 */
const AuditOptionsSchema = z.object({
  includeDevDependencies: z.boolean().optional(),
  minSeverity: SeveritySchema.optional(),
  sources: z.array(z.string()).optional(),
  ignoreVulnerabilities: z.array(z.string()).optional(),
  ignorePackages: z.array(z.string()).optional(),
  maxDepth: z.number().positive().optional(),
  suggestUpgrades: z.boolean().optional(),
  checkBreaking: z.boolean().optional(),
  registryUrl: z.string().url().optional(),
}).optional();

/**
 * Zod schema for report config
 */
const ReportConfigSchema = z.object({
  format: z.enum(['json', 'sarif', 'markdown', 'html', 'csv']).optional(),
  outputPath: z.string().optional(),
  includeCodeSnippets: z.boolean().optional(),
  includeFixes: z.boolean().optional(),
  includeTaintPaths: z.boolean().optional(),
  groupBy: z.enum(['file', 'type', 'severity']).optional(),
  maxPerFile: z.number().positive().optional(),
  includeSummary: z.boolean().optional(),
  templatePath: z.string().optional(),
}).optional();

/**
 * Zod schema for knowledge graph config
 */
const KnowledgeGraphConfigSchema = z.object({
  mode: z.enum(['local', 'global', 'hybrid', 'disabled']).optional(),
  localDbPath: z.string().optional(),
  globalEndpoint: z.string().url().optional(),
  autoLearn: z.boolean().optional(),
  namespace: z.string().optional(),
  maxCachedPatterns: z.number().positive().optional(),
}).optional();

/**
 * Zod schema for AI config
 */
const AIConfigSchema = z.object({
  enabled: z.boolean().optional(),
  provider: z.enum(['vscode-lm', 'openai', 'anthropic']).optional(),
  model: z.string().optional(),
  maxTokens: z.number().positive().optional(),
  temperature: z.number().min(0).max(2).optional(),
  useForFixes: z.boolean().optional(),
  useForExplanation: z.boolean().optional(),
}).optional();

/**
 * Zod schema for cache config
 */
const CacheConfigSchema = z.object({
  strategy: z.enum(['memory', 'file', 'none']).optional(),
  cacheDir: z.string().optional(),
  ttlSeconds: z.number().positive().optional(),
  maxSizeMB: z.number().positive().optional(),
  cacheAST: z.boolean().optional(),
  cachePatterns: z.boolean().optional(),
}).optional();

/**
 * Zod schema for CI config
 */
const CIConfigSchema = z.object({
  failOnSeverity: SeveritySchema.optional(),
  failOnCount: z.number().nonnegative().optional(),
  failOnNewOnly: z.boolean().optional(),
  baselinePath: z.string().optional(),
  sarifOutput: z.boolean().optional(),
  sarifPath: z.string().optional(),
  prComments: z.boolean().optional(),
  platform: z.enum(['github', 'gitlab', 'azure-devops', 'jenkins']).optional(),
}).optional();

/**
 * Complete security config schema
 */
const SecurityConfigSchema = z.object({
  version: z.literal('1.0').optional(),
  projectRoot: z.string().optional(),
  scan: ScanOptionsSchema,
  taint: TaintOptionsSchema,
  fix: FixOptionsSchema,
  secret: SecretOptionsSchema,
  audit: AuditOptionsSchema,
  sbom: z.object({
    format: z.enum(['cyclonedx', 'spdx']).optional(),
    includeDevDependencies: z.boolean().optional(),
    includeVulnerabilities: z.boolean().optional(),
    includeLicenses: z.boolean().optional(),
    outputPath: z.string().optional(),
  }).optional(),
  licensePolicy: z.object({
    allowed: z.array(z.string()).optional(),
    denied: z.array(z.string()).optional(),
    requireApproval: z.array(z.string()).optional(),
  }).optional(),
  report: ReportConfigSchema,
  knowledgeGraph: KnowledgeGraphConfigSchema,
  ai: AIConfigSchema,
  cache: CacheConfigSchema,
  ci: CIConfigSchema,
  severityFilter: z.array(SeveritySchema).optional(),
  excludePatterns: z.array(z.string()).optional(),
  customRulesDir: z.string().optional(),
  verbose: z.boolean().optional(),
  debug: z.boolean().optional(),
});

/**
 * Configuration loader result
 */
export interface ConfigLoadResult {
  config: SecurityConfig;
  filepath?: string;
  isEmpty: boolean;
}

/**
 * Load configuration from environment variables
 */
function loadEnvConfig(): Partial<SecurityConfig> {
  const config: Partial<SecurityConfig> = {};

  // Helper to get env var with prefix
  const getEnv = (key: string): string | undefined => process.env[`${ENV_PREFIX}${key}`];

  // Verbose mode
  const verbose = getEnv('VERBOSE');
  if (verbose) {
    config.verbose = verbose === 'true' || verbose === '1';
  }

  // Debug mode
  const debug = getEnv('DEBUG');
  if (debug) {
    config.debug = debug === 'true' || debug === '1';
  }

  // Severity filter
  const severityFilter = getEnv('SEVERITY_FILTER');
  if (severityFilter) {
    config.severityFilter = severityFilter.split(',').map((s) => s.trim() as any);
  }

  // Project root
  const projectRoot = getEnv('PROJECT_ROOT');
  if (projectRoot) {
    config.projectRoot = projectRoot;
  }

  // AI enabled
  const aiEnabled = getEnv('AI_ENABLED');
  if (aiEnabled) {
    config.ai = { enabled: aiEnabled === 'true' || aiEnabled === '1' };
  }

  // KG mode
  const kgMode = getEnv('KG_MODE');
  if (kgMode) {
    config.knowledgeGraph = { mode: kgMode as any };
  }

  // Report format
  const reportFormat = getEnv('REPORT_FORMAT');
  if (reportFormat) {
    config.report = { format: reportFormat as any };
  }

  // CI fail severity
  const ciFailSeverity = getEnv('CI_FAIL_SEVERITY');
  if (ciFailSeverity) {
    config.ci = { failOnSeverity: ciFailSeverity as any };
  }

  return config;
}

/**
 * Deep merge two objects
 */
function deepMerge<T extends Record<string, any>>(target: T, source: Partial<T>): T {
  const result = { ...target };

  for (const key of Object.keys(source) as (keyof T)[]) {
    const sourceValue = source[key];
    const targetValue = target[key];

    if (
      sourceValue !== undefined &&
      sourceValue !== null &&
      typeof sourceValue === 'object' &&
      !Array.isArray(sourceValue) &&
      typeof targetValue === 'object' &&
      !Array.isArray(targetValue)
    ) {
      result[key] = deepMerge(targetValue as any, sourceValue as any);
    } else if (sourceValue !== undefined) {
      result[key] = sourceValue as any;
    }
  }

  return result;
}

/**
 * Load configuration asynchronously
 */
export async function loadConfig(searchFrom?: string): Promise<ConfigLoadResult> {
  const explorer = cosmiconfig('musubix-security', {
    searchPlaces: CONFIG_FILE_LOCATIONS,
  });

  try {
    const result = searchFrom
      ? await explorer.search(searchFrom)
      : await explorer.search();

    if (result && !result.isEmpty) {
      // Validate loaded config
      const parsed = SecurityConfigSchema.safeParse(result.config);
      if (!parsed.success) {
        console.error('Configuration validation error:', parsed.error.format());
        throw new Error(`Invalid configuration: ${parsed.error.message}`);
      }

      // Merge with defaults and env
      const envConfig = loadEnvConfig();
      const fileConfig = parsed.data as Partial<SecurityConfig>;
      const mergedConfig = deepMerge(deepMerge(DEFAULT_CONFIG, fileConfig), envConfig);

      return {
        config: mergedConfig,
        filepath: result.filepath,
        isEmpty: false,
      };
    }

    // No config file found, use defaults with env overrides
    const envConfig = loadEnvConfig();
    const mergedConfig = deepMerge(DEFAULT_CONFIG, envConfig);

    return {
      config: mergedConfig,
      isEmpty: true,
    };
  } catch (error) {
    // On error, return defaults with env overrides
    console.error('Error loading configuration:', error);
    const envConfig = loadEnvConfig();
    const mergedConfig = deepMerge(DEFAULT_CONFIG, envConfig);

    return {
      config: mergedConfig,
      isEmpty: true,
    };
  }
}

/**
 * Load configuration synchronously
 */
export function loadConfigSync(searchFrom?: string): ConfigLoadResult {
  const explorer = cosmiconfigSync('musubix-security', {
    searchPlaces: CONFIG_FILE_LOCATIONS,
  });

  try {
    const result = searchFrom
      ? explorer.search(searchFrom)
      : explorer.search();

    if (result && !result.isEmpty) {
      const parsed = SecurityConfigSchema.safeParse(result.config);
      if (!parsed.success) {
        throw new Error(`Invalid configuration: ${parsed.error.message}`);
      }

      const envConfig = loadEnvConfig();
      const fileConfig = parsed.data as Partial<SecurityConfig>;
      const mergedConfig = deepMerge(deepMerge(DEFAULT_CONFIG, fileConfig), envConfig);

      return {
        config: mergedConfig,
        filepath: result.filepath,
        isEmpty: false,
      };
    }

    const envConfig = loadEnvConfig();
    const mergedConfig = deepMerge(DEFAULT_CONFIG, envConfig);

    return {
      config: mergedConfig,
      isEmpty: true,
    };
  } catch (error) {
    console.error('Error loading configuration:', error);
    const envConfig = loadEnvConfig();
    const mergedConfig = deepMerge(DEFAULT_CONFIG, envConfig);

    return {
      config: mergedConfig,
      isEmpty: true,
    };
  }
}

/**
 * Validate a configuration object
 */
export function validateConfig(config: unknown): { valid: boolean; errors?: string[] } {
  const result = SecurityConfigSchema.safeParse(config);
  if (result.success) {
    return { valid: true };
  }

  const errors = result.error.issues.map(
    (issue) => `${issue.path.join('.')}: ${issue.message}`
  );
  return { valid: false, errors };
}

/**
 * Get config schema for documentation
 */
export function getConfigSchema(): z.ZodType<any> {
  return SecurityConfigSchema;
}
