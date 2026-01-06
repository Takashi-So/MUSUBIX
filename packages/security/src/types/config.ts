/**
 * @fileoverview Security configuration type definitions
 * @module @nahisaho/musubix-security/types/config
 * @trace REQ-SEC-CONFIG-001, REQ-SEC-CONFIG-002, REQ-SEC-REPORT-001
 */

import type { Severity, ScanOptions } from './vulnerability.js';
import type { TaintAnalysisOptions } from './taint.js';
import type { FixGenerationOptions } from './fix.js';
import type { SecretScanOptions } from './secret.js';
import type { AuditOptions, SBOMOptions, LicensePolicy } from './dependency.js';

/**
 * Output format for reports
 * @trace REQ-SEC-REPORT-001
 */
export type ReportFormat = 'json' | 'sarif' | 'markdown' | 'html';

/**
 * Knowledge graph mode
 * @trace REQ-SEC-KG-001
 */
export type KnowledgeGraphMode = 'local' | 'global' | 'hybrid' | 'disabled';

/**
 * Cache strategy
 */
export type CacheStrategy = 'memory' | 'file' | 'none';

/**
 * Report configuration
 * @trace REQ-SEC-REPORT-001
 */
export interface ReportConfig {
  /** Output format(s) */
  format: ReportFormat | ReportFormat[];
  /** Output file path (stdout if not specified) */
  outputPath?: string;
  /** Include code snippets in report */
  includeCode?: boolean;
  /** Include code snippets in report (alias) */
  includeCodeSnippets?: boolean;
  /** Include fix suggestions in report */
  includeFixes?: boolean;
  /** Include taint paths in report */
  includeTaintPaths?: boolean;
  /** Group by file or vulnerability type */
  groupBy?: 'file' | 'type' | 'severity';
  /** Sort by */
  sortBy?: 'severity' | 'file' | 'type';
  /** Maximum vulnerabilities per file in report */
  maxPerFile?: number;
  /** Include summary section */
  includeSummary?: boolean;
  /** Custom report template path */
  templatePath?: string;
}

/**
 * Knowledge graph configuration
 * @trace REQ-SEC-KG-001
 */
export interface KnowledgeGraphConfig {
  /** KG mode */
  mode: KnowledgeGraphMode;
  /** Local KG database path */
  localDbPath?: string;
  /** Global YATA endpoint */
  globalEndpoint?: string;
  /** Auto-learn from scan results */
  autoLearn?: boolean;
  /** Namespace for learned patterns */
  namespace?: string;
  /** Maximum patterns to cache */
  maxCachedPatterns?: number;
}

/**
 * AI assistance configuration
 */
export interface AIConfig {
  /** Enable AI-assisted features */
  enabled: boolean;
  /** AI provider */
  provider?: 'vscode-lm' | 'openai' | 'anthropic';
  /** Model identifier */
  model?: string;
  /** Maximum tokens for generation */
  maxTokens?: number;
  /** Temperature for generation */
  temperature?: number;
  /** Use AI for fix generation */
  useForFixes?: boolean;
  /** Use AI for vulnerability explanation */
  useForExplanation?: boolean;
}

/**
 * Cache configuration
 */
export interface CacheConfig {
  /** Cache strategy */
  strategy: CacheStrategy;
  /** Cache directory for file strategy */
  cacheDir?: string;
  /** TTL in seconds for cached entries */
  ttlSeconds?: number;
  /** Maximum cache size in MB */
  maxSizeMB?: number;
  /** Cache AST parse results */
  cacheAST?: boolean;
  /** Cache vulnerability patterns */
  cachePatterns?: boolean;
}

/**
 * CI/CD integration configuration
 */
export interface CIConfig {
  /** Fail build on severity */
  failOnSeverity?: Severity;
  /** Fail build on vulnerability count */
  failOnCount?: number;
  /** Fail build on new vulnerabilities only */
  failOnNewOnly?: boolean;
  /** Baseline file path for comparison */
  baselinePath?: string;
  /** Output SARIF for GitHub Code Scanning */
  sarifOutput?: boolean;
  /** SARIF output path */
  sarifPath?: string;
  /** Enable PR comments */
  prComments?: boolean;
  /** CI platform */
  platform?: 'github' | 'gitlab' | 'azure-devops' | 'jenkins';
}

/**
 * Complete security configuration
 * @trace REQ-SEC-CONFIG-001
 */
export interface SecurityConfig {
  /** Configuration version */
  version: '1.0';
  /** Project root path */
  projectRoot?: string;
  /** Scan configuration */
  scan?: ScanOptions;
  /** Taint analysis configuration */
  taint?: TaintAnalysisOptions;
  /** Fix generation configuration */
  fix?: FixGenerationOptions;
  /** Secret detection configuration */
  secret?: SecretScanOptions;
  /** Dependency audit configuration */
  audit?: AuditOptions;
  /** SBOM generation configuration */
  sbom?: SBOMOptions;
  /** License policy */
  licensePolicy?: LicensePolicy;
  /** Report configuration */
  report?: ReportConfig;
  /** Knowledge graph configuration */
  knowledgeGraph?: KnowledgeGraphConfig;
  /** AI configuration */
  ai?: AIConfig;
  /** Cache configuration */
  cache?: CacheConfig;
  /** CI/CD configuration */
  ci?: CIConfig;
  /** Global severity filter */
  severityFilter?: Severity[];
  /** Global exclude patterns */
  excludePatterns?: string[];
  /** Custom rules directory */
  customRulesDir?: string;
  /** Enable verbose logging */
  verbose?: boolean;
  /** Enable debug mode */
  debug?: boolean;
}

/**
 * Default security configuration
 */
export const DEFAULT_CONFIG: SecurityConfig = {
  version: '1.0',
  scan: {
    severityFilter: ['critical', 'high', 'medium'],
    rulesets: ['owasp-top-10', 'cwe-top-25'],
    incremental: true,
  },
  taint: {
    interprocedural: true,
    trackAsync: true,
    maxPathDepth: 10,
  },
  fix: {
    useAI: false,
    generateAlternatives: true,
    maxAlternatives: 3,
    preserveStyle: true,
  },
  secret: {
    ignoreTestValues: true,
    verify: false,
  },
  audit: {
    includeDevDependencies: false,
    minSeverity: 'medium',
    suggestUpgrades: true,
    checkBreaking: true,
  },
  report: {
    format: 'json',
    includeCodeSnippets: true,
    includeFixes: true,
    includeTaintPaths: true,
    groupBy: 'severity',
    includeSummary: true,
  },
  knowledgeGraph: {
    mode: 'local',
    autoLearn: true,
    namespace: 'security',
    maxCachedPatterns: 1000,
  },
  ai: {
    enabled: false,
  },
  cache: {
    strategy: 'file',
    ttlSeconds: 3600,
    maxSizeMB: 100,
    cacheAST: true,
    cachePatterns: true,
  },
  ci: {
    failOnSeverity: 'high',
    sarifOutput: true,
  },
  severityFilter: ['critical', 'high', 'medium'],
  verbose: false,
  debug: false,
};

/**
 * Configuration file locations (in order of precedence)
 */
export const CONFIG_FILE_LOCATIONS = [
  'musubix-security.config.ts',
  'musubix-security.config.js',
  'musubix-security.config.json',
  '.musubix-security.yml',
  '.musubix-security.yaml',
  '.musubix-securityrc',
  '.musubix-securityrc.json',
];

/**
 * Environment variable prefix for configuration
 */
export const ENV_PREFIX = 'MUSUBIX_SECURITY_';

/**
 * Configuration schema version
 */
export const CONFIG_SCHEMA_VERSION = '1.0';
