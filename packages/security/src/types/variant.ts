/**
 * @fileoverview Variant Analysis Type Definitions
 * @module @nahisaho/musubix-security/types/variant
 * @trace TSK-002, REQ-SEC-VA-001, REQ-SEC-VA-002, REQ-SEC-VA-003, REQ-SEC-VA-004
 */

// ============================================================================
// Vulnerability Model Types
// ============================================================================

/**
 * Vulnerability model definition
 */
export interface VulnerabilityModel {
  /** Model ID */
  id: string;
  /** Display name */
  name: string;
  /** Description */
  description: string;
  /** CWE IDs */
  cwe: number[];
  /** Severity */
  severity: VulnerabilitySeverity;
  /** Affected languages */
  languages: string[];
  /** Source patterns */
  sources: SourcePattern[];
  /** Sink patterns */
  sinks: SinkPattern[];
  /** Sanitizer patterns */
  sanitizers: SanitizerPattern[];
  /** Propagation rules */
  propagators?: PropagatorPattern[];
  /** Message template */
  messageTemplate: string;
  /** References */
  references: Reference[];
  /** Is enabled? */
  enabled: boolean;
  /** Custom tags */
  tags?: string[];
}

/**
 * Vulnerability severity levels
 */
export type VulnerabilitySeverity = 
  | 'critical'
  | 'high'
  | 'medium'
  | 'low'
  | 'info';

/**
 * Reference link
 */
export interface Reference {
  /** Reference type */
  type: 'cwe' | 'owasp' | 'cve' | 'article' | 'documentation';
  /** Reference ID or URL */
  value: string;
  /** Display title */
  title?: string;
}

// ============================================================================
// Pattern Types
// ============================================================================

/**
 * Source pattern - where tainted data enters
 */
export interface SourcePattern {
  /** Pattern ID */
  id: string;
  /** Pattern type */
  type: 'function' | 'parameter' | 'property' | 'import' | 'annotation';
  /** Pattern matcher */
  matcher: PatternMatcher;
  /** Taint label */
  taintLabel?: string;
  /** Description */
  description?: string;
}

/**
 * Sink pattern - where vulnerabilities manifest
 */
export interface SinkPattern {
  /** Pattern ID */
  id: string;
  /** Pattern type */
  type: 'function' | 'method' | 'property' | 'operator';
  /** Pattern matcher */
  matcher: PatternMatcher;
  /** Vulnerable arguments (indices) */
  vulnerableArgs?: number[];
  /** Required taint labels */
  requiredLabels?: string[];
  /** Description */
  description?: string;
}

/**
 * Sanitizer pattern - neutralizes taint
 */
export interface SanitizerPattern {
  /** Pattern ID */
  id: string;
  /** Pattern type */
  type: 'function' | 'method' | 'validation';
  /** Pattern matcher */
  matcher: PatternMatcher;
  /** Sanitized arguments */
  sanitizedArgs?: number[];
  /** Labels to remove */
  removesLabels?: string[];
  /** Description */
  description?: string;
}

/**
 * Propagator pattern - how taint spreads
 */
export interface PropagatorPattern {
  /** Pattern ID */
  id: string;
  /** Pattern type */
  type: 'function' | 'method' | 'operator' | 'assignment';
  /** Pattern matcher */
  matcher: PatternMatcher;
  /** Input arguments */
  inputArgs: number[];
  /** Output (return = -1) */
  output: number;
  /** Label transformation */
  labelTransform?: 'preserve' | 'merge' | 'replace';
  /** Description */
  description?: string;
}

/**
 * Pattern matcher
 */
export type PatternMatcher =
  | ExactMatcher
  | RegexMatcher
  | GlobMatcher
  | MQLMatcher;

/**
 * Exact string matcher
 */
export interface ExactMatcher {
  type: 'exact';
  value: string;
  caseSensitive?: boolean;
}

/**
 * Regex matcher
 */
export interface RegexMatcher {
  type: 'regex';
  pattern: string;
  flags?: string;
}

/**
 * Glob pattern matcher
 */
export interface GlobMatcher {
  type: 'glob';
  pattern: string;
}

/**
 * MQL query matcher
 */
export interface MQLMatcher {
  type: 'mql';
  query: string;
}

// ============================================================================
// Variant Detection Types
// ============================================================================

/**
 * Vulnerability finding
 */
export interface VulnerabilityFinding {
  /** Finding ID */
  id: string;
  /** Rule/model ID */
  ruleId: string;
  /** Rule name */
  ruleName: string;
  /** CWE IDs */
  cwe: number[];
  /** Severity */
  severity: VulnerabilitySeverity;
  /** Message */
  message: string;
  /** Source location */
  location: SourceLocation;
  /** Taint path (if applicable) */
  taintPath?: TaintPathInfo;
  /** Confidence score (0-1) */
  confidence: number;
  /** Status */
  status: FindingStatus;
  /** Remediation suggestions */
  remediation?: RemediationSuggestion[];
  /** Related findings */
  relatedFindings?: string[];
  /** Custom metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Finding status
 */
export type FindingStatus = 
  | 'open'
  | 'confirmed'
  | 'false-positive'
  | 'fixed'
  | 'wont-fix';

/**
 * Source code location
 */
export interface SourceLocation {
  /** File path */
  file: string;
  /** Start line */
  startLine: number;
  /** End line */
  endLine: number;
  /** Start column */
  startColumn: number;
  /** End column */
  endColumn: number;
  /** Code snippet */
  snippet?: string;
}

/**
 * Taint path information
 */
export interface TaintPathInfo {
  /** Source node */
  source: TaintNode;
  /** Sink node */
  sink: TaintNode;
  /** Intermediate nodes */
  path: TaintNode[];
  /** Path length */
  length: number;
}

/**
 * Taint node in path
 */
export interface TaintNode {
  /** Node ID */
  id: string;
  /** Node type */
  type: 'source' | 'propagator' | 'sink' | 'intermediate';
  /** Location */
  location: SourceLocation;
  /** Code snippet */
  snippet: string;
  /** Taint labels */
  labels: string[];
  /** Description */
  description?: string;
}

/**
 * Remediation suggestion
 */
export interface RemediationSuggestion {
  /** Suggestion type */
  type: 'sanitize' | 'validate' | 'replace' | 'remove' | 'configure';
  /** Description */
  description: string;
  /** Code example */
  example?: string;
  /** Reference */
  reference?: Reference;
  /** Effort estimate */
  effort?: 'low' | 'medium' | 'high';
}

// ============================================================================
// Variant Query Types
// ============================================================================

/**
 * Variant query definition
 */
export interface VariantQuery {
  /** Query ID */
  id: string;
  /** Query name */
  name: string;
  /** Description */
  description: string;
  /** Base vulnerability model */
  baseModel?: string;
  /** MQL query */
  query: string;
  /** Query parameters */
  parameters?: QueryParameter[];
  /** Severity */
  severity: VulnerabilitySeverity;
  /** Tags */
  tags?: string[];
}

/**
 * Query parameter
 */
export interface QueryParameter {
  /** Parameter name */
  name: string;
  /** Parameter type */
  type: 'string' | 'number' | 'boolean' | 'string[]';
  /** Default value */
  default?: unknown;
  /** Description */
  description?: string;
}

// ============================================================================
// Historical Analysis Types
// ============================================================================

/**
 * Historical vulnerability data
 */
export interface HistoricalVulnerability {
  /** Finding ID */
  findingId: string;
  /** When first detected */
  firstDetected: Date;
  /** When fixed (if applicable) */
  fixedAt?: Date;
  /** Git commits where present */
  presentInCommits: string[];
  /** Fix commit (if applicable) */
  fixCommit?: string;
  /** Status history */
  statusHistory: StatusChange[];
}

/**
 * Status change record
 */
export interface StatusChange {
  /** Previous status */
  from: FindingStatus;
  /** New status */
  to: FindingStatus;
  /** When changed */
  timestamp: Date;
  /** Changed by */
  changedBy?: string;
  /** Reason */
  reason?: string;
}

// ============================================================================
// Scan Types
// ============================================================================

/**
 * Scan configuration
 */
export interface ScanConfig {
  /** Target paths */
  targets: string[];
  /** Include patterns */
  include?: string[];
  /** Exclude patterns */
  exclude?: string[];
  /** Enabled models */
  enabledModels?: string[];
  /** Disabled models */
  disabledModels?: string[];
  /** Minimum severity */
  minSeverity?: VulnerabilitySeverity;
  /** Enable incremental scan */
  incremental?: boolean;
  /** Baseline file (for diff scanning) */
  baseline?: string;
  /** Custom models */
  customModels?: VulnerabilityModel[];
  /** Max findings per rule */
  maxFindingsPerRule?: number;
  /** Timeout per file (ms) */
  fileTimeout?: number;
}

/**
 * Scan result
 */
export interface ScanResult {
  /** Scan ID */
  id: string;
  /** Scan timestamp */
  timestamp: Date;
  /** Duration (ms) */
  duration: number;
  /** Scanned files */
  filesScanned: number;
  /** Lines scanned */
  linesScanned: number;
  /** Findings */
  findings: VulnerabilityFinding[];
  /** Summary by severity */
  summary: ScanSummary;
  /** Errors encountered */
  errors?: ScanError[];
  /** Config used */
  config: ScanConfig;
}

/**
 * Scan summary
 */
export interface ScanSummary {
  /** Total findings */
  total: number;
  /** By severity */
  bySeverity: Record<VulnerabilitySeverity, number>;
  /** By CWE */
  byCWE: Record<number, number>;
  /** By file */
  byFile: Record<string, number>;
  /** New findings (vs baseline) */
  newFindings?: number;
  /** Fixed findings (vs baseline) */
  fixedFindings?: number;
}

/**
 * Scan error
 */
export interface ScanError {
  /** File path */
  file: string;
  /** Error type */
  type: 'parse' | 'timeout' | 'memory' | 'unknown';
  /** Error message */
  message: string;
}

// ============================================================================
// Model Registry Types
// ============================================================================

/**
 * Model registry
 */
export interface ModelRegistry {
  /** Registered models */
  models: Map<string, VulnerabilityModel>;
  /** Model categories */
  categories: ModelCategory[];
  /** Custom predicates */
  predicates: Map<string, PredicateInfo>;
}

/**
 * Model category
 */
export interface ModelCategory {
  /** Category ID */
  id: string;
  /** Category name */
  name: string;
  /** Description */
  description: string;
  /** Model IDs in category */
  modelIds: string[];
}

/**
 * Predicate info
 */
export interface PredicateInfo {
  /** Predicate name */
  name: string;
  /** Description */
  description: string;
  /** Parameters */
  parameters: string[];
  /** Return type */
  returnType: string;
}

// ============================================================================
// Built-in Vulnerability Models
// ============================================================================

/**
 * Built-in vulnerability model IDs
 */
export const BUILTIN_MODELS = {
  // Injection
  SQL_INJECTION: 'sql-injection',
  COMMAND_INJECTION: 'command-injection',
  LDAP_INJECTION: 'ldap-injection',
  XPATH_INJECTION: 'xpath-injection',
  NOSQL_INJECTION: 'nosql-injection',
  
  // XSS
  XSS_REFLECTED: 'xss-reflected',
  XSS_STORED: 'xss-stored',
  XSS_DOM: 'xss-dom',
  
  // Path Traversal
  PATH_TRAVERSAL: 'path-traversal',
  
  // SSRF
  SSRF: 'ssrf',
  
  // XXE
  XXE: 'xxe',
  
  // Deserialization
  UNSAFE_DESERIALIZATION: 'unsafe-deserialization',
  
  // Crypto
  WEAK_CRYPTO: 'weak-crypto',
  HARDCODED_SECRET: 'hardcoded-secret',
  
  // Auth
  BROKEN_AUTH: 'broken-auth',
  INSECURE_RANDOM: 'insecure-random',
  
  // Other
  OPEN_REDIRECT: 'open-redirect',
  LOG_INJECTION: 'log-injection',
  REGEX_DOS: 'regex-dos',
} as const;

/**
 * CWE mappings
 */
export const CWE_MAPPINGS: Record<string, number[]> = {
  [BUILTIN_MODELS.SQL_INJECTION]: [89],
  [BUILTIN_MODELS.COMMAND_INJECTION]: [78, 77],
  [BUILTIN_MODELS.LDAP_INJECTION]: [90],
  [BUILTIN_MODELS.XPATH_INJECTION]: [91],
  [BUILTIN_MODELS.NOSQL_INJECTION]: [943],
  [BUILTIN_MODELS.XSS_REFLECTED]: [79],
  [BUILTIN_MODELS.XSS_STORED]: [79],
  [BUILTIN_MODELS.XSS_DOM]: [79],
  [BUILTIN_MODELS.PATH_TRAVERSAL]: [22, 23],
  [BUILTIN_MODELS.SSRF]: [918],
  [BUILTIN_MODELS.XXE]: [611],
  [BUILTIN_MODELS.UNSAFE_DESERIALIZATION]: [502],
  [BUILTIN_MODELS.WEAK_CRYPTO]: [327, 328],
  [BUILTIN_MODELS.HARDCODED_SECRET]: [798],
  [BUILTIN_MODELS.BROKEN_AUTH]: [287],
  [BUILTIN_MODELS.INSECURE_RANDOM]: [330],
  [BUILTIN_MODELS.OPEN_REDIRECT]: [601],
  [BUILTIN_MODELS.LOG_INJECTION]: [117],
  [BUILTIN_MODELS.REGEX_DOS]: [1333],
};

// ============================================================================
// Export Report Types
// ============================================================================

/**
 * Export format
 */
export type ExportFormat = 'sarif' | 'json' | 'csv' | 'html' | 'markdown';

/**
 * SARIF report
 */
export interface SARIFReport {
  /** SARIF version */
  version: '2.1.0';
  /** Schema URL */
  $schema: string;
  /** Runs */
  runs: SARIFRun[];
}

/**
 * SARIF run
 */
export interface SARIFRun {
  /** Tool */
  tool: {
    driver: {
      name: string;
      version: string;
      informationUri?: string;
      rules: SARIFRule[];
    };
  };
  /** Results */
  results: SARIFResult[];
}

/**
 * SARIF rule
 */
export interface SARIFRule {
  /** Rule ID */
  id: string;
  /** Name */
  name: string;
  /** Short description */
  shortDescription: { text: string };
  /** Full description */
  fullDescription?: { text: string };
  /** Default configuration */
  defaultConfiguration?: {
    level: 'error' | 'warning' | 'note' | 'none';
  };
  /** Help */
  help?: { text: string; markdown?: string };
  /** Properties */
  properties?: Record<string, unknown>;
}

/**
 * SARIF result
 */
export interface SARIFResult {
  /** Rule ID */
  ruleId: string;
  /** Rule index */
  ruleIndex?: number;
  /** Level */
  level: 'error' | 'warning' | 'note' | 'none';
  /** Message */
  message: { text: string };
  /** Locations */
  locations: SARIFLocation[];
  /** Code flows */
  codeFlows?: SARIFCodeFlow[];
}

/**
 * SARIF location
 */
export interface SARIFLocation {
  /** Physical location */
  physicalLocation: {
    artifactLocation: {
      uri: string;
      uriBaseId?: string;
    };
    region: {
      startLine: number;
      startColumn: number;
      endLine?: number;
      endColumn?: number;
    };
  };
}

/**
 * SARIF code flow
 */
export interface SARIFCodeFlow {
  /** Thread flows */
  threadFlows: Array<{
    locations: Array<{
      location: SARIFLocation;
      message?: { text: string };
    }>;
  }>;
}
