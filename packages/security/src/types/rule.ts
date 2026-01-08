/**
 * @fileoverview Security rule type definitions
 * @module @nahisaho/musubix-security/types/rule
 * @trace REQ-SEC-RULES-001, REQ-SEC-RULES-002, REQ-SEC-RULES-003, REQ-SEC-RULES-004
 */

import type { Severity } from './vulnerability.js';
import type { TaintSinkCategory } from './taint.js';

/**
 * OWASP Top 10 (2021) category identifiers
 */
export type OWASPTopTenCategory =
  | 'A01' // Broken Access Control
  | 'A02' // Cryptographic Failures
  | 'A03' // Injection
  | 'A04' // Insecure Design
  | 'A05' // Security Misconfiguration
  | 'A06' // Vulnerable and Outdated Components
  | 'A07' // Identification and Authentication Failures
  | 'A08' // Software and Data Integrity Failures
  | 'A09' // Security Logging and Monitoring Failures
  | 'A10'; // Server-Side Request Forgery

/**
 * Rule category for organization
 */
export type RuleCategory =
  | 'injection'
  | 'authentication'
  | 'authorization'
  | 'cryptography'
  | 'configuration'
  | 'data-exposure'
  | 'logging'
  | 'ssrf'
  | 'deserialization'
  | 'path-traversal'
  | 'code-execution';

/**
 * AST pattern for rule matching
 * @trace DES-SEC-RULES-001
 */
export interface ASTPattern {
  /** Node type to match (e.g., "CallExpression", "MemberExpression") */
  type: string;
  /** Property matchers */
  properties?: Record<string, ASTPatternMatcher>;
  /** Child pattern constraints */
  children?: ASTPattern[];
  /** Pattern constraints */
  constraints?: PatternConstraint[];
}

/**
 * AST pattern matcher options
 */
export type ASTPatternMatcher =
  | string // Exact match
  | RegExp // Regex match
  | ASTPattern // Nested pattern
  | ASTPatternAnyOf // Any of patterns
  | ASTPatternAllOf; // All of patterns

/**
 * Any of pattern matcher
 */
export interface ASTPatternAnyOf {
  anyOf: ASTPatternMatcher[];
}

/**
 * All of pattern matcher
 */
export interface ASTPatternAllOf {
  allOf: ASTPatternMatcher[];
}

/**
 * Pattern constraint for additional checks
 */
export interface PatternConstraint {
  /** Constraint type */
  type: 'tainted' | 'literal' | 'regex' | 'not' | 'contains' | 'startsWith' | 'endsWith';
  /** JSON path to the value to check */
  path: string;
  /** Value for comparison (for literal, regex, contains, startsWith, endsWith) */
  value?: string | RegExp;
  /** Nested constraint (for 'not' type) */
  constraint?: PatternConstraint;
}

/**
 * Fix template for automatic remediation
 * @trace DES-SEC-FIX-001
 */
export interface RuleFixTemplate {
  /** Fix type */
  type: 'replace' | 'wrap' | 'parameterize' | 'insert' | 'delete' | 'custom';
  /** Template string with placeholders */
  template: string;
  /** Required imports to add */
  imports?: RuleFixImport[];
  /** Description of the fix */
  description?: string;
}

/**
 * Import specification for fix
 */
export interface RuleFixImport {
  /** Module to import from */
  module: string;
  /** Named imports */
  namedImports?: string[];
  /** Default import name */
  defaultImport?: string;
  /** Type-only import */
  isTypeOnly?: boolean;
}

/**
 * Security rule definition
 * @trace REQ-SEC-RULES-001, REQ-SEC-RULES-002, DES-SEC-RULES-001
 */
export interface SecurityRuleDefinition {
  /** Unique rule ID (e.g., "sql-injection-template-literal") */
  id: string;
  /** Human-readable rule name */
  name: string;
  /** Severity level */
  severity: Severity;
  /** Related CWE identifier */
  cwe: string;
  /** OWASP Top 10 category */
  owasp?: OWASPTopTenCategory;
  /** Rule category */
  category: RuleCategory;
  /** Short message for display */
  message: string;
  /** Detailed description */
  description: string;
  /** AST pattern to match */
  pattern: ASTPattern;
  /** Automatic fix template */
  fix?: RuleFixTemplate;
  /** Reference URLs */
  references: string[];
  /** Tags for filtering */
  tags: string[];
  /** Languages this rule applies to */
  languages: ('typescript' | 'javascript')[];
  /** Whether rule is enabled by default */
  defaultEnabled: boolean;
  /** Related taint sink category (if applicable) */
  taintSink?: TaintSinkCategory;
}

/**
 * Rule match result
 * @trace DES-SEC-RULES-001
 */
export interface RuleMatch {
  /** Matched rule */
  rule: SecurityRuleDefinition;
  /** Match location in source */
  location: {
    file: string;
    startLine: number;
    endLine: number;
    startColumn: number;
    endColumn: number;
  };
  /** Matched source code */
  matchedCode: string;
  /** Match context for fix generation */
  context: RuleMatchContext;
  /** Taint information (if applicable) */
  taintInfo?: {
    isTainted: boolean;
    sourceCategory?: string;
  };
}

/**
 * Rule match context for fix generation
 */
export interface RuleMatchContext {
  /** Captured groups from pattern matching */
  captures: Record<string, string>;
  /** Surrounding code context */
  surroundingCode: string;
  /** Function/method context */
  functionContext?: string;
  /** Class context */
  classContext?: string;
  /** Module imports */
  imports: string[];
}

/**
 * Rule filter options
 */
export interface RuleFilter {
  /** Filter by severity */
  severity?: Severity[];
  /** Filter by OWASP category */
  owasp?: OWASPTopTenCategory[];
  /** Filter by CWE */
  cwe?: string[];
  /** Filter by category */
  category?: RuleCategory[];
  /** Filter by tags */
  tags?: string[];
  /** Filter by language */
  language?: 'typescript' | 'javascript';
  /** Include only enabled rules */
  enabledOnly?: boolean;
}

/**
 * Rule set configuration
 * @trace REQ-SEC-RULES-003
 */
export interface RuleSetConfig {
  /** Rule set name */
  name: string;
  /** Rule set description */
  description: string;
  /** Rule IDs to include */
  includes: string[];
  /** Rule IDs to exclude */
  excludes?: string[];
  /** Severity overrides */
  severityOverrides?: Record<string, Severity>;
  /** Enable/disable overrides */
  enableOverrides?: Record<string, boolean>;
}

/**
 * Built-in rule sets
 */
export type BuiltinRuleSet =
  | 'owasp-top-10'
  | 'cwe-top-25'
  | 'injection'
  | 'authentication'
  | 'cryptography'
  | 'all';

/**
 * Rule match options
 */
export interface RuleMatchOptions {
  /** Maximum matches per file */
  maxMatchesPerFile?: number;
  /** Include taint analysis */
  includeTaintAnalysis?: boolean;
  /** Timeout per file in ms */
  timeout?: number;
}

/**
 * Rule YAML file structure
 * @trace DES-SEC-RULES-FORMAT-001
 */
export interface RuleYAMLFile {
  /** Metadata section */
  metadata: {
    id: string;
    name: string;
    version: string;
    description: string;
  };
  /** Rules array */
  rules: RuleYAMLEntry[];
}

/**
 * Rule entry in YAML format
 */
export interface RuleYAMLEntry {
  id: string;
  name: string;
  severity: Severity;
  cwe: string;
  owasp?: OWASPTopTenCategory;
  message: string;
  description: string;
  pattern: ASTPattern;
  fix?: RuleFixTemplate;
  references: string[];
  tags: string[];
}
