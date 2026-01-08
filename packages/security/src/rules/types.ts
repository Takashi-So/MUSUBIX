/**
 * @fileoverview Rule Engine Type Definitions
 * @module @nahisaho/musubix-security/rules/types
 * @trace REQ-RULE-001, REQ-RULE-002, REQ-RULE-003
 */

import type { SourceFile } from 'ts-morph';
import type { TaintResult, TaintPath } from '../types/taint.js';

/**
 * Rule severity levels
 */
export type RuleSeverity = 'critical' | 'high' | 'medium' | 'low' | 'info';

/**
 * Detection method types
 */
export type DetectionMethod =
  | 'taint-analysis'
  | 'pattern-match'
  | 'type-analysis'
  | 'config-check'
  | 'dependency-check'
  | 'combined';

/**
 * Source location in code
 */
export interface SourceLocation {
  /** File path */
  file: string;
  /** Start line (1-based) */
  startLine: number;
  /** End line (1-based) */
  endLine: number;
  /** Start column (0-based) */
  startColumn?: number;
  /** End column (0-based) */
  endColumn?: number;
}

/**
 * Fix suggestion for a finding
 */
export interface FixSuggestion {
  /** Description of the fix */
  description: string;
  /** Replacement text */
  replacement?: string;
  /** Location to apply the fix */
  location: SourceLocation;
  /** Is this an automated fix? */
  isAutoFixable: boolean;
}

/**
 * Individual finding from rule execution
 */
export interface RuleFinding {
  /** Unique finding ID */
  id: string;
  /** Rule ID that generated this finding */
  ruleId: string;
  /** Finding severity */
  severity: RuleSeverity;
  /** Human-readable message */
  message: string;
  /** Source location */
  location: SourceLocation;
  /** Related CWE IDs */
  cwe?: string[];
  /** Related OWASP categories */
  owasp?: string[];
  /** Remediation guidance */
  remediation?: string;
  /** Is this finding suppressed? */
  suppressed?: boolean;
  /** Suppression reason if suppressed */
  suppressionReason?: string;
  /** Fix suggestion */
  fix?: FixSuggestion;
  /** Suggestion for remediation (alternative to fix) */
  suggestion?: {
    /** Description of suggested fix */
    description: string;
    /** Example code */
    example?: string;
  };
  /** Additional metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Result from executing a single rule
 */
export interface RuleResult {
  /** Rule ID */
  ruleId: string;
  /** Rule name */
  ruleName: string;
  /** Findings generated */
  findings: RuleFinding[];
  /** Execution time in milliseconds */
  executionTime: number;
  /** Errors encountered */
  errors: string[];
  /** Was execution successful? */
  success: boolean;
}

/**
 * Rule configuration settings
 */
export interface RuleSettings {
  /** Is rule enabled? */
  enabled: boolean;
  /** Override default severity */
  severity?: RuleSeverity;
  /** Rule-specific options */
  options?: Record<string, unknown>;
}

/**
 * Global rule configuration
 */
export interface RuleConfig {
  /** Configuration profile */
  profile?: string;
  /** Rule-specific settings */
  rules: Record<string, RuleSettings>;
  /** File patterns to exclude */
  exclude: string[];
  /** File patterns to include */
  include: string[];
  /** Minimum severity to report */
  severityThreshold: RuleSeverity;
  /** Enable taint analysis */
  enableTaintAnalysis: boolean;
  /** Enable DFG analysis */
  enableDFG: boolean;
}

/**
 * Taint analysis results for rule context
 */
export interface RuleTaintResults {
  /** Taint flows (alias for unsafePaths) */
  flows: TaintPath[];
  /** Full taint analysis result */
  fullResult?: TaintResult;
}

/**
 * Rule execution context
 */
export interface RuleContext {
  /** File path being analyzed */
  filePath: string;
  /** Source code content */
  sourceCode: string;
  /** ts-morph SourceFile AST */
  sourceFile: SourceFile;
  /** Project root directory */
  projectRoot: string;
  /** Rule configuration */
  config: RuleConfig;
  /** Results from previously executed rules */
  previousResults: Map<string, RuleResult>;
  /** Taint analysis results (if available) */
  taintResults?: RuleTaintResults;
  /** Report a finding */
  report(finding: Omit<RuleFinding, 'id' | 'ruleId'>): void;
  /** Get option value for current rule */
  getOption<T>(key: string, defaultValue: T): T;
}

/**
 * Rule reference link
 */
export interface RuleReference {
  /** Reference title */
  title: string;
  /** Reference URL */
  url: string;
}

/**
 * Security rule interface
 */
export interface SecurityRule {
  /** Unique rule ID (e.g., "CWE-079", "OWASP-A03") */
  id: string;
  /** Human-readable name */
  name: string;
  /** Detailed description */
  description: string;
  /** Default severity */
  defaultSeverity: RuleSeverity;
  /** Rule category for grouping */
  category?: string;
  /** Related CWE IDs */
  cwe?: string[];
  /** Related OWASP categories */
  owasp?: string[];
  /** Detection method used */
  detectionMethod?: DetectionMethod;
  /** Tags for categorization */
  tags?: string[];
  /** Reference links */
  references?: RuleReference[];
  /** Execute the rule */
  analyze(context: RuleContext): Promise<RuleFinding[]>;
  /** Generate fix suggestion for a finding */
  getSuggestion?(finding: RuleFinding): FixSuggestion | null;
}

/**
 * Rule engine options
 */
export interface RuleEngineOptions {
  /** Configuration */
  config?: Partial<RuleConfig>;
  /** Enable parallel execution */
  parallel?: boolean;
  /** Maximum concurrent rules */
  maxConcurrent?: number;
  /** Progress callback */
  onProgress?: (progress: AnalysisProgress) => void;
}

/**
 * Analysis progress information
 */
export interface AnalysisProgress {
  /** Current phase */
  phase: 'initializing' | 'parsing' | 'analyzing' | 'reporting' | 'complete';
  /** Total files to analyze */
  totalFiles: number;
  /** Files analyzed so far */
  analyzedFiles: number;
  /** Current file being analyzed */
  currentFile?: string;
  /** Total rules enabled */
  totalRules: number;
  /** Findings so far */
  findingsCount: number;
}

/**
 * Complete analysis report
 */
export interface AnalysisReport {
  /** Report timestamp */
  timestamp: string;
  /** Project root */
  projectRoot: string;
  /** Configuration used */
  config: RuleConfig;
  /** Files analyzed */
  filesAnalyzed: string[];
  /** Total execution time in ms */
  totalTime: number;
  /** Results by rule */
  ruleResults: RuleResult[];
  /** All findings (aggregated) */
  findings: RuleFinding[];
  /** Summary statistics */
  summary: AnalysisSummary;
}

/**
 * Analysis summary statistics
 */
export interface AnalysisSummary {
  /** Total findings */
  total: number;
  /** Findings by severity */
  bySeverity: Record<RuleSeverity, number>;
  /** Findings by rule */
  byRule: Record<string, number>;
  /** Suppressed count */
  suppressed: number;
  /** Files with findings */
  filesWithFindings: number;
  /** Rules that found issues */
  rulesTriggered: number;
}

/**
 * Default rule configuration
 */
export const DEFAULT_RULE_CONFIG: RuleConfig = {
  profile: 'standard',
  rules: {},
  exclude: ['**/node_modules/**', '**/dist/**', '**/*.test.ts', '**/*.spec.ts'],
  include: ['**/*.ts', '**/*.tsx', '**/*.js', '**/*.jsx'],
  severityThreshold: 'info',
  enableTaintAnalysis: true,
  enableDFG: false,
};

/**
 * Severity ordering for comparison
 */
export const SEVERITY_ORDER: Record<RuleSeverity, number> = {
  critical: 0,
  high: 1,
  medium: 2,
  low: 3,
  info: 4,
};

/**
 * Check if severity meets threshold
 */
export function meetsSeverityThreshold(
  severity: RuleSeverity,
  threshold: RuleSeverity
): boolean {
  return SEVERITY_ORDER[severity] <= SEVERITY_ORDER[threshold];
}
