/**
 * NonNegotiablesEngine Types
 *
 * Defines non-negotiable rules that must be enforced during development.
 *
 * @see TSK-FR-007 - NonNegotiablesEngine型定義
 * @see REQ-FR-020〜023 - NonNegotiablesEngine
 * @trace DES-MUSUBIX-FR-001 DES-POLICY-002
 */

/**
 * Non-negotiable rule category
 */
export type NonNegotiableCategory =
  | 'security'      // Security-related rules
  | 'architecture'  // Architecture constraints
  | 'quality'       // Quality standards
  | 'compliance'    // Compliance requirements
  | 'convention';   // Coding conventions

/**
 * Non-negotiable rule severity
 */
export type NonNegotiableSeverity = 'critical' | 'high' | 'medium';

/**
 * Non-negotiable rule definition
 */
export interface NonNegotiableRule {
  /** Unique rule identifier */
  readonly id: string;
  /** Rule name */
  readonly name: string;
  /** Rule description */
  readonly description: string;
  /** Rule category */
  readonly category: NonNegotiableCategory;
  /** Severity level */
  readonly severity: NonNegotiableSeverity;
  /** Whether rule is enabled */
  readonly enabled: boolean;
  /** Pattern or condition to check */
  readonly pattern?: string | RegExp;
  /** Custom validation function */
  readonly validate?: (context: ValidationContext) => ValidationResult;
}

/**
 * Validation context for rule checking
 */
export interface ValidationContext {
  /** File path being validated */
  readonly filePath?: string;
  /** File content */
  readonly content?: string;
  /** Artifact type */
  readonly artifactType?: string;
  /** Artifact content */
  readonly artifact?: unknown;
  /** Changed files list */
  readonly changedFiles?: readonly string[];
}

/**
 * Validation result from a single rule
 */
export interface ValidationResult {
  /** Whether validation passed */
  readonly passed: boolean;
  /** Violation message if failed */
  readonly message?: string;
  /** Location of violation */
  readonly location?: ViolationLocation;
}

/**
 * Location of a violation
 */
export interface ViolationLocation {
  readonly file?: string;
  readonly line?: number;
  readonly column?: number;
}

/**
 * Violation report entry
 */
export interface Violation {
  /** Rule that was violated */
  readonly rule: NonNegotiableRule;
  /** Violation message */
  readonly message: string;
  /** Severity of violation */
  readonly severity: NonNegotiableSeverity;
  /** Location of violation */
  readonly location?: ViolationLocation;
  /** Timestamp of detection */
  readonly detectedAt: Date;
}

/**
 * Violation report summary
 */
export interface ViolationReport {
  /** Whether all checks passed */
  readonly passed: boolean;
  /** List of violations */
  readonly violations: readonly Violation[];
  /** Count by severity */
  readonly counts: ViolationCounts;
  /** Summary message */
  readonly summary: string;
  /** Timestamp */
  readonly generatedAt: Date;
}

/**
 * Violation counts by severity
 */
export interface ViolationCounts {
  readonly critical: number;
  readonly high: number;
  readonly medium: number;
  readonly total: number;
}

/**
 * NonNegotiablesEngine configuration
 */
export interface NonNegotiablesConfig {
  /** Rules to use */
  readonly rules: readonly NonNegotiableRule[];
  /** Whether to fail on first violation */
  readonly failFast?: boolean;
  /** Custom rule overrides */
  readonly overrides?: Partial<Record<string, Partial<NonNegotiableRule>>>;
}

/**
 * Default non-negotiable rules based on FastRender insights
 */
export const DEFAULT_NON_NEGOTIABLE_RULES: readonly NonNegotiableRule[] = Object.freeze([
  // Security Rules
  {
    id: 'NN-SEC-001',
    name: 'No Hardcoded Secrets',
    description: 'Prevents hardcoded passwords, API keys, or tokens in code',
    category: 'security',
    severity: 'critical',
    enabled: true,
    pattern: /(password|api[_-]?key|secret|token)\s*[:=]\s*["'][^"']{8,}["']/i,
  },
  {
    id: 'NN-SEC-002',
    name: 'No SQL Injection Patterns',
    description: 'Prevents potential SQL injection vulnerabilities',
    category: 'security',
    severity: 'critical',
    enabled: true,
    pattern: /\+\s*["'].*SELECT.*FROM|execute\s*\(\s*["'].*\+/i,
  },

  // Architecture Rules
  {
    id: 'NN-ARCH-001',
    name: 'No Circular Dependencies',
    description: 'Prevents circular import patterns',
    category: 'architecture',
    severity: 'high',
    enabled: true,
  },
  {
    id: 'NN-ARCH-002',
    name: 'Domain Independence',
    description: 'Domain layer must not depend on infrastructure',
    category: 'architecture',
    severity: 'high',
    enabled: true,
  },

  // Quality Rules
  {
    id: 'NN-QUAL-001',
    name: 'No console.log in Production',
    description: 'Prevents console.log statements in production code',
    category: 'quality',
    severity: 'medium',
    enabled: true,
    pattern: /console\.log\s*\(/,
  },
  {
    id: 'NN-QUAL-002',
    name: 'No TODO/FIXME in Main Branch',
    description: 'Prevents unresolved TODO/FIXME comments',
    category: 'quality',
    severity: 'medium',
    enabled: true,
    pattern: /\/\/\s*(TODO|FIXME|HACK|XXX):/i,
  },

  // Convention Rules
  {
    id: 'NN-CONV-001',
    name: 'Test Files Naming',
    description: 'Test files must follow *.test.ts or *.spec.ts naming',
    category: 'convention',
    severity: 'medium',
    enabled: true,
  },
  {
    id: 'NN-CONV-002',
    name: 'Interface Prefix',
    description: 'Interfaces should start with I prefix',
    category: 'convention',
    severity: 'medium',
    enabled: false, // Optional rule
  },
]);

/**
 * Create a non-negotiable rule
 */
export function createNonNegotiableRule(
  params: Omit<NonNegotiableRule, 'enabled'> & { enabled?: boolean }
): NonNegotiableRule {
  return Object.freeze({
    ...params,
    enabled: params.enabled ?? true,
  });
}

/**
 * Create initial violation counts
 */
export function createViolationCounts(): ViolationCounts {
  return Object.freeze({
    critical: 0,
    high: 0,
    medium: 0,
    total: 0,
  });
}

/**
 * Create a violation report
 */
export function createViolationReport(
  violations: readonly Violation[]
): ViolationReport {
  const counts: ViolationCounts = {
    critical: violations.filter(v => v.severity === 'critical').length,
    high: violations.filter(v => v.severity === 'high').length,
    medium: violations.filter(v => v.severity === 'medium').length,
    total: violations.length,
  };

  const passed = violations.length === 0;
  const summary = passed
    ? 'All non-negotiable checks passed'
    : `${counts.total} violations found (${counts.critical} critical, ${counts.high} high, ${counts.medium} medium)`;

  return Object.freeze({
    passed,
    violations,
    counts: Object.freeze(counts),
    summary,
    generatedAt: new Date(),
  });
}
