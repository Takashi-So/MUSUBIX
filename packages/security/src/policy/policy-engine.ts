/**
 * @fileoverview Security Policy Engine
 * @module @nahisaho/musubix-security/policy/policy-engine
 * 
 * Provides customizable security policy definition, evaluation,
 * and enforcement capabilities.
 */

import type { ScanResult, Vulnerability, Severity } from '../types/index.js';

// ============================================================================
// Types
// ============================================================================

/**
 * Policy rule operator
 */
export type PolicyOperator = 
  | 'equals'
  | 'not_equals'
  | 'greater_than'
  | 'less_than'
  | 'greater_than_or_equals'
  | 'less_than_or_equals'
  | 'contains'
  | 'not_contains'
  | 'matches'
  | 'exists'
  | 'not_exists';

/**
 * Policy rule target
 */
export type PolicyTarget =
  | 'severity'
  | 'rule'
  | 'owasp'
  | 'cwe'
  | 'file'
  | 'message'
  | 'count.critical'
  | 'count.high'
  | 'count.medium'
  | 'count.low'
  | 'count.total'
  | 'score';

/**
 * Policy action
 */
export type PolicyAction = 'fail' | 'warn' | 'info' | 'ignore' | 'require_review';

/**
 * Policy rule condition
 */
export interface PolicyCondition {
  /** Target field to evaluate */
  target: PolicyTarget;
  /** Operator for comparison */
  operator: PolicyOperator;
  /** Value to compare against */
  value: string | number | string[];
}

/**
 * Policy rule
 */
export interface PolicyRule {
  /** Rule ID */
  id: string;
  /** Rule name */
  name: string;
  /** Rule description */
  description?: string;
  /** Conditions (all must match - AND logic) */
  conditions: PolicyCondition[];
  /** Action to take when rule matches */
  action: PolicyAction;
  /** Priority (higher = evaluated first) */
  priority?: number;
  /** Whether rule is enabled */
  enabled?: boolean;
  /** Tags for categorization */
  tags?: string[];
  /** Custom metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Security policy
 */
export interface SecurityPolicy {
  /** Policy name */
  name: string;
  /** Policy version */
  version: string;
  /** Policy description */
  description?: string;
  /** Base policies to extend */
  extends?: string[];
  /** Policy rules */
  rules: PolicyRule[];
  /** Global settings */
  settings?: PolicySettings;
  /** Custom metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Policy settings
 */
export interface PolicySettings {
  /** Default action when no rules match */
  defaultAction?: PolicyAction;
  /** Stop evaluating after first match */
  stopOnFirstMatch?: boolean;
  /** Enable strict mode (fail on unknown rules) */
  strictMode?: boolean;
  /** Allowed severities (others are ignored) */
  allowedSeverities?: Severity[];
  /** Blocked file patterns */
  blockedPatterns?: string[];
  /** Required compliance standards */
  requiredCompliance?: string[];
}

/**
 * Policy evaluation result
 */
export interface PolicyEvaluationResult {
  /** Policy name */
  policyName: string;
  /** Policy version */
  policyVersion: string;
  /** Overall pass/fail */
  passed: boolean;
  /** Final action */
  action: PolicyAction;
  /** Rules that matched */
  matchedRules: PolicyRuleMatch[];
  /** Rules that were evaluated */
  evaluatedRules: number;
  /** Evaluation time in ms */
  evaluationTime: number;
  /** Summary by action */
  summary: PolicyEvaluationSummary;
  /** Recommendations */
  recommendations: string[];
}

/**
 * Policy rule match
 */
export interface PolicyRuleMatch {
  /** Rule that matched */
  rule: PolicyRule;
  /** Vulnerabilities that triggered the match */
  triggeredBy: Vulnerability[];
  /** Conditions that matched */
  matchedConditions: PolicyCondition[];
  /** Action from rule */
  action: PolicyAction;
}

/**
 * Policy evaluation summary
 */
export interface PolicyEvaluationSummary {
  /** Count by action */
  byAction: Record<PolicyAction, number>;
  /** Count of failures */
  failures: number;
  /** Count of warnings */
  warnings: number;
  /** Count of reviews required */
  reviewsRequired: number;
}

/**
 * Policy validation result
 */
export interface PolicyValidationResult {
  /** Whether policy is valid */
  valid: boolean;
  /** Validation errors */
  errors: PolicyValidationError[];
  /** Validation warnings */
  warnings: PolicyValidationWarning[];
}

/**
 * Policy validation error
 */
export interface PolicyValidationError {
  /** Error code */
  code: string;
  /** Error message */
  message: string;
  /** Path to problematic element */
  path?: string;
}

/**
 * Policy validation warning
 */
export interface PolicyValidationWarning {
  /** Warning code */
  code: string;
  /** Warning message */
  message: string;
  /** Path to element */
  path?: string;
}

/**
 * Policy engine options
 */
export interface PolicyEngineOptions {
  /** Built-in policies to load */
  builtInPolicies?: ('default' | 'strict' | 'minimal' | 'enterprise')[];
  /** Custom policies */
  customPolicies?: SecurityPolicy[];
  /** Enable caching */
  enableCache?: boolean;
}

// ============================================================================
// Built-in Policies
// ============================================================================

/**
 * Default security policy
 */
const DEFAULT_POLICY: SecurityPolicy = {
  name: 'default',
  version: '1.0.0',
  description: 'Default security policy - blocks critical and high severity issues',
  rules: [
    {
      id: 'block-critical',
      name: 'Block Critical Vulnerabilities',
      description: 'Fail on any critical severity vulnerability',
      conditions: [
        { target: 'count.critical', operator: 'greater_than', value: 0 },
      ],
      action: 'fail',
      priority: 100,
      enabled: true,
    },
    {
      id: 'block-high',
      name: 'Block High Vulnerabilities',
      description: 'Fail on any high severity vulnerability',
      conditions: [
        { target: 'count.high', operator: 'greater_than', value: 0 },
      ],
      action: 'fail',
      priority: 90,
      enabled: true,
    },
    {
      id: 'warn-medium',
      name: 'Warn on Medium Vulnerabilities',
      conditions: [
        { target: 'count.medium', operator: 'greater_than', value: 0 },
      ],
      action: 'warn',
      priority: 50,
      enabled: true,
    },
  ],
  settings: {
    defaultAction: 'info',
    stopOnFirstMatch: false,
  },
};

/**
 * Strict security policy
 */
const STRICT_POLICY: SecurityPolicy = {
  name: 'strict',
  version: '1.0.0',
  description: 'Strict security policy - blocks all vulnerabilities',
  extends: ['default'],
  rules: [
    {
      id: 'block-all',
      name: 'Block All Vulnerabilities',
      conditions: [
        { target: 'count.total', operator: 'greater_than', value: 0 },
      ],
      action: 'fail',
      priority: 100,
      enabled: true,
    },
    {
      id: 'require-high-score',
      name: 'Require High Security Score',
      conditions: [
        { target: 'score', operator: 'less_than', value: 90 },
      ],
      action: 'fail',
      priority: 80,
      enabled: true,
    },
  ],
  settings: {
    defaultAction: 'fail',
    strictMode: true,
  },
};

/**
 * Minimal security policy
 */
const MINIMAL_POLICY: SecurityPolicy = {
  name: 'minimal',
  version: '1.0.0',
  description: 'Minimal security policy - only blocks critical issues',
  rules: [
    {
      id: 'block-critical-only',
      name: 'Block Critical Only',
      conditions: [
        { target: 'count.critical', operator: 'greater_than', value: 0 },
      ],
      action: 'fail',
      priority: 100,
      enabled: true,
    },
  ],
  settings: {
    defaultAction: 'info',
  },
};

/**
 * Enterprise security policy
 */
const ENTERPRISE_POLICY: SecurityPolicy = {
  name: 'enterprise',
  version: '1.0.0',
  description: 'Enterprise security policy with compliance requirements',
  extends: ['default'],
  rules: [
    {
      id: 'owasp-top10-fail',
      name: 'Fail on OWASP Top 10',
      conditions: [
        { target: 'owasp', operator: 'matches', value: '^A[0-9]{2}' },
      ],
      action: 'fail',
      priority: 95,
      enabled: true,
    },
    {
      id: 'require-review-medium',
      name: 'Require Review for Medium Issues',
      conditions: [
        { target: 'count.medium', operator: 'greater_than', value: 5 },
      ],
      action: 'require_review',
      priority: 60,
      enabled: true,
    },
    {
      id: 'block-low-score',
      name: 'Block Low Security Score',
      conditions: [
        { target: 'score', operator: 'less_than', value: 70 },
      ],
      action: 'fail',
      priority: 70,
      enabled: true,
    },
  ],
  settings: {
    defaultAction: 'warn',
    requiredCompliance: ['OWASP-ASVS-L1', 'PCI-DSS'],
  },
};

const BUILT_IN_POLICIES: Record<string, SecurityPolicy> = {
  default: DEFAULT_POLICY,
  strict: STRICT_POLICY,
  minimal: MINIMAL_POLICY,
  enterprise: ENTERPRISE_POLICY,
};

// ============================================================================
// Policy Engine Class
// ============================================================================

/**
 * Security Policy Engine
 * 
 * @example
 * ```typescript
 * const engine = createPolicyEngine({
 *   builtInPolicies: ['default'],
 * });
 * 
 * const result = engine.evaluate('default', scanResult);
 * if (!result.passed) {
 *   console.log('Policy violations:', result.matchedRules);
 * }
 * ```
 */
export class PolicyEngine {
  private policies: Map<string, SecurityPolicy> = new Map();
  private options: Required<PolicyEngineOptions>;

  constructor(options: PolicyEngineOptions = {}) {
    this.options = {
      builtInPolicies: options.builtInPolicies ?? ['default'],
      customPolicies: options.customPolicies ?? [],
      enableCache: options.enableCache ?? true,
    };

    // Load built-in policies
    for (const name of this.options.builtInPolicies) {
      const policy = BUILT_IN_POLICIES[name];
      if (policy) {
        this.policies.set(name, policy);
      }
    }

    // Load custom policies
    for (const policy of this.options.customPolicies) {
      this.policies.set(policy.name, policy);
    }
  }

  /**
   * Evaluate scan result against a policy
   */
  evaluate(policyName: string, scanResult: ScanResult): PolicyEvaluationResult {
    const startTime = Date.now();
    
    const policy = this.getPolicy(policyName);
    if (!policy) {
      throw new Error(`Policy not found: ${policyName}`);
    }

    // Get resolved policy (with extends)
    const resolvedPolicy = this.resolvePolicy(policy);
    
    // Sort rules by priority
    const sortedRules = [...resolvedPolicy.rules]
      .filter(r => r.enabled !== false)
      .sort((a, b) => (b.priority ?? 0) - (a.priority ?? 0));

    const matchedRules: PolicyRuleMatch[] = [];
    const settings = resolvedPolicy.settings ?? {};

    // Evaluate each rule
    for (const rule of sortedRules) {
      const match = this.evaluateRule(rule, scanResult);
      
      if (match) {
        matchedRules.push(match);
        
        if (settings.stopOnFirstMatch) {
          break;
        }
      }
    }

    // Calculate summary
    const summary = this.calculateSummary(matchedRules);
    
    // Determine final action
    const action = this.determineFinalAction(matchedRules, settings);
    const passed = action !== 'fail';

    // Generate recommendations
    const recommendations = this.generateRecommendations(matchedRules, scanResult);

    return {
      policyName: policy.name,
      policyVersion: policy.version,
      passed,
      action,
      matchedRules,
      evaluatedRules: sortedRules.length,
      evaluationTime: Date.now() - startTime,
      summary,
      recommendations,
    };
  }

  /**
   * Validate a policy definition
   */
  validatePolicy(policy: SecurityPolicy): PolicyValidationResult {
    const errors: PolicyValidationError[] = [];
    const warnings: PolicyValidationWarning[] = [];

    // Check required fields
    if (!policy.name) {
      errors.push({ code: 'MISSING_NAME', message: 'Policy name is required' });
    }
    if (!policy.version) {
      errors.push({ code: 'MISSING_VERSION', message: 'Policy version is required' });
    }
    if (!policy.rules || policy.rules.length === 0) {
      warnings.push({ code: 'NO_RULES', message: 'Policy has no rules defined' });
    }

    // Validate rules
    for (let i = 0; i < (policy.rules?.length ?? 0); i++) {
      const rule = policy.rules[i];
      const path = `rules[${i}]`;

      if (!rule.id) {
        errors.push({ code: 'MISSING_RULE_ID', message: 'Rule ID is required', path });
      }
      if (!rule.name) {
        errors.push({ code: 'MISSING_RULE_NAME', message: 'Rule name is required', path });
      }
      if (!rule.conditions || rule.conditions.length === 0) {
        errors.push({ code: 'NO_CONDITIONS', message: 'Rule must have at least one condition', path });
      }
      if (!rule.action) {
        errors.push({ code: 'MISSING_ACTION', message: 'Rule action is required', path });
      }

      // Validate conditions
      for (let j = 0; j < (rule.conditions?.length ?? 0); j++) {
        const condition = rule.conditions[j];
        const condPath = `${path}.conditions[${j}]`;

        if (!this.isValidTarget(condition.target)) {
          errors.push({ 
            code: 'INVALID_TARGET', 
            message: `Invalid target: ${condition.target}`, 
            path: condPath 
          });
        }
        if (!this.isValidOperator(condition.operator)) {
          errors.push({ 
            code: 'INVALID_OPERATOR', 
            message: `Invalid operator: ${condition.operator}`, 
            path: condPath 
          });
        }
      }

      // Check for duplicate IDs
      const duplicates = policy.rules.filter(r => r.id === rule.id);
      if (duplicates.length > 1) {
        warnings.push({ 
          code: 'DUPLICATE_ID', 
          message: `Duplicate rule ID: ${rule.id}`, 
          path 
        });
      }
    }

    // Validate extends
    if (policy.extends) {
      for (const extendedPolicy of policy.extends) {
        if (!this.policies.has(extendedPolicy) && !BUILT_IN_POLICIES[extendedPolicy]) {
          errors.push({ 
            code: 'UNKNOWN_EXTENDS', 
            message: `Unknown policy to extend: ${extendedPolicy}` 
          });
        }
      }
    }

    return {
      valid: errors.length === 0,
      errors,
      warnings,
    };
  }

  /**
   * Register a custom policy
   */
  registerPolicy(policy: SecurityPolicy): void {
    const validation = this.validatePolicy(policy);
    if (!validation.valid) {
      throw new Error(`Invalid policy: ${validation.errors.map(e => e.message).join(', ')}`);
    }
    this.policies.set(policy.name, policy);
  }

  /**
   * Get a policy by name
   */
  getPolicy(name: string): SecurityPolicy | undefined {
    return this.policies.get(name);
  }

  /**
   * List all available policies
   */
  listPolicies(): string[] {
    return Array.from(this.policies.keys());
  }

  /**
   * Get built-in policy by name
   */
  getBuiltInPolicy(name: string): SecurityPolicy | undefined {
    return BUILT_IN_POLICIES[name];
  }

  /**
   * Create policy from YAML string
   */
  parsePolicy(yamlContent: string): SecurityPolicy {
    // Simple YAML-like parsing (for demonstration)
    // In production, use a proper YAML parser
    const lines = yamlContent.split('\n');
    const policy: Partial<SecurityPolicy> = { rules: [] };
    
    for (const line of lines) {
      const trimmed = line.trim();
      if (trimmed.startsWith('name:')) {
        policy.name = trimmed.substring(5).trim();
      } else if (trimmed.startsWith('version:')) {
        policy.version = trimmed.substring(8).trim();
      } else if (trimmed.startsWith('description:')) {
        policy.description = trimmed.substring(12).trim();
      }
    }

    return policy as SecurityPolicy;
  }

  /**
   * Export policy to YAML
   */
  exportPolicy(policyName: string): string {
    const policy = this.getPolicy(policyName);
    if (!policy) {
      throw new Error(`Policy not found: ${policyName}`);
    }

    const lines: string[] = [];
    lines.push(`name: ${policy.name}`);
    lines.push(`version: ${policy.version}`);
    if (policy.description) {
      lines.push(`description: ${policy.description}`);
    }
    if (policy.extends && policy.extends.length > 0) {
      lines.push(`extends:`);
      for (const ext of policy.extends) {
        lines.push(`  - ${ext}`);
      }
    }
    lines.push('rules:');
    for (const rule of policy.rules) {
      lines.push(`  - id: ${rule.id}`);
      lines.push(`    name: ${rule.name}`);
      lines.push(`    action: ${rule.action}`);
      if (rule.priority !== undefined) {
        lines.push(`    priority: ${rule.priority}`);
      }
      lines.push('    conditions:');
      for (const cond of rule.conditions) {
        lines.push(`      - target: ${cond.target}`);
        lines.push(`        operator: ${cond.operator}`);
        lines.push(`        value: ${cond.value}`);
      }
    }

    return lines.join('\n');
  }

  // ============================================================================
  // Private Methods
  // ============================================================================

  private resolvePolicy(policy: SecurityPolicy): SecurityPolicy {
    if (!policy.extends || policy.extends.length === 0) {
      return policy;
    }

    // Collect rules from extended policies
    const allRules: PolicyRule[] = [];
    const seenIds = new Set<string>();

    // First, add rules from extended policies
    for (const extendedName of policy.extends) {
      const extended = this.policies.get(extendedName) ?? BUILT_IN_POLICIES[extendedName];
      if (extended) {
        const resolved = this.resolvePolicy(extended);
        for (const rule of resolved.rules) {
          if (!seenIds.has(rule.id)) {
            allRules.push(rule);
            seenIds.add(rule.id);
          }
        }
      }
    }

    // Then, add/override with current policy's rules
    for (const rule of policy.rules) {
      const existingIndex = allRules.findIndex(r => r.id === rule.id);
      if (existingIndex >= 0) {
        allRules[existingIndex] = rule;
      } else {
        allRules.push(rule);
      }
    }

    return {
      ...policy,
      rules: allRules,
    };
  }

  private evaluateRule(rule: PolicyRule, scanResult: ScanResult): PolicyRuleMatch | null {
    const matchedConditions: PolicyCondition[] = [];
    const triggeredBy: Vulnerability[] = [];

    for (const condition of rule.conditions) {
      const { matches, vulnerabilities } = this.evaluateCondition(condition, scanResult);
      
      if (!matches) {
        return null; // All conditions must match (AND logic)
      }
      
      matchedConditions.push(condition);
      triggeredBy.push(...vulnerabilities);
    }

    return {
      rule,
      triggeredBy: [...new Set(triggeredBy)], // Deduplicate
      matchedConditions,
      action: rule.action,
    };
  }

  private evaluateCondition(
    condition: PolicyCondition, 
    scanResult: ScanResult
  ): { matches: boolean; vulnerabilities: Vulnerability[] } {
    const { target, operator, value } = condition;
    
    // Handle count-based targets
    if (target.startsWith('count.')) {
      const countTarget = target.substring(6) as Severity | 'total';
      let count: number;
      
      if (countTarget === 'total') {
        const s = scanResult.summary;
        count = s.critical + s.high + s.medium + s.low + s.info;
      } else {
        count = scanResult.summary[countTarget];
      }
      
      return {
        matches: this.compareValues(count, operator, value as number),
        vulnerabilities: [],
      };
    }

    // Handle score target
    if (target === 'score') {
      const s = scanResult.summary;
      const penalty = s.critical * 25 + s.high * 10 + s.medium * 5 + s.low * 2 + s.info * 0.5;
      const score = Math.max(0, Math.min(100, 100 - penalty));
      
      return {
        matches: this.compareValues(score, operator, value as number),
        vulnerabilities: [],
      };
    }

    // Handle vulnerability-level targets
    const matchingVulns: Vulnerability[] = [];
    
    for (const vuln of scanResult.vulnerabilities) {
      let fieldValue: string | undefined;
      
      switch (target) {
        case 'severity':
          fieldValue = vuln.severity;
          break;
        case 'rule':
          fieldValue = vuln.ruleId;
          break;
        case 'owasp':
          fieldValue = vuln.owasp?.join(', ');
          break;
        case 'cwe':
          fieldValue = vuln.cwes?.join(', ');
          break;
        case 'file':
          fieldValue = vuln.location.file;
          break;
        case 'message':
          fieldValue = vuln.description;
          break;
      }

      if (fieldValue && this.compareStringValues(fieldValue, operator, value)) {
        matchingVulns.push(vuln);
      }
    }

    return {
      matches: matchingVulns.length > 0,
      vulnerabilities: matchingVulns,
    };
  }

  private compareValues(actual: number, operator: PolicyOperator, expected: number): boolean {
    switch (operator) {
      case 'equals':
        return actual === expected;
      case 'not_equals':
        return actual !== expected;
      case 'greater_than':
        return actual > expected;
      case 'less_than':
        return actual < expected;
      case 'greater_than_or_equals':
        return actual >= expected;
      case 'less_than_or_equals':
        return actual <= expected;
      default:
        return false;
    }
  }

  private compareStringValues(
    actual: string, 
    operator: PolicyOperator, 
    expected: string | number | string[]
  ): boolean {
    const expectedStr = String(expected);
    
    switch (operator) {
      case 'equals':
        return actual === expectedStr;
      case 'not_equals':
        return actual !== expectedStr;
      case 'contains':
        return actual.includes(expectedStr);
      case 'not_contains':
        return !actual.includes(expectedStr);
      case 'matches':
        return new RegExp(expectedStr).test(actual);
      case 'exists':
        return actual !== undefined && actual !== '';
      case 'not_exists':
        return actual === undefined || actual === '';
      default:
        return false;
    }
  }

  private calculateSummary(matchedRules: PolicyRuleMatch[]): PolicyEvaluationSummary {
    const byAction: Record<PolicyAction, number> = {
      fail: 0,
      warn: 0,
      info: 0,
      ignore: 0,
      require_review: 0,
    };

    for (const match of matchedRules) {
      byAction[match.action]++;
    }

    return {
      byAction,
      failures: byAction.fail,
      warnings: byAction.warn,
      reviewsRequired: byAction.require_review,
    };
  }

  private determineFinalAction(
    matchedRules: PolicyRuleMatch[], 
    settings: PolicySettings
  ): PolicyAction {
    // Priority: fail > require_review > warn > info > ignore
    const actionPriority: PolicyAction[] = ['fail', 'require_review', 'warn', 'info', 'ignore'];
    
    for (const action of actionPriority) {
      if (matchedRules.some(m => m.action === action)) {
        return action;
      }
    }
    
    return settings.defaultAction ?? 'info';
  }

  private generateRecommendations(
    matchedRules: PolicyRuleMatch[], 
    scanResult: ScanResult
  ): string[] {
    const recommendations: string[] = [];

    const failRules = matchedRules.filter(m => m.action === 'fail');
    if (failRules.length > 0) {
      recommendations.push(`Address ${failRules.length} policy violation(s) before proceeding`);
      
      const criticalCount = scanResult.summary.critical;
      if (criticalCount > 0) {
        recommendations.push(`Fix ${criticalCount} critical vulnerability(s) immediately`);
      }
    }

    const reviewRules = matchedRules.filter(m => m.action === 'require_review');
    if (reviewRules.length > 0) {
      recommendations.push(`${reviewRules.length} issue(s) require security team review`);
    }

    if (scanResult.summary.high > 5) {
      recommendations.push('Consider enabling stricter security controls');
    }

    return recommendations;
  }

  private isValidTarget(target: PolicyTarget): boolean {
    const validTargets: PolicyTarget[] = [
      'severity', 'rule', 'owasp', 'cwe', 'file', 'message',
      'count.critical', 'count.high', 'count.medium', 'count.low', 'count.total',
      'score',
    ];
    return validTargets.includes(target);
  }

  private isValidOperator(operator: PolicyOperator): boolean {
    const validOperators: PolicyOperator[] = [
      'equals', 'not_equals', 'greater_than', 'less_than',
      'greater_than_or_equals', 'less_than_or_equals',
      'contains', 'not_contains', 'matches', 'exists', 'not_exists',
    ];
    return validOperators.includes(operator);
  }
}

// ============================================================================
// Factory Functions
// ============================================================================

/**
 * Create a policy engine
 */
export function createPolicyEngine(options?: PolicyEngineOptions): PolicyEngine {
  return new PolicyEngine(options);
}

/**
 * Get a built-in policy
 */
export function getBuiltInPolicy(name: 'default' | 'strict' | 'minimal' | 'enterprise'): SecurityPolicy {
  return BUILT_IN_POLICIES[name];
}
