/**
 * Constitution Rule Registry
 *
 * Manages and enforces the 9 Constitution Articles.
 *
 * @packageDocumentation
 * @module symbolic
 *
 * @see REQ-CONST-001〜009 - Constitution Articles
 * @see DES-SYMB-001 §4.3 - ConstitutionRuleRegistry
 * @see TSK-SYMB-003, TSK-SYMB-004
 */

import type {
  ConstitutionRule,
  ConstitutionCheckInput,
  ConstitutionCheckResult,
  ConstitutionReport,
  ConstitutionArticle,
  ConstitutionViolation,
  Explanation,
} from './types.js';

/**
 * Configuration for ConstitutionRuleRegistry
 */
export interface ConstitutionRegistryConfig {
  rules?: ConstitutionRule[];
  strictMode?: boolean;
}

// ============================================================================
// Article Validators
// ============================================================================

/**
 * Article I: Library-First
 * All functionality must begin as independent library components
 */
export async function checkArticleI(input: ConstitutionCheckInput): Promise<ConstitutionCheckResult> {
  const violations: ConstitutionViolation[] = [];

  if (!input.context.hasLibraryStructure) {
    violations.push({
      article: 'I',
      severity: 'error',
      message: 'Code does not follow library-first architecture',
      suggestion: 'Structure code as reusable library components before integration',
    });
  }

  return {
    passed: violations.length === 0,
    violations,
    explanation: buildArticleExplanation('I', 'Library-First', violations),
  };
}

/**
 * Article II: CLI Interface
 * All libraries must expose CLI interface
 */
export async function checkArticleII(input: ConstitutionCheckInput): Promise<ConstitutionCheckResult> {
  const violations: ConstitutionViolation[] = [];

  if (input.context.hasLibraryStructure && !input.context.hasCLI) {
    violations.push({
      article: 'II',
      severity: 'warning',
      message: 'Library does not expose CLI interface',
      suggestion: 'Add CLI commands using commander or similar',
    });
  }

  return {
    passed: violations.length === 0,
    violations,
    explanation: buildArticleExplanation('II', 'CLI Interface', violations),
  };
}

/**
 * Article III: Test-First
 * Red-Green-Blue cycle for test-driven development
 */
export async function checkArticleIII(input: ConstitutionCheckInput): Promise<ConstitutionCheckResult> {
  const violations: ConstitutionViolation[] = [];

  if (!input.context.hasTests) {
    violations.push({
      article: 'III',
      severity: 'error',
      message: 'Code does not have associated tests',
      suggestion: 'Write tests first following Red-Green-Blue cycle',
    });
  }

  return {
    passed: violations.length === 0,
    violations,
    explanation: buildArticleExplanation('III', 'Test-First', violations),
  };
}

/**
 * Article IV: EARS Format
 * Requirements must be in EARS format
 */
export async function checkArticleIV(input: ConstitutionCheckInput): Promise<ConstitutionCheckResult> {
  const violations: ConstitutionViolation[] = [];

  if (input.context.earsRequirements.length === 0) {
    violations.push({
      article: 'IV',
      severity: 'warning',
      message: 'No EARS-formatted requirements found',
      suggestion: 'Define requirements using EARS patterns (Ubiquitous, Event-driven, etc.)',
    });
  }

  return {
    passed: violations.length === 0,
    violations,
    explanation: buildArticleExplanation('IV', 'EARS Format', violations),
  };
}

/**
 * Article V: Traceability
 * 100% traceability between requirements, design, code, and tests
 */
export async function checkArticleV(input: ConstitutionCheckInput): Promise<ConstitutionCheckResult> {
  const violations: ConstitutionViolation[] = [];

  if (input.context.traceabilityLinks.length === 0 && input.context.earsRequirements.length > 0) {
    violations.push({
      article: 'V',
      severity: 'error',
      message: 'Traceability links missing between artifacts',
      suggestion: 'Add traceability links (REQ-* → DES-* → TSK-*)',
    });
  }

  return {
    passed: violations.length === 0,
    violations,
    explanation: buildArticleExplanation('V', 'Traceability', violations),
  };
}

/**
 * Article VI: Project Memory
 * Reference steering/ before making decisions
 */
export async function checkArticleVI(input: ConstitutionCheckInput): Promise<ConstitutionCheckResult> {
  const violations: ConstitutionViolation[] = [];

  if (!input.context.hasSteeringReference) {
    violations.push({
      article: 'VI',
      severity: 'info',
      message: 'No reference to steering/ project memory',
      suggestion: 'Review steering/ documents before making architectural decisions',
    });
  }

  return {
    passed: violations.length === 0,
    violations,
    explanation: buildArticleExplanation('VI', 'Project Memory', violations),
  };
}

/**
 * Article VII: Design Patterns
 * Document applied design patterns
 */
export async function checkArticleVII(input: ConstitutionCheckInput): Promise<ConstitutionCheckResult> {
  const violations: ConstitutionViolation[] = [];

  if (input.context.documentedPatterns.length === 0) {
    violations.push({
      article: 'VII',
      severity: 'info',
      message: 'No documented design patterns',
      suggestion: 'Document applied design patterns (Repository, Service, etc.)',
    });
  }

  return {
    passed: violations.length === 0,
    violations,
    explanation: buildArticleExplanation('VII', 'Design Patterns', violations),
  };
}

/**
 * Article VIII: Decision Records
 * Record all decisions as ADRs
 */
export async function checkArticleVIII(input: ConstitutionCheckInput): Promise<ConstitutionCheckResult> {
  const violations: ConstitutionViolation[] = [];

  if (!input.context.hasADR) {
    violations.push({
      article: 'VIII',
      severity: 'info',
      message: 'No Architecture Decision Records (ADR) found',
      suggestion: 'Create ADR for significant architectural decisions',
    });
  }

  return {
    passed: violations.length === 0,
    violations,
    explanation: buildArticleExplanation('VIII', 'Decision Records', violations),
  };
}

/**
 * Article IX: Quality Gates
 * Quality verification before phase transitions
 */
export async function checkArticleIX(input: ConstitutionCheckInput): Promise<ConstitutionCheckResult> {
  const violations: ConstitutionViolation[] = [];

  if (!input.context.hasQualityGates) {
    violations.push({
      article: 'IX',
      severity: 'warning',
      message: 'Quality gates not configured',
      suggestion: 'Set up quality gates for phase transitions',
    });
  }

  return {
    passed: violations.length === 0,
    violations,
    explanation: buildArticleExplanation('IX', 'Quality Gates', violations),
  };
}

/**
 * Build explanation for article check
 */
function buildArticleExplanation(
  article: ConstitutionArticle,
  name: string,
  violations: ConstitutionViolation[],
): Explanation {
  const passed = violations.length === 0;
  return {
    summary: passed
      ? `Article ${article} (${name}): PASSED`
      : `Article ${article} (${name}): ${violations.length} violation(s)`,
    reasoning: violations.map((v) => v.message),
    evidence: violations.map((v) => ({
      type: 'rule_match' as const,
      description: v.message,
      artifacts: [],
      confidence: 1.0,
    })),
    relatedRequirements: [`REQ-CONST-00${article === 'IX' ? '9' : article.charCodeAt(0) - 'I'.charCodeAt(0) + 1}`],
  };
}

// ============================================================================
// Default Rules
// ============================================================================

/**
 * Default constitution rules (all 9 articles)
 */
export const DEFAULT_CONSTITUTION_RULES: ConstitutionRule[] = [
  { article: 'I', name: 'Library-First', description: 'All functionality begins as independent library', validator: checkArticleI },
  { article: 'II', name: 'CLI Interface', description: 'All libraries expose CLI interface', validator: checkArticleII },
  { article: 'III', name: 'Test-First', description: 'Red-Green-Blue TDD cycle', validator: checkArticleIII },
  { article: 'IV', name: 'EARS Format', description: 'Requirements in EARS format', validator: checkArticleIV },
  { article: 'V', name: 'Traceability', description: '100% artifact traceability', validator: checkArticleV },
  { article: 'VI', name: 'Project Memory', description: 'Reference steering/ before decisions', validator: checkArticleVI },
  { article: 'VII', name: 'Design Patterns', description: 'Document applied patterns', validator: checkArticleVII },
  { article: 'VIII', name: 'Decision Records', description: 'Record decisions as ADRs', validator: checkArticleVIII },
  { article: 'IX', name: 'Quality Gates', description: 'Quality verification at phase transitions', validator: checkArticleIX },
];

// ============================================================================
// ConstitutionRuleRegistry
// ============================================================================

/**
 * Constitution Rule Registry
 *
 * Manages and enforces the 9 Constitution Articles
 */
export class ConstitutionRuleRegistry {
  private readonly rules: Map<ConstitutionArticle, ConstitutionRule>;
  private readonly strictMode: boolean;

  constructor(config: ConstitutionRegistryConfig = {}) {
    this.rules = new Map();
    this.strictMode = config.strictMode ?? false;

    const rulesToUse = config.rules ?? DEFAULT_CONSTITUTION_RULES;
    for (const rule of rulesToUse) {
      this.rules.set(rule.article, rule);
    }
  }

  /**
   * Get number of rules
   */
  get ruleCount(): number {
    return this.rules.size;
  }

  /**
   * Get a rule by article
   */
  getRule(article: ConstitutionArticle): ConstitutionRule | undefined {
    return this.rules.get(article);
  }

  /**
   * Check code against all rules
   */
  async check(input: ConstitutionCheckInput): Promise<ConstitutionCheckResult> {
    const allViolations: ConstitutionViolation[] = [];

    for (const rule of this.rules.values()) {
      const result = await rule.validator(input);
      allViolations.push(...result.violations);
    }

    const passed = this.strictMode
      ? allViolations.length === 0
      : !allViolations.some((v) => v.severity === 'critical' || v.severity === 'error');

    return {
      passed,
      violations: allViolations,
      explanation: {
        summary: passed
          ? 'All constitution checks passed'
          : `Constitution check failed: ${allViolations.length} violation(s)`,
        reasoning: allViolations.map((v) => `[${v.article}] ${v.message}`),
        evidence: [],
        relatedRequirements: ['REQ-CONST-001'],
      },
    };
  }

  /**
   * Generate detailed report
   */
  async generateReport(input: ConstitutionCheckInput): Promise<ConstitutionReport> {
    const articleResults: Array<{
      article: ConstitutionArticle;
      passed: boolean;
      violations: ConstitutionViolation[];
    }> = [];

    for (const [article, rule] of this.rules) {
      const result = await rule.validator(input);
      articleResults.push({
        article,
        passed: result.passed,
        violations: result.violations,
      });
    }

    const overallPassed = this.strictMode
      ? articleResults.every((r) => r.passed)
      : !articleResults.some((r) =>
          r.violations.some((v) => v.severity === 'critical' || v.severity === 'error'),
        );

    return {
      overallPassed,
      articleResults,
      explanation: {
        summary: overallPassed
          ? 'Constitution compliance: PASSED'
          : 'Constitution compliance: FAILED',
        reasoning: articleResults.map(
          (r) => `Article ${r.article}: ${r.passed ? 'PASSED' : 'FAILED'}`,
        ),
        evidence: [],
        relatedRequirements: ['REQ-CONST-001'],
      },
    };
  }
}

/**
 * Factory function
 */
export function createConstitutionRuleRegistry(
  config?: ConstitutionRegistryConfig,
): ConstitutionRuleRegistry {
  return new ConstitutionRuleRegistry(config);
}
