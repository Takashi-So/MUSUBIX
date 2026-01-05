/**
 * Quality Gate Validator for Neuro-Symbolic Integration
 *
 * TSK-SYMB-019: 品質ゲート（承認条件）検証タスク
 *
 * Validates that all acceptance criteria defined in DES-SYMB-001 Section 7.2 are met
 * before transitioning to implementation phase.
 *
 * @module quality-gate
 * @implements REQ-CONST-004, REQ-CONST-010
 */

import type { Explanation, Evidence } from './types.js';

// ============================================================
// Quality Gate Types
// ============================================================

/**
 * Individual check result
 */
export interface QualityCheckResult {
  /** Check identifier */
  checkId: string;
  /** Check category */
  category: 'traceability' | 'non-functional' | 'security' | 'constitution';
  /** Check name */
  name: string;
  /** Pass/fail status */
  passed: boolean;
  /** Related requirement IDs */
  requirementIds: string[];
  /** Detailed message */
  message: string;
  /** Evidence supporting the result */
  evidence: Evidence[];
  /** Severity if failed */
  severity?: 'blocker' | 'critical' | 'major' | 'minor';
}

/**
 * Quality gate validation result
 */
export interface QualityGateResult {
  /** Overall pass/fail */
  passed: boolean;
  /** Gate name */
  gateName: string;
  /** Phase being validated */
  phase: 'requirements' | 'design' | 'implementation' | 'testing' | 'deployment';
  /** Individual check results */
  checks: QualityCheckResult[];
  /** Summary statistics */
  summary: {
    totalChecks: number;
    passedChecks: number;
    failedChecks: number;
    blockerCount: number;
    criticalCount: number;
  };
  /** Validation timestamp */
  validatedAt: string;
  /** Explanation of the validation */
  explanation: Explanation;
}

/**
 * Traceability coverage data
 */
export interface TraceabilityCoverage {
  /** Requirement ID */
  requirementId: string;
  /** Design document IDs that cover this requirement */
  designIds: string[];
  /** Task IDs that implement this requirement */
  taskIds: string[];
  /** Test IDs that verify this requirement */
  testIds: string[];
  /** Coverage percentage */
  coveragePercent: number;
}

/**
 * Quality gate configuration
 */
export interface QualityGateConfig {
  /** Minimum design coverage percentage */
  minDesignCoverage: number;
  /** Minimum test coverage percentage */
  minTestCoverage: number;
  /** Required Constitution articles */
  requiredConstitutionArticles: string[];
  /** Performance budget must be defined */
  requirePerformanceBudget: boolean;
  /** Audit logging must be configured */
  requireAuditLogging: boolean;
  /** Security policies must be defined */
  requireSecurityPolicies: boolean;
}

// ============================================================
// Default Configuration
// ============================================================

const DEFAULT_CONFIG: QualityGateConfig = {
  minDesignCoverage: 100,
  minTestCoverage: 80,
  requiredConstitutionArticles: ['I', 'II', 'III', 'IV', 'V', 'VI', 'VII', 'VIII', 'IX'],
  requirePerformanceBudget: true,
  requireAuditLogging: true,
  requireSecurityPolicies: true,
};

// ============================================================
// Quality Gate Validator
// ============================================================

/**
 * Quality Gate Validator
 *
 * Validates acceptance criteria defined in DES-SYMB-001 Section 7.2:
 * - Traceability: 100% design coverage for all 27 requirements
 * - Non-functional: Performance budget, extensibility, explainability
 * - Security/Audit: Masking policy, tamper detection
 * - Constitution: All 9 articles compliance
 */
export class QualityGateValidator {
  private readonly config: QualityGateConfig;

  constructor(config: Partial<QualityGateConfig> = {}) {
    this.config = { ...DEFAULT_CONFIG, ...config };
  }

  /**
   * Validate all quality gate criteria
   */
  validate(
    traceability: TraceabilityCoverage[],
    components: ComponentValidation,
  ): QualityGateResult {
    const checks: QualityCheckResult[] = [];
    const startTime = Date.now();

    // 1. Traceability checks
    checks.push(...this.validateTraceability(traceability));

    // 2. Non-functional checks
    checks.push(...this.validateNonFunctional(components));

    // 3. Security/Audit checks
    checks.push(...this.validateSecurityAudit(components));

    // 4. Constitution compliance checks
    checks.push(...this.validateConstitution(components));

    // Calculate summary
    const passedChecks = checks.filter((c) => c.passed).length;
    const failedChecks = checks.filter((c) => !c.passed);
    const blockerCount = failedChecks.filter((c) => c.severity === 'blocker').length;
    const criticalCount = failedChecks.filter((c) => c.severity === 'critical').length;

    const passed = blockerCount === 0 && criticalCount === 0;

    return {
      passed,
      gateName: 'DES-SYMB-001 Implementation Gate',
      phase: 'design',
      checks,
      summary: {
        totalChecks: checks.length,
        passedChecks,
        failedChecks: failedChecks.length,
        blockerCount,
        criticalCount,
      },
      validatedAt: new Date().toISOString(),
      explanation: this.generateExplanation(checks, passed, Date.now() - startTime),
    };
  }

  /**
   * Validate traceability coverage
   */
  private validateTraceability(traceability: TraceabilityCoverage[]): QualityCheckResult[] {
    const checks: QualityCheckResult[] = [];

    // Check 1: Design coverage for all requirements
    const designCoverage = traceability.filter((t) => t.designIds.length > 0);
    const designCoveragePercent =
      traceability.length > 0 ? (designCoverage.length / traceability.length) * 100 : 0;

    checks.push({
      checkId: 'QG-TRACE-001',
      category: 'traceability',
      name: 'Design Coverage',
      passed: designCoveragePercent >= this.config.minDesignCoverage,
      requirementIds: ['REQ-CONST-004', 'REQ-CONST-005'],
      message:
        designCoveragePercent >= this.config.minDesignCoverage
          ? `Design coverage is ${designCoveragePercent.toFixed(1)}% (required: ${this.config.minDesignCoverage}%)`
          : `Design coverage is only ${designCoveragePercent.toFixed(1)}% (required: ${this.config.minDesignCoverage}%)`,
      evidence: [
        {
          type: 'traceability',
          source: 'TraceabilityMatrix',
          content: `Covered: ${designCoverage.length}/${traceability.length} requirements`,
          confidence: 1.0,
        },
      ],
      severity: designCoveragePercent >= this.config.minDesignCoverage ? undefined : 'blocker',
    });

    // Check 2: Task decomposition coverage
    const taskCoverage = traceability.filter((t) => t.taskIds.length > 0);
    const taskCoveragePercent =
      traceability.length > 0 ? (taskCoverage.length / traceability.length) * 100 : 0;

    checks.push({
      checkId: 'QG-TRACE-002',
      category: 'traceability',
      name: 'Task Decomposition',
      passed: taskCoveragePercent >= 80,
      requirementIds: ['REQ-CONST-004'],
      message: `Task coverage is ${taskCoveragePercent.toFixed(1)}%`,
      evidence: [
        {
          type: 'traceability',
          source: 'TaskMatrix',
          content: `Tasks defined: ${taskCoverage.length}/${traceability.length} requirements`,
          confidence: 1.0,
        },
      ],
      severity: taskCoveragePercent >= 80 ? undefined : 'critical',
    });

    // Check 3: Uncovered requirements
    const uncovered = traceability.filter((t) => t.coveragePercent < 100);
    checks.push({
      checkId: 'QG-TRACE-003',
      category: 'traceability',
      name: 'Requirement Coverage Gaps',
      passed: uncovered.length === 0,
      requirementIds: uncovered.map((u) => u.requirementId),
      message:
        uncovered.length === 0
          ? 'All requirements have full traceability'
          : `${uncovered.length} requirements have coverage gaps`,
      evidence: uncovered.map((u) => ({
        type: 'traceability' as const,
        source: u.requirementId,
        content: `Coverage: ${u.coveragePercent}%`,
        confidence: 1.0,
      })),
      severity: uncovered.length === 0 ? undefined : 'major',
    });

    return checks;
  }

  /**
   * Validate non-functional requirements
   */
  private validateNonFunctional(components: ComponentValidation): QualityCheckResult[] {
    const checks: QualityCheckResult[] = [];

    // Check 1: Performance budget defined
    checks.push({
      checkId: 'QG-NFR-001',
      category: 'non-functional',
      name: 'Performance Budget',
      passed: components.performanceBudgetDefined,
      requirementIds: ['REQ-NFR-001'],
      message: components.performanceBudgetDefined
        ? 'Performance budget is defined with step-level budgets'
        : 'Performance budget is not defined',
      evidence: [
        {
          type: 'artifact',
          source: 'PerformanceBudget',
          content: components.performanceBudgetDefined
            ? 'Step budgets: parse, vc_gen, z3, explain, audit'
            : 'Missing',
          confidence: 1.0,
        },
      ],
      severity: components.performanceBudgetDefined ? undefined : 'blocker',
    });

    // Check 2: Extensibility via configuration
    checks.push({
      checkId: 'QG-NFR-002',
      category: 'non-functional',
      name: 'Extensibility',
      passed: components.extensibleConfigDefined,
      requirementIds: ['REQ-NFR-002', 'REQ-CONST-001'],
      message: components.extensibleConfigDefined
        ? 'Rule configuration system is extensible via YAML/JSON'
        : 'Extensibility mechanism is not defined',
      evidence: [
        {
          type: 'artifact',
          source: 'ExtensibleRuleConfig',
          content: components.extensibleConfigDefined
            ? 'Schema validation, YAML/JSON support, ArtifactRef tracking'
            : 'Missing',
          confidence: 1.0,
        },
      ],
      severity: components.extensibleConfigDefined ? undefined : 'critical',
    });

    // Check 3: Explainability
    checks.push({
      checkId: 'QG-NFR-003',
      category: 'non-functional',
      name: 'Explainability',
      passed: components.explanationGeneratorDefined,
      requirementIds: ['REQ-NFR-003', 'REQ-CONST-005'],
      message: components.explanationGeneratorDefined
        ? 'All decisions have attached explanations'
        : 'Explanation generation is not implemented',
      evidence: [
        {
          type: 'artifact',
          source: 'ExplanationGenerator',
          content: components.explanationGeneratorDefined
            ? 'Reasoning chains with evidence'
            : 'Missing',
          confidence: 1.0,
        },
      ],
      severity: components.explanationGeneratorDefined ? undefined : 'critical',
    });

    return checks;
  }

  /**
   * Validate security and audit requirements
   */
  private validateSecurityAudit(components: ComponentValidation): QualityCheckResult[] {
    const checks: QualityCheckResult[] = [];

    // Check 1: Sensitive data masking
    checks.push({
      checkId: 'QG-SEC-001',
      category: 'security',
      name: 'Sensitive Data Masking',
      passed: components.securityMaskingDefined,
      requirementIds: ['REQ-NFR-005'],
      message: components.securityMaskingDefined
        ? 'Sensitive data masking policy is defined'
        : 'Sensitive data masking is not defined',
      evidence: [
        {
          type: 'artifact',
          source: 'SecurityPolicy',
          content: components.securityMaskingDefined ? 'Pattern-based masking enabled' : 'Missing',
          confidence: 1.0,
        },
      ],
      severity: components.securityMaskingDefined ? undefined : 'critical',
    });

    // Check 2: Audit logging with tamper detection
    checks.push({
      checkId: 'QG-SEC-002',
      category: 'security',
      name: 'Audit Logging',
      passed: components.auditLoggingDefined,
      requirementIds: ['REQ-NFR-006'],
      message: components.auditLoggingDefined
        ? 'Audit logging with hash-chain tamper detection is configured'
        : 'Audit logging is not configured',
      evidence: [
        {
          type: 'artifact',
          source: 'AuditLogger',
          content: components.auditLoggingDefined
            ? 'SHA-256 hash chain, checkpoint intervals, retention policy'
            : 'Missing',
          confidence: 1.0,
        },
      ],
      severity: components.auditLoggingDefined ? undefined : 'blocker',
    });

    return checks;
  }

  /**
   * Validate Constitution compliance
   */
  private validateConstitution(components: ComponentValidation): QualityCheckResult[] {
    const checks: QualityCheckResult[] = [];

    // Map of Constitution articles to their checks
    const articleChecks: Array<{
      article: string;
      name: string;
      check: () => boolean;
      requirementIds: string[];
    }> = [
      {
        article: 'I',
        name: 'Library-First',
        check: () => components.libraryFirstCompliant,
        requirementIds: ['REQ-CONST-001'],
      },
      {
        article: 'II',
        name: 'CLI Interface',
        check: () => components.cliInterfaceDefined,
        requirementIds: ['REQ-CONST-002'],
      },
      {
        article: 'III',
        name: 'Test-First',
        check: () => components.testFirstCompliant,
        requirementIds: ['REQ-CONST-003'],
      },
      {
        article: 'IV',
        name: 'EARS Format',
        check: () => components.earsFormatCompliant,
        requirementIds: ['REQ-CONST-004'],
      },
      {
        article: 'V',
        name: 'Traceability',
        check: () => components.traceabilityCompliant,
        requirementIds: ['REQ-CONST-005'],
      },
      {
        article: 'VI',
        name: 'Project Memory',
        check: () => components.projectMemoryCompliant,
        requirementIds: ['REQ-CONST-006'],
      },
      {
        article: 'VII',
        name: 'Design Patterns',
        check: () => components.designPatternsDocumented,
        requirementIds: ['REQ-CONST-007'],
      },
      {
        article: 'VIII',
        name: 'Decision Records',
        check: () => components.adrCompliant,
        requirementIds: ['REQ-CONST-008'],
      },
      {
        article: 'IX',
        name: 'Quality Gates',
        check: () => components.qualityGatesConfigured,
        requirementIds: ['REQ-CONST-009', 'REQ-CONST-010'],
      },
    ];

    for (const articleCheck of articleChecks) {
      const passed = articleCheck.check();
      checks.push({
        checkId: `QG-CONST-${articleCheck.article}`,
        category: 'constitution',
        name: `Article ${articleCheck.article}: ${articleCheck.name}`,
        passed,
        requirementIds: articleCheck.requirementIds,
        message: passed
          ? `Constitution Article ${articleCheck.article} (${articleCheck.name}) is compliant`
          : `Constitution Article ${articleCheck.article} (${articleCheck.name}) is NOT compliant`,
        evidence: [
          {
            type: 'constitution',
            source: `Article ${articleCheck.article}`,
            content: passed ? 'Compliant' : 'Non-compliant',
            confidence: 1.0,
          },
        ],
        severity: passed ? undefined : articleCheck.article === 'V' ? 'blocker' : 'critical',
      });
    }

    return checks;
  }

  /**
   * Generate explanation for the quality gate result
   */
  private generateExplanation(
    checks: QualityCheckResult[],
    passed: boolean,
    durationMs: number,
  ): Explanation {
    const failed = checks.filter((c) => !c.passed);
    const blockers = failed.filter((c) => c.severity === 'blocker');
    const criticals = failed.filter((c) => c.severity === 'critical');

    const reasoning: string[] = [];

    if (passed) {
      reasoning.push('All quality gate checks passed.');
      reasoning.push(`${checks.length} checks validated successfully.`);
    } else {
      if (blockers.length > 0) {
        reasoning.push(`${blockers.length} blocker issue(s) must be resolved:`);
        blockers.forEach((b) => reasoning.push(`  - ${b.name}: ${b.message}`));
      }
      if (criticals.length > 0) {
        reasoning.push(`${criticals.length} critical issue(s) should be addressed:`);
        criticals.forEach((c) => reasoning.push(`  - ${c.name}: ${c.message}`));
      }
    }

    return {
      summary: passed
        ? 'Quality gate validation PASSED. Ready for implementation phase.'
        : `Quality gate validation FAILED. ${blockers.length} blocker(s), ${criticals.length} critical issue(s).`,
      reasoning,
      evidence: checks.flatMap((c) => c.evidence),
      confidence: passed ? 1.0 : 0.0,
      generatedAt: new Date().toISOString(),
      metadata: {
        durationMs,
        checksRun: checks.length,
        phase: 'design-to-implementation',
      },
    };
  }

  /**
   * Generate approval report
   */
  generateApprovalReport(result: QualityGateResult): string {
    const lines: string[] = [];

    lines.push('# Quality Gate Approval Report');
    lines.push('');
    lines.push(`**Gate**: ${result.gateName}`);
    lines.push(`**Phase**: ${result.phase}`);
    lines.push(`**Status**: ${result.passed ? '✅ PASSED' : '❌ FAILED'}`);
    lines.push(`**Validated At**: ${result.validatedAt}`);
    lines.push('');

    lines.push('## Summary');
    lines.push('');
    lines.push(`| Metric | Value |`);
    lines.push(`|--------|-------|`);
    lines.push(`| Total Checks | ${result.summary.totalChecks} |`);
    lines.push(`| Passed | ${result.summary.passedChecks} |`);
    lines.push(`| Failed | ${result.summary.failedChecks} |`);
    lines.push(`| Blockers | ${result.summary.blockerCount} |`);
    lines.push(`| Critical | ${result.summary.criticalCount} |`);
    lines.push('');

    // Group checks by category
    const categories = ['traceability', 'non-functional', 'security', 'constitution'] as const;

    for (const category of categories) {
      const categoryChecks = result.checks.filter((c) => c.category === category);
      if (categoryChecks.length === 0) continue;

      lines.push(`## ${this.capitalizeCategory(category)} Checks`);
      lines.push('');
      lines.push(`| Check | Status | Requirements | Message |`);
      lines.push(`|-------|--------|--------------|---------|`);

      for (const check of categoryChecks) {
        const status = check.passed ? '✅' : check.severity === 'blocker' ? '🚫' : '⚠️';
        lines.push(
          `| ${check.name} | ${status} | ${check.requirementIds.join(', ')} | ${check.message} |`,
        );
      }

      lines.push('');
    }

    lines.push('## Explanation');
    lines.push('');
    lines.push(result.explanation.summary);
    lines.push('');
    if (result.explanation.reasoning.length > 0) {
      lines.push('### Reasoning');
      lines.push('');
      for (const reason of result.explanation.reasoning) {
        lines.push(`- ${reason}`);
      }
    }

    lines.push('');
    lines.push('## Approval Record');
    lines.push('');
    lines.push('| Role | Name | Date | Signature |');
    lines.push('|------|------|------|-----------|');
    lines.push('| Validator | AI Agent | ' + new Date().toISOString().split('T')[0] + ' | Auto |');
    lines.push('| Reviewer | | | |');
    lines.push('| Approver | | | |');
    lines.push('');
    lines.push('---');
    lines.push('');
    lines.push('**Generated by**: MUSUBIX Quality Gate Validator');
    lines.push(`**Document ID**: QG-RPT-${Date.now()}`);

    return lines.join('\n');
  }

  private capitalizeCategory(category: string): string {
    const names: Record<string, string> = {
      traceability: 'Traceability',
      'non-functional': 'Non-Functional',
      security: 'Security & Audit',
      constitution: 'Constitution',
    };
    return names[category] || category;
  }
}

// ============================================================
// Component Validation Interface
// ============================================================

/**
 * Component validation status
 */
export interface ComponentValidation {
  /** Performance budget is defined */
  performanceBudgetDefined: boolean;
  /** Extensible config system is defined */
  extensibleConfigDefined: boolean;
  /** Explanation generator is defined */
  explanationGeneratorDefined: boolean;
  /** Security masking policy is defined */
  securityMaskingDefined: boolean;
  /** Audit logging with tamper detection is defined */
  auditLoggingDefined: boolean;
  /** Library-first architecture compliant */
  libraryFirstCompliant: boolean;
  /** CLI interface is defined */
  cliInterfaceDefined: boolean;
  /** Test-first development followed */
  testFirstCompliant: boolean;
  /** EARS format used for requirements */
  earsFormatCompliant: boolean;
  /** Full traceability maintained */
  traceabilityCompliant: boolean;
  /** Project memory (steering/) referenced */
  projectMemoryCompliant: boolean;
  /** Design patterns documented */
  designPatternsDocumented: boolean;
  /** ADR records maintained */
  adrCompliant: boolean;
  /** Quality gates configured */
  qualityGatesConfigured: boolean;
}

/**
 * Create component validation from current project state
 */
export function createComponentValidation(options: Partial<ComponentValidation>): ComponentValidation {
  return {
    performanceBudgetDefined: options.performanceBudgetDefined ?? false,
    extensibleConfigDefined: options.extensibleConfigDefined ?? false,
    explanationGeneratorDefined: options.explanationGeneratorDefined ?? false,
    securityMaskingDefined: options.securityMaskingDefined ?? false,
    auditLoggingDefined: options.auditLoggingDefined ?? false,
    libraryFirstCompliant: options.libraryFirstCompliant ?? false,
    cliInterfaceDefined: options.cliInterfaceDefined ?? false,
    testFirstCompliant: options.testFirstCompliant ?? false,
    earsFormatCompliant: options.earsFormatCompliant ?? false,
    traceabilityCompliant: options.traceabilityCompliant ?? false,
    projectMemoryCompliant: options.projectMemoryCompliant ?? false,
    designPatternsDocumented: options.designPatternsDocumented ?? false,
    adrCompliant: options.adrCompliant ?? false,
    qualityGatesConfigured: options.qualityGatesConfigured ?? false,
  };
}
