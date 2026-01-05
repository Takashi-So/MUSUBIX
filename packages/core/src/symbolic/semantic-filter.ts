/**
 * Semantic Code Filter Pipeline
 *
 * Filters LLM-generated code through hallucination detection
 * and constitution enforcement checks.
 *
 * @packageDocumentation
 * @module symbolic
 *
 * @see REQ-SF-001 - Semantic Code Filter
 * @see DES-SYMB-001 §4.1 - SemanticCodeFilterPipeline
 * @see TSK-SYMB-001
 */

import type {
  FilterInput,
  FilterOutput,
  CodeCandidate,
  ConstitutionViolation,
  HallucinationResult,
  ConstitutionReport,
  ConstitutionCheckInput,
  Explanation,
} from './types.js';
import type { HallucinationDetector } from './hallucination-detector.js';
import type { ConstitutionRuleRegistry } from './constitution-registry.js';

/**
 * Configuration for SemanticCodeFilterPipeline
 */
export interface SemanticCodeFilterConfig {
  hallucinationDetector: HallucinationDetector;
  constitutionRegistry: ConstitutionRuleRegistry;
  enableHallucinationCheck?: boolean;
  enableConstitutionCheck?: boolean;
}

/**
 * Semantic Code Filter Pipeline
 *
 * Orchestrates multiple validation checks on LLM-generated code:
 * 1. Hallucination detection (non-existent API/module references)
 * 2. Constitution enforcement (9 articles compliance)
 * 3. EARS consistency validation
 */
export class SemanticCodeFilterPipeline {
  private readonly hallucinationDetector: HallucinationDetector;
  private readonly constitutionRegistry: ConstitutionRuleRegistry;
  private readonly enableHallucinationCheck: boolean;
  private readonly enableConstitutionCheck: boolean;

  constructor(config: SemanticCodeFilterConfig) {
    this.hallucinationDetector = config.hallucinationDetector;
    this.constitutionRegistry = config.constitutionRegistry;
    this.enableHallucinationCheck = config.enableHallucinationCheck ?? true;
    this.enableConstitutionCheck = config.enableConstitutionCheck ?? true;
  }

  /**
   * Filter code candidates through the pipeline
   */
  async filter(input: FilterInput): Promise<FilterOutput> {
    const startTime = Date.now();
    const allViolations: ConstitutionViolation[] = [];
    let hallucinationReport: HallucinationResult | undefined;
    let constitutionReport: ConstitutionReport | undefined;

    // Process each candidate
    for (const candidate of input.candidates) {
      // Step 1: Hallucination detection
      if (this.enableHallucinationCheck) {
        const hallResult = await this.hallucinationDetector.detect(candidate, input.projectContext);
        if (!hallucinationReport) {
          hallucinationReport = hallResult;
        } else {
          // Merge results
          hallucinationReport.hasHallucinations =
            hallucinationReport.hasHallucinations || hallResult.hasHallucinations;
          hallucinationReport.items.push(...hallResult.items);
        }
      }

      // Step 2: Constitution check
      if (this.enableConstitutionCheck) {
        const constInput = this.buildConstitutionInput(candidate, input);
        constitutionReport = await this.constitutionRegistry.generateReport(constInput);
        allViolations.push(
          ...constitutionReport.articleResults.flatMap((r) => r.violations),
        );
      }
    }

    // Determine acceptance
    const hasBlockingViolations = allViolations.some(
      (v) => v.severity === 'critical' || v.severity === 'error',
    );
    const hasHallucinations = hallucinationReport?.hasHallucinations ?? false;
    const accepted = !hasBlockingViolations && !hasHallucinations;

    // Build explanation
    const explanation = this.buildExplanation(
      accepted,
      allViolations,
      hallucinationReport,
      constitutionReport,
      Date.now() - startTime,
    );

    return {
      accepted,
      filteredCandidates: input.candidates,
      violations: allViolations,
      hallucinationReport,
      constitutionReport,
      explanation,
    };
  }

  /**
   * Build constitution check input from code candidate
   */
  private buildConstitutionInput(
    candidate: CodeCandidate,
    input: FilterInput,
  ): ConstitutionCheckInput {
    const symbols = input.projectContext.symbols ?? [];
    const hasLibrary = symbols.some((s) => s.type === 'class' || s.type === 'function');
    const hasCLI = candidate.code.includes('commander') || candidate.code.includes('yargs');
    const hasTests = candidate.code.includes('describe(') || candidate.code.includes('it(');
    const earsReqs = input.requirements?.map((r) => r.id) ?? [];

    return {
      code: candidate.code,
      context: {
        hasLibraryStructure: hasLibrary,
        hasCLI,
        hasTests,
        earsRequirements: earsReqs,
        traceabilityLinks: [],
        hasSteeringReference: candidate.code.includes('steering/') || candidate.code.includes('ADR'),
        documentedPatterns: [],
        hasADR: candidate.code.includes('ADR-'),
        hasQualityGates: true,
      },
      requirements: input.requirements ?? [],
    };
  }

  /**
   * Build explanation for filter output
   */
  private buildExplanation(
    accepted: boolean,
    violations: ConstitutionViolation[],
    hallucinationReport: HallucinationResult | undefined,
    constitutionReport: ConstitutionReport | undefined,
    durationMs: number,
  ): Explanation {
    const summary = accepted
      ? `Code accepted (${durationMs}ms)`
      : `Code rejected: ${violations.length} violations, ${hallucinationReport?.items.length ?? 0} hallucinations`;

    const reasoning: string[] = [
      `Hallucination check: ${hallucinationReport?.hasHallucinations ? 'FAILED' : 'PASSED'}`,
      `Constitution check: ${constitutionReport?.overallPassed ? 'PASSED' : 'FAILED'}`,
      `Violations: ${violations.length}`,
      `Hallucinations: ${hallucinationReport?.items.length ?? 0}`,
    ];

    if (violations.length > 0) {
      reasoning.push('Violations:');
      for (const v of violations.slice(0, 5)) {
        reasoning.push(`  - [${v.article}] ${v.message}`);
      }
    }

    return {
      summary,
      reasoning,
      evidence: [],
      relatedRequirements: ['REQ-SF-001', 'REQ-SF-002', 'REQ-SF-003'],
    };
  }
}

/**
 * Factory function to create a SemanticCodeFilterPipeline
 */
export function createSemanticCodeFilterPipeline(
  config: SemanticCodeFilterConfig,
): SemanticCodeFilterPipeline {
  return new SemanticCodeFilterPipeline(config);
}
