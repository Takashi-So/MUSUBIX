/**
 * Confidence-Based Router
 *
 * Routes LLM outputs based on confidence thresholds
 * to appropriate handlers (accept, verify, regenerate).
 *
 * @packageDocumentation
 * @module symbolic
 *
 * @see REQ-ROUTE-002 - Confidence-Based Routing
 * @see DES-SYMB-001 §4.20 - ConfidenceBasedRouter
 * @see TSK-SYMB-006
 */

import type {
  ConfidenceEstimation,
  RoutingResult,
  RoutingDecision,
  VerificationRequirement,
  Explanation,
  FilterOutput,
} from './types.js';

/**
 * Routing thresholds configuration
 */
export interface RoutingThresholds {
  acceptThreshold: number;
  verifyThreshold: number;
}

/**
 * Router configuration
 */
export interface ConfidenceRouterConfig {
  thresholds: RoutingThresholds;
  maxRegenerationAttempts: number;
  detailedExplanations: boolean;
}

/**
 * Default router configuration
 */
export const DEFAULT_ROUTER_CONFIG: ConfidenceRouterConfig = {
  thresholds: {
    acceptThreshold: 0.8,
    verifyThreshold: 0.5,
  },
  maxRegenerationAttempts: 3,
  detailedExplanations: true,
};

/**
 * Confidence-Based Router
 */
export class ConfidenceBasedRouter {
  private readonly config: ConfidenceRouterConfig;

  constructor(config: Partial<ConfidenceRouterConfig> = {}) {
    this.config = {
      ...DEFAULT_ROUTER_CONFIG,
      ...config,
      thresholds: {
        ...DEFAULT_ROUTER_CONFIG.thresholds,
        ...config.thresholds,
      },
    };
  }

  /**
   * Route a code candidate based on confidence
   */
  route(estimation: ConfidenceEstimation, filterOutput?: FilterOutput): RoutingResult {
    const decision = this.determineDecision(estimation.score, filterOutput);
    const verificationRequirements =
      decision === 'verify' ? this.determineVerificationRequirements(estimation) : [];
    const explanation = this.buildExplanation(decision, estimation, verificationRequirements);

    return {
      decision,
      confidence: estimation.score,
      verificationRequirements,
      explanation,
    };
  }

  private determineDecision(score: number, filterOutput?: FilterOutput): RoutingDecision {
    if (filterOutput) {
      const hasBlockingIssues =
        filterOutput.violations.some((v) => v.severity === 'critical' || v.severity === 'error') ||
        filterOutput.hallucinationReport?.hasHallucinations === true;

      if (hasBlockingIssues && score < this.config.thresholds.verifyThreshold) {
        return 'regenerate';
      }
      if (hasBlockingIssues) {
        return 'verify';
      }
    }

    if (score >= this.config.thresholds.acceptThreshold) {
      return 'accept';
    } else if (score >= this.config.thresholds.verifyThreshold) {
      return 'verify';
    } else {
      return 'regenerate';
    }
  }

  private determineVerificationRequirements(
    estimation: ConfidenceEstimation,
  ): VerificationRequirement[] {
    const requirements: VerificationRequirement[] = [];
    const { breakdown, riskFactors } = estimation;

    if (breakdown.syntactic < 0.8) {
      requirements.push({
        type: 'syntax_check',
        description: 'Verify code syntax is correct',
        priority: 'high',
      });
    }

    if (breakdown.semantic < 0.8) {
      requirements.push({
        type: 'semantic_review',
        description: 'Review semantic correctness and logic',
        priority: 'medium',
      });
    }

    if (breakdown.factual < 0.8) {
      requirements.push({
        type: 'api_verification',
        description: 'Verify all API calls and imports exist',
        priority: 'high',
      });
    }

    if (breakdown.consistency < 0.7) {
      requirements.push({
        type: 'pattern_review',
        description: 'Review adherence to project patterns',
        priority: 'low',
      });
    }

    for (const risk of riskFactors) {
      if (risk.type === 'complexity') {
        requirements.push({
          type: 'test_coverage',
          description: 'Ensure adequate test coverage',
          priority: 'medium',
        });
        break;
      }
    }

    // Deduplicate
    const seen = new Set<string>();
    return requirements.filter((r) => {
      if (seen.has(r.type)) return false;
      seen.add(r.type);
      return true;
    });
  }

  private buildExplanation(
    decision: RoutingDecision,
    estimation: ConfidenceEstimation,
    requirements: VerificationRequirement[],
  ): Explanation {
    const { score, breakdown, riskFactors } = estimation;
    const { acceptThreshold, verifyThreshold } = this.config.thresholds;

    let summary: string;
    if (decision === 'accept') {
      summary = `Accepted: Confidence ${(score * 100).toFixed(0)}% >= ${(acceptThreshold * 100).toFixed(0)}%`;
    } else if (decision === 'verify') {
      summary = `Verification required: Confidence ${(score * 100).toFixed(0)}% between ${(verifyThreshold * 100).toFixed(0)}% and ${(acceptThreshold * 100).toFixed(0)}%`;
    } else {
      summary = `Regeneration recommended: Confidence ${(score * 100).toFixed(0)}% < ${(verifyThreshold * 100).toFixed(0)}%`;
    }

    const reasoning: string[] = [
      `Decision: ${decision.toUpperCase()}`,
      `Overall confidence: ${(score * 100).toFixed(0)}%`,
      `Syntactic: ${(breakdown.syntactic * 100).toFixed(0)}%`,
      `Semantic: ${(breakdown.semantic * 100).toFixed(0)}%`,
      `Factual: ${(breakdown.factual * 100).toFixed(0)}%`,
      `Consistency: ${(breakdown.consistency * 100).toFixed(0)}%`,
    ];

    if (riskFactors.length > 0) {
      reasoning.push('Risk factors:');
      for (const risk of riskFactors) {
        reasoning.push(`  - ${risk.description}`);
      }
    }

    if (requirements.length > 0) {
      reasoning.push('Verification requirements:');
      for (const req of requirements) {
        reasoning.push(`  - [${req.priority}] ${req.type}: ${req.description}`);
      }
    }

    return {
      summary,
      reasoning,
      evidence: riskFactors.map((r) => ({
        type: 'rule_match' as const,
        description: r.description,
        artifacts: [],
        confidence: 1 - r.impact,
      })),
      relatedRequirements: ['REQ-ROUTE-001', 'REQ-ROUTE-002'],
    };
  }

  getThresholds(): RoutingThresholds {
    return { ...this.config.thresholds };
  }

  updateThresholds(thresholds: Partial<RoutingThresholds>): void {
    Object.assign(this.config.thresholds, thresholds);
  }

  isRegenerationLimitReached(attempts: number): boolean {
    return attempts >= this.config.maxRegenerationAttempts;
  }
}

/**
 * Factory function
 */
export function createConfidenceBasedRouter(
  config?: Partial<ConfidenceRouterConfig>,
): ConfidenceBasedRouter {
  return new ConfidenceBasedRouter(config);
}
