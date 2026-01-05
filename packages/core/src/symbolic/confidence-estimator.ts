/**
 * Confidence Estimator
 *
 * Estimates confidence scores for LLM outputs with 4-aspect breakdown
 * and risk factor identification.
 *
 * @packageDocumentation
 * @module symbolic
 *
 * @see REQ-ROUTE-001 - Confidence Estimation
 * @see DES-SYMB-001 §4.19 - ConfidenceEstimator
 * @see TSK-SYMB-005
 */

import type {
  ConfidenceEstimation,
  ConfidenceBreakdown,
  RiskFactor,
  Explanation,
  CodeCandidate,
  ProjectContext,
} from './types.js';

/**
 * Configuration for ConfidenceEstimator
 */
export interface ConfidenceEstimatorConfig {
  syntacticWeight: number;
  semanticWeight: number;
  factualWeight: number;
  consistencyWeight: number;
  lowConfidenceThreshold: number;
}

/**
 * Default configuration
 */
export const DEFAULT_CONFIDENCE_CONFIG: ConfidenceEstimatorConfig = {
  syntacticWeight: 0.25,
  semanticWeight: 0.25,
  factualWeight: 0.25,
  consistencyWeight: 0.25,
  lowConfidenceThreshold: 0.5,
};

/**
 * Confidence Estimator
 *
 * Estimates confidence in LLM outputs using 4 aspects:
 * - Syntactic: Code syntax correctness
 * - Semantic: Semantic meaning correctness
 * - Factual: API/function existence accuracy
 * - Consistency: Context consistency
 */
export class ConfidenceEstimator {
  private readonly config: ConfidenceEstimatorConfig;

  constructor(config: Partial<ConfidenceEstimatorConfig> = {}) {
    this.config = { ...DEFAULT_CONFIDENCE_CONFIG, ...config };
  }

  /**
   * Estimate confidence for a code candidate
   */
  async estimate(
    candidate: CodeCandidate,
    context: ProjectContext,
    hallucinations: number = 0,
  ): Promise<ConfidenceEstimation> {
    const syntactic = await this.estimateSyntactic(candidate);
    const semantic = await this.estimateSemantic(candidate);
    const factual = await this.estimateFactual(hallucinations);
    const consistency = await this.estimateConsistency(candidate, context);

    const breakdown: ConfidenceBreakdown = { syntactic, semantic, factual, consistency };
    const score = this.calculateWeightedScore(breakdown);
    const riskFactors = this.identifyRiskFactors(breakdown, candidate, hallucinations);
    const explanation = this.buildExplanation(score, breakdown, riskFactors);

    return { score, breakdown, riskFactors, explanation };
  }

  private async estimateSyntactic(candidate: CodeCandidate): Promise<number> {
    let score = 1.0;
    const code = candidate.code;

    // Check for balanced brackets
    const brackets: Record<string, string> = { '(': ')', '[': ']', '{': '}' };
    const stack: string[] = [];
    for (const char of code) {
      if (char in brackets) {
        stack.push(brackets[char]);
      } else if (Object.values(brackets).includes(char)) {
        if (stack.pop() !== char) {
          score -= 0.2;
        }
      }
    }
    if (stack.length > 0) {
      score -= 0.1 * stack.length;
    }

    return Math.max(0, Math.min(1, score));
  }

  private async estimateSemantic(candidate: CodeCandidate): Promise<number> {
    let score = 0.8;
    const code = candidate.code;

    if (/async\s+function/.test(code) && !/await|Promise|return/.test(code)) {
      score -= 0.15;
    }
    if (/throw\s+new\s+Error/.test(code) || /try\s*\{/.test(code)) {
      score += 0.05;
    }
    if (candidate.language === 'typescript') {
      if (/:\s*(string|number|boolean|void|\w+\[\]|Promise<|Record<)/.test(code)) {
        score += 0.05;
      }
    }

    return Math.max(0, Math.min(1, score));
  }

  private async estimateFactual(hallucinations: number): Promise<number> {
    return Math.max(0, Math.min(1, 1.0 - hallucinations * 0.2));
  }

  private async estimateConsistency(candidate: CodeCandidate, context: ProjectContext): Promise<number> {
    let score = 0.7;
    const code = candidate.code;
    const symbols = context.symbols ?? [];
    const symbolNames = new Set(symbols.map((s) => s.name));

    let knownRefs = 0;
    let unknownRefs = 0;
    const identifierPattern = /\b([A-Z][a-zA-Z0-9]*)\b/g;
    let match;
    while ((match = identifierPattern.exec(code)) !== null) {
      if (symbolNames.has(match[1])) {
        knownRefs++;
      } else {
        unknownRefs++;
      }
    }

    if (knownRefs + unknownRefs > 0) {
      const knownRatio = knownRefs / (knownRefs + unknownRefs);
      score = 0.5 + knownRatio * 0.5;
    }

    return Math.max(0, Math.min(1, score));
  }

  private calculateWeightedScore(breakdown: ConfidenceBreakdown): number {
    const { syntacticWeight, semanticWeight, factualWeight, consistencyWeight } = this.config;
    const totalWeight = syntacticWeight + semanticWeight + factualWeight + consistencyWeight;

    return (
      (breakdown.syntactic * syntacticWeight +
        breakdown.semantic * semanticWeight +
        breakdown.factual * factualWeight +
        breakdown.consistency * consistencyWeight) /
      totalWeight
    );
  }

  private identifyRiskFactors(
    breakdown: ConfidenceBreakdown,
    candidate: CodeCandidate,
    hallucinations: number,
  ): RiskFactor[] {
    const riskFactors: RiskFactor[] = [];
    const score = this.calculateWeightedScore(breakdown);

    if (score < this.config.lowConfidenceThreshold) {
      riskFactors.push({
        type: 'low_confidence',
        description: `Overall confidence ${(score * 100).toFixed(0)}% is below threshold`,
        impact: 0.3,
      });
    }

    if (hallucinations > 0) {
      riskFactors.push({
        type: 'hallucination_risk',
        description: `${hallucinations} potential hallucination(s) detected`,
        impact: hallucinations * 0.15,
      });
    }

    const codeLines = candidate.code.split('\n').length;
    if (codeLines > 100) {
      riskFactors.push({
        type: 'complexity',
        description: `Large code block (${codeLines} lines)`,
        impact: 0.1,
      });
    }

    if (breakdown.factual < 0.7) {
      riskFactors.push({
        type: 'hallucination_risk',
        description: `Low factual accuracy (${(breakdown.factual * 100).toFixed(0)}%)`,
        impact: 0.2,
      });
    }

    return riskFactors;
  }

  private buildExplanation(
    score: number,
    breakdown: ConfidenceBreakdown,
    riskFactors: RiskFactor[],
  ): Explanation {
    const level = score >= 0.8 ? 'high' : score >= 0.5 ? 'medium' : 'low';
    return {
      summary: `Confidence: ${(score * 100).toFixed(0)}% (${level})`,
      reasoning: [
        `Syntactic: ${(breakdown.syntactic * 100).toFixed(0)}%`,
        `Semantic: ${(breakdown.semantic * 100).toFixed(0)}%`,
        `Factual: ${(breakdown.factual * 100).toFixed(0)}%`,
        `Consistency: ${(breakdown.consistency * 100).toFixed(0)}%`,
        ...riskFactors.map((r) => `Risk: ${r.description}`),
      ],
      evidence: riskFactors.map((r) => ({
        type: 'rule_match' as const,
        description: r.description,
        artifacts: [],
        confidence: 1 - r.impact,
      })),
      relatedRequirements: ['REQ-ROUTE-001'],
    };
  }
}

/**
 * Factory function
 */
export function createConfidenceEstimator(
  config?: Partial<ConfidenceEstimatorConfig>,
): ConfidenceEstimator {
  return new ConfidenceEstimator(config);
}
