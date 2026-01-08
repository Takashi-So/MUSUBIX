/**
 * Meta Learner
 * @module @nahisaho/musubix-synthesis
 * @description Continuous rule improvement and suggestions
 * Traces to: REQ-SYN-004 (Rule Learning)
 */

import type {
  IMetaLearner,
  IRuleLibrary,
  SynthesisResult,
  SynthesisRule,
} from '../types.js';
import { RuleExtractor, resetRuleIdCounter } from './RuleExtractor.js';

/**
 * Meta learner implementation
 */
export class MetaLearner implements IMetaLearner {
  private readonly library: IRuleLibrary;
  private readonly extractor: RuleExtractor;
  private readonly pendingSuggestions: SynthesisRule[];
  private totalLearned: number;

  constructor(library: IRuleLibrary) {
    this.library = library;
    this.extractor = new RuleExtractor();
    this.pendingSuggestions = [];
    this.totalLearned = 0;
  }

  /**
   * Learn from synthesis result
   */
  async learn(
    result: SynthesisResult,
    usedRules: SynthesisRule[]
  ): Promise<void> {
    // Update confidence for used rules
    for (const rule of usedRules) {
      await this.library.recordUsage(rule.id, result.success);
    }

    // Extract new rules from successful synthesis
    if (result.success && result.program) {
      const newRules = this.extractor.extract(
        { examples: [] }, // Simplified - would need actual spec
        result.program
      );

      for (const rule of newRules) {
        // Check if similar rule exists
        const existing = await this.library.getAll();
        if (!this.hasSimularRule(rule, existing)) {
          this.pendingSuggestions.push(rule);
        }
      }

      this.totalLearned++;
    }
  }

  /**
   * Update confidence for a rule
   */
  async updateConfidence(ruleId: string, success: boolean): Promise<void> {
    await this.library.recordUsage(ruleId, success);
  }

  /**
   * Suggest new rules
   */
  async suggestRules(): Promise<SynthesisRule[]> {
    // Generalize pending suggestions
    if (this.pendingSuggestions.length > 0) {
      const generalized = this.extractor.generalize(this.pendingSuggestions);
      
      // Filter out low-confidence suggestions
      const suggestions = generalized.filter((r) => r.confidence >= 0.5);
      
      // Clear pending
      this.pendingSuggestions.length = 0;
      
      return suggestions;
    }

    // Analyze existing rules for generalization opportunities
    const allRules = await this.library.getAll();
    const opportunities = this.findGeneralizationOpportunities(allRules);

    return opportunities;
  }

  /**
   * Get total learned count
   */
  getTotalLearned(): number {
    return this.totalLearned;
  }

  /**
   * Reset state (for testing)
   */
  reset(): void {
    this.pendingSuggestions.length = 0;
    this.totalLearned = 0;
    resetRuleIdCounter();
  }

  /**
   * Check if similar rule exists
   */
  private hasSimularRule(rule: SynthesisRule, existing: SynthesisRule[]): boolean {
    for (const r of existing) {
      if (this.rulesAreSimilar(rule, r)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Check rule similarity
   */
  private rulesAreSimilar(a: SynthesisRule, b: SynthesisRule): boolean {
    // Compare template structure
    const aExpr = a.template.expression;
    const bExpr = b.template.expression;

    if (aExpr.kind !== bExpr.kind) return false;

    if (aExpr.kind === 'application' && bExpr.kind === 'application') {
      if (aExpr.operator !== bExpr.operator) return false;
      if (aExpr.args.length !== bExpr.args.length) return false;
      return true;
    }

    if (aExpr.kind === 'constant' && bExpr.kind === 'constant') {
      return aExpr.name === bExpr.name;
    }

    return false;
  }

  /**
   * Find generalization opportunities
   */
  private findGeneralizationOpportunities(
    rules: SynthesisRule[]
  ): SynthesisRule[] {
    const opportunities: SynthesisRule[] = [];

    // Group by operator
    const byOperator = new Map<string, SynthesisRule[]>();
    for (const rule of rules) {
      const expr = rule.template.expression;
      if (expr.kind === 'application') {
        const group = byOperator.get(expr.operator) ?? [];
        group.push(rule);
        byOperator.set(expr.operator, group);
      }
    }

    // Look for groups with multiple similar rules
    for (const [_operator, group] of byOperator) {
      if (group.length >= 2) {
        // Could potentially merge these
        const avgConfidence =
          group.reduce((sum, r) => sum + r.confidence, 0) / group.length;
        
        if (avgConfidence >= 0.7) {
          // Create a generalized rule
          const generalized = this.extractor.generalize(group);
          opportunities.push(...generalized);
        }
      }
    }

    return opportunities;
  }
}
