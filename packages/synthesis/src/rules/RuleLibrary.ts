/**
 * Rule Library
 * @module @nahisaho/musubix-synthesis
 * @description Storage and retrieval of synthesis rules
 * Traces to: REQ-SYN-004 (Rule Learning)
 */

import type { IRuleLibrary, Specification, SynthesisRule } from '../types.js';

/**
 * Rule library implementation
 */
export class RuleLibrary implements IRuleLibrary {
  private rules: Map<string, SynthesisRule>;

  constructor() {
    this.rules = new Map();
  }

  /**
   * Add a rule to the library
   */
  async add(rule: SynthesisRule): Promise<void> {
    this.rules.set(rule.id, rule);
  }

  /**
   * Get a rule by ID
   */
  async get(id: string): Promise<SynthesisRule | null> {
    return this.rules.get(id) ?? null;
  }

  /**
   * Match rules against specification
   */
  async match(spec: Specification): Promise<SynthesisRule[]> {
    const matches: SynthesisRule[] = [];

    for (const rule of this.rules.values()) {
      if (this.ruleMatchesSpec(rule, spec)) {
        matches.push(rule);
      }
    }

    // Sort by confidence (descending)
    matches.sort((a, b) => b.confidence - a.confidence);

    return matches;
  }

  /**
   * Record rule usage
   */
  async recordUsage(ruleId: string, success: boolean): Promise<void> {
    const rule = this.rules.get(ruleId);
    if (!rule) return;

    const currentUsage = rule.usageCount ?? 0;
    const currentSuccess = rule.successCount ?? 0;

    // Update mutable copy
    const updated: SynthesisRule = {
      ...rule,
      usageCount: currentUsage + 1,
      successCount: currentSuccess + (success ? 1 : 0),
      confidence: this.calculateConfidence(currentUsage + 1, currentSuccess + (success ? 1 : 0)),
    };

    this.rules.set(ruleId, updated);
  }

  /**
   * Calculate confidence from usage statistics
   */
  private calculateConfidence(usageCount: number, successCount: number): number {
    // Bayesian update with prior of 0.5
    // Add smoothing to avoid extreme values
    const alpha = successCount + 1;
    const beta = (usageCount - successCount) + 1;
    return alpha / (alpha + beta);
  }

  /**
   * Prune low-confidence rules
   */
  async prune(threshold: number): Promise<number> {
    let pruned = 0;
    const toDelete: string[] = [];

    for (const [id, rule] of this.rules) {
      // Prune if confidence is below threshold
      // Only require high usage count if usageCount is defined and > 0
      const usageCount = rule.usageCount ?? 0;
      const shouldPrune = rule.confidence < threshold && (usageCount === 0 || usageCount > 10);
      if (shouldPrune) {
        toDelete.push(id);
        pruned++;
      }
    }

    for (const id of toDelete) {
      this.rules.delete(id);
    }

    return pruned;
  }

  /**
   * Get all rules
   */
  async getAll(): Promise<SynthesisRule[]> {
    return Array.from(this.rules.values());
  }

  /**
   * Check if rule matches spec
   */
  private ruleMatchesSpec(rule: SynthesisRule, spec: Specification): boolean {
    const pattern = rule.pattern;

    // Check inputCount if specified
    if (pattern.inputCount !== undefined) {
      const firstInput = spec.examples[0]?.input;
      const specInputCount = typeof firstInput === 'object' && firstInput !== null
        ? Object.keys(firstInput as Record<string, unknown>).length
        : 0;
      if (pattern.inputCount !== specInputCount) {
        return false;
      }
    }

    // Check exampleCount if specified
    if (pattern.exampleCount !== undefined) {
      if (pattern.exampleCount !== spec.examples.length) {
        return false;
      }
    }

    // Check type constraints
    if (pattern.typeConstraints && spec.inputType) {
      const [inputType, outputType] = pattern.typeConstraints;
      if (inputType !== 'any' && inputType !== spec.inputType) {
        return false;
      }
      if (outputType !== 'any' && spec.outputType && outputType !== spec.outputType) {
        return false;
      }
    }

    // Check input/output patterns
    if (pattern.inputPattern) {
      if (!this.valueMatchesPattern(spec.examples[0]?.input, pattern.inputPattern)) {
        return false;
      }
    }

    if (pattern.outputPattern) {
      if (!this.valueMatchesPattern(spec.examples[0]?.output, pattern.outputPattern)) {
        return false;
      }
    }

    return true;
  }

  /**
   * Check if value matches pattern
   */
  private valueMatchesPattern(value: unknown, pattern: unknown): boolean {
    if (pattern === undefined || pattern === null) return true;

    if (typeof pattern === 'object' && pattern !== null) {
      const p = pattern as Record<string, unknown>;

      // Type pattern
      if ('type' in p) {
        return typeof value === p.type;
      }

      // Prefix/suffix pattern for strings
      if ('prefix' in p || 'suffix' in p) {
        if (typeof value !== 'string') return false;
        if (p.prefix && !value.startsWith(p.prefix as string)) return false;
        if (p.suffix && !value.endsWith(p.suffix as string)) return false;
        return true;
      }

      // Array length pattern
      if ('arrayLength' in p) {
        if (!Array.isArray(value)) return false;
        return value.length === p.arrayLength;
      }

      // Any of pattern
      if ('anyOf' in p) {
        const anyOf = p.anyOf as unknown[];
        return anyOf.some((v) => this.valuesEqual(value, v));
      }
    }

    return this.valuesEqual(value, pattern);
  }

  /**
   * Value equality
   */
  private valuesEqual(a: unknown, b: unknown): boolean {
    if (a === b) return true;
    if (typeof a !== typeof b) return false;
    if (typeof a === 'object' && a !== null && b !== null) {
      return JSON.stringify(a) === JSON.stringify(b);
    }
    return false;
  }
}
