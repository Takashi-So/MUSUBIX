/**
 * Rule Extractor
 * @module @nahisaho/musubix-synthesis
 * @description Extract synthesis rules from successful synthesis
 * Traces to: REQ-SYN-004 (Rule Learning)
 */

import type {
  Expression,
  HoleDefinition,
  IRuleExtractor,
  Program,
  ProgramTemplate,
  SpecPattern,
  Specification,
  SynthesisRule,
} from '../types.js';

/**
 * Rule ID counter
 */
let ruleIdCounter = 0;

/**
 * Generate rule ID
 */
function generateRuleId(): string {
  return `RULE-${String(++ruleIdCounter).padStart(3, '0')}`;
}

/**
 * Reset rule ID counter (for testing)
 */
export function resetRuleIdCounter(): void {
  ruleIdCounter = 0;
}

/**
 * Rule extractor implementation
 */
export class RuleExtractor implements IRuleExtractor {
  /**
   * Extract rules from successful synthesis
   */
  extract(spec: Specification, program: Program): SynthesisRule[] {
    const rules: SynthesisRule[] = [];

    // Extract pattern from spec
    const pattern = this.extractPattern(spec);

    // Extract template from program
    const template = this.extractTemplate(program);

    // Create rule
    const rule: SynthesisRule = {
      id: generateRuleId(),
      name: this.generateRuleName(program),
      pattern,
      template,
      confidence: 0.5, // Initial confidence (prior)
      usageCount: 0,
      successCount: 0,
    };

    rules.push(rule);

    // Also extract sub-rules from nested expressions
    const subRules = this.extractSubRules(program.expression, spec);
    rules.push(...subRules);

    return rules;
  }

  /**
   * Generalize multiple rules
   */
  generalize(rules: SynthesisRule[]): SynthesisRule[] {
    // Group similar rules
    const groups = this.groupSimilarRules(rules);
    const generalized: SynthesisRule[] = [];

    for (const group of groups) {
      if (group.length === 1) {
        generalized.push(group[0]);
      } else {
        // Merge similar rules
        const merged = this.mergeRules(group);
        generalized.push(merged);
      }
    }

    return generalized;
  }

  /**
   * Extract pattern from specification
   */
  private extractPattern(spec: Specification): SpecPattern {
    const examples = spec.examples;

    // Try to find common patterns in inputs
    const inputPattern = this.findCommonPattern(examples.map((e) => e.input));

    // Try to find common patterns in outputs
    const outputPattern = this.findCommonPattern(examples.map((e) => e.output));

    // Count input keys from first example
    const firstInput = examples[0]?.input;
    const inputCount = typeof firstInput === 'object' && firstInput !== null
      ? Object.keys(firstInput as Record<string, unknown>).length
      : undefined;

    return {
      inputPattern,
      outputPattern,
      typeConstraints: spec.inputType
        ? [spec.inputType, spec.outputType ?? 'any']
        : undefined,
      inputCount,
    };
  }

  /**
   * Extract template from program
   */
  private extractTemplate(program: Program): ProgramTemplate {
    const holes: HoleDefinition[] = [];
    const expression = this.templatizeExpression(
      program.expression,
      holes,
      []
    );

    return {
      expression,
      holes,
    };
  }

  /**
   * Convert expression to template with holes
   */
  private templatizeExpression(
    expr: Expression,
    holes: HoleDefinition[],
    path: number[]
  ): Expression {
    switch (expr.kind) {
      case 'constant':
        // Keep constants as-is
        return expr;

      case 'variable':
        // Keep variables as-is
        return expr;

      case 'application':
        // Recursively templatize arguments
        return {
          kind: 'application',
          operator: expr.operator,
          args: expr.args.map((arg, i) =>
            this.templatizeExpression(arg, holes, [...path, i])
          ),
        };

      case 'lambda':
        // Templatize body
        return {
          ...expr,
          body: this.templatizeExpression(expr.body, holes, [...path, 0]),
        };

      default:
        return expr;
    }
  }

  /**
   * Extract sub-rules from nested expressions
   */
  private extractSubRules(
    expr: Expression,
    _spec: Specification
  ): SynthesisRule[] {
    const subRules: SynthesisRule[] = [];

    if (expr.kind === 'application') {
      // Create a rule for this operator application
      for (const arg of expr.args) {
        if (arg.kind === 'application') {
          // Recursively extract from nested applications
          subRules.push(...this.extractSubRules(arg, _spec));
        }
      }
    }

    return subRules;
  }

  /**
   * Generate rule name from program
   */
  private generateRuleName(program: Program): string {
    const expr = program.expression;
    if (expr.kind === 'application') {
      return `${expr.operator}-rule`;
    }
    if (expr.kind === 'constant') {
      return `const-${expr.name}-rule`;
    }
    if (expr.kind === 'variable') {
      return `var-${expr.name}-rule`;
    }
    return 'anonymous-rule';
  }

  /**
   * Find common pattern in values
   */
  private findCommonPattern(values: unknown[]): unknown {
    if (values.length === 0) return undefined;
    if (values.length === 1) return values[0];

    // Check if all values are same type
    const types = values.map((v) => typeof v);
    if (new Set(types).size > 1) {
      return { anyOf: values };
    }

    // For strings, try to find common structure
    if (types[0] === 'string') {
      const strings = values as string[];
      const commonPrefix = this.findCommonPrefix(strings);
      const commonSuffix = this.findCommonSuffix(strings);

      if (commonPrefix || commonSuffix) {
        return { prefix: commonPrefix, suffix: commonSuffix };
      }
    }

    // For arrays, try to find common structure
    if (Array.isArray(values[0])) {
      const arrays = values as unknown[][];
      if (arrays.every((a) => a.length === arrays[0].length)) {
        return { arrayLength: arrays[0].length };
      }
    }

    return { type: types[0] };
  }

  /**
   * Find common prefix of strings
   */
  private findCommonPrefix(strings: string[]): string {
    if (strings.length === 0) return '';
    let prefix = strings[0];
    for (const s of strings.slice(1)) {
      while (!s.startsWith(prefix) && prefix.length > 0) {
        prefix = prefix.slice(0, -1);
      }
    }
    return prefix;
  }

  /**
   * Find common suffix of strings
   */
  private findCommonSuffix(strings: string[]): string {
    if (strings.length === 0) return '';
    let suffix = strings[0];
    for (const s of strings.slice(1)) {
      while (!s.endsWith(suffix) && suffix.length > 0) {
        suffix = suffix.slice(1);
      }
    }
    return suffix;
  }

  /**
   * Group similar rules
   */
  private groupSimilarRules(rules: SynthesisRule[]): SynthesisRule[][] {
    const groups: SynthesisRule[][] = [];
    const assigned = new Set<string>();

    for (const rule of rules) {
      if (assigned.has(rule.id)) continue;

      const group = [rule];
      assigned.add(rule.id);

      for (const other of rules) {
        if (assigned.has(other.id)) continue;
        if (this.areRulesSimilar(rule, other)) {
          group.push(other);
          assigned.add(other.id);
        }
      }

      groups.push(group);
    }

    return groups;
  }

  /**
   * Check if two rules are similar
   */
  private areRulesSimilar(a: SynthesisRule, b: SynthesisRule): boolean {
    // Check if templates have same structure
    const aExpr = a.template.expression;
    const bExpr = b.template.expression;

    if (aExpr.kind !== bExpr.kind) return false;

    if (aExpr.kind === 'application' && bExpr.kind === 'application') {
      return aExpr.operator === bExpr.operator;
    }

    return false;
  }

  /**
   * Merge similar rules
   */
  private mergeRules(rules: SynthesisRule[]): SynthesisRule {
    // Use the most common template
    const templateCounts = new Map<string, number>();
    for (const rule of rules) {
      const key = JSON.stringify(rule.template.expression);
      templateCounts.set(key, (templateCounts.get(key) ?? 0) + 1);
    }

    let bestTemplate = rules[0].template;
    let bestCount = 0;
    for (const [key, count] of templateCounts) {
      if (count > bestCount) {
        bestCount = count;
        bestTemplate = rules.find(
          (r) => JSON.stringify(r.template.expression) === key
        )!.template;
      }
    }

    return {
      id: generateRuleId(),
      name: `merged-${rules[0].name ?? 'rule'}`,
      pattern: rules[0].pattern, // Use first pattern (could be merged)
      template: bestTemplate,
      confidence: rules.reduce((sum, r) => sum + r.confidence, 0) / rules.length,
      usageCount: rules.reduce((sum, r) => sum + (r.usageCount ?? 0), 0),
      successCount: rules.reduce((sum, r) => sum + (r.successCount ?? 0), 0),
    };
  }
}
