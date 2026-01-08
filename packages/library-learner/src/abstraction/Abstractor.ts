/**
 * Abstractor - Hierarchical abstraction of patterns
 *
 * REQ-LL-001: 階層的抽象化
 * DES-PHASE2-001: Abstraction Engine / Abstractor
 */

import type {
  PatternCandidate,
  ConcretePattern,
  ParameterizedTemplate,
  AbstractConcept,
  TemplateParameter,
  TemplateNode,
  TypeSignature,
} from '../types.js';

/**
 * Abstractor interface
 */
export interface Abstractor {
  /** Level 1: Extract concrete patterns */
  extractConcretePatterns(candidates: PatternCandidate[]): ConcretePattern[];

  /** Level 2: Parameterize patterns into templates */
  parameterize(patterns: ConcretePattern[]): ParameterizedTemplate[];

  /** Level 3: Generalize templates into abstract concepts */
  generalize(templates: ParameterizedTemplate[]): AbstractConcept[];

  /** Full abstraction pipeline */
  abstract(candidates: PatternCandidate[]): {
    concrete: ConcretePattern[];
    templates: ParameterizedTemplate[];
    concepts: AbstractConcept[];
  };
}

/**
 * Default Abstractor implementation
 */
class AbstractorImpl implements Abstractor {
  extractConcretePatterns(candidates: PatternCandidate[]): ConcretePattern[] {
    if (!candidates || candidates.length === 0) {
      return [];
    }

    return candidates.map((candidate) => ({
      id: candidate.id,
      ast: candidate.ast,
      occurrenceCount: candidate.occurrences.length,
      locations: candidate.occurrences,
    }));
  }

  parameterize(patterns: ConcretePattern[]): ParameterizedTemplate[] {
    if (!patterns || patterns.length === 0) {
      return [];
    }

    const templates: ParameterizedTemplate[] = [];
    const groups = this.groupSimilarPatterns(patterns);

    for (const group of groups) {
      if (group.length < 2) {
        // Single pattern - create simple template
        templates.push(this.createSimpleTemplate(group[0]));
      } else {
        // Multiple similar patterns - find common structure
        const template = this.findCommonTemplate(group);
        if (template) {
          templates.push(template);
        }
      }
    }

    return templates;
  }

  generalize(templates: ParameterizedTemplate[]): AbstractConcept[] {
    if (!templates || templates.length === 0) {
      return [];
    }

    const concepts: AbstractConcept[] = [];
    const categories = this.categorizeTemplates(templates);

    let conceptId = 0;
    for (const [category, categoryTemplates] of categories) {
      concepts.push({
        id: `CONCEPT-${++conceptId}`,
        name: this.generateConceptName(category),
        description: this.generateConceptDescription(category, categoryTemplates),
        templates: categoryTemplates.map((t) => t.id),
        category,
      });
    }

    return concepts;
  }

  abstract(candidates: PatternCandidate[]): {
    concrete: ConcretePattern[];
    templates: ParameterizedTemplate[];
    concepts: AbstractConcept[];
  } {
    const concrete = this.extractConcretePatterns(candidates);
    const templates = this.parameterize(concrete);
    const concepts = this.generalize(templates);

    return { concrete, templates, concepts };
  }

  // =========================================================================
  // Private methods
  // =========================================================================

  private groupSimilarPatterns(patterns: ConcretePattern[]): ConcretePattern[][] {
    const groups: ConcretePattern[][] = [];
    const used = new Set<string>();

    for (const pattern of patterns) {
      if (used.has(pattern.id)) continue;

      const group = [pattern];
      used.add(pattern.id);

      for (const other of patterns) {
        if (used.has(other.id)) continue;
        if (this.isSimilar(pattern, other)) {
          group.push(other);
          used.add(other.id);
        }
      }

      groups.push(group);
    }

    return groups;
  }

  private isSimilar(a: ConcretePattern, b: ConcretePattern): boolean {
    // Compare AST structure similarity
    return this.computeSimilarity(a.ast, b.ast) > 0.7;
  }

  private computeSimilarity(a: unknown, b: unknown): number {
    if (typeof a !== 'object' || typeof b !== 'object') {
      return a === b ? 1 : 0;
    }

    if (a === null || b === null) {
      return a === b ? 1 : 0;
    }

    const aObj = a as Record<string, unknown>;
    const bObj = b as Record<string, unknown>;

    // Compare type
    if (aObj.type !== bObj.type) {
      return 0;
    }

    let score = 1;
    let count = 1;

    // Compare children
    const aChildren = (aObj.children as unknown[]) ?? [];
    const bChildren = (bObj.children as unknown[]) ?? [];

    if (aChildren.length === bChildren.length) {
      for (let i = 0; i < aChildren.length; i++) {
        score += this.computeSimilarity(aChildren[i], bChildren[i]);
        count++;
      }
    } else {
      // Different number of children - less similar
      score += 0.5;
      count++;
    }

    return score / count;
  }

  private createSimpleTemplate(pattern: ConcretePattern): ParameterizedTemplate {
    return {
      id: `TMPL-${pattern.id}`,
      template: this.astToTemplate(pattern.ast),
      parameters: [],
      concretePatterns: [pattern.id],
    };
  }

  private findCommonTemplate(patterns: ConcretePattern[]): ParameterizedTemplate | null {
    if (patterns.length === 0) return null;

    // Use first pattern as base and find differences with others
    const base = patterns[0];
    const template = this.astToTemplate(base.ast);
    const parameters: TemplateParameter[] = [];

    let paramCount = 0;
    for (let i = 1; i < patterns.length; i++) {
      const diffs = this.findDifferences(base.ast, patterns[i].ast);
      for (const diff of diffs) {
        const paramName = `$${++paramCount}`;
        parameters.push({
          name: paramName,
          type: this.inferType(diff.value),
        });
        this.markAsHole(template, diff.path, paramName);
      }
    }

    return {
      id: `TMPL-${patterns.map((p) => p.id).join('-')}`,
      template,
      parameters,
      concretePatterns: patterns.map((p) => p.id),
    };
  }

  private astToTemplate(ast: unknown): TemplateNode {
    if (typeof ast !== 'object' || ast === null) {
      return { type: 'Literal', value: ast };
    }

    const node = ast as Record<string, unknown>;
    const template: TemplateNode = {
      type: String(node.type ?? 'Unknown'),
    };

    if (node.value !== undefined) {
      template.value = node.value;
    }

    if (Array.isArray(node.children)) {
      template.children = node.children.map((c) => this.astToTemplate(c));
    }

    return template;
  }

  private findDifferences(
    a: unknown,
    b: unknown,
    path: string[] = []
  ): Array<{ path: string[]; value: unknown }> {
    const diffs: Array<{ path: string[]; value: unknown }> = [];

    if (typeof a !== typeof b) {
      diffs.push({ path, value: b });
      return diffs;
    }

    if (typeof a !== 'object' || a === null) {
      if (a !== b) {
        diffs.push({ path, value: b });
      }
      return diffs;
    }

    const aObj = a as Record<string, unknown>;
    const bObj = b as Record<string, unknown>;

    // Compare properties
    const keys = new Set([...Object.keys(aObj), ...Object.keys(bObj)]);
    for (const key of keys) {
      if (key === 'children') continue;
      if (aObj[key] !== bObj[key]) {
        diffs.push({ path: [...path, key], value: bObj[key] });
      }
    }

    // Compare children
    const aChildren = (aObj.children as unknown[]) ?? [];
    const bChildren = (bObj.children as unknown[]) ?? [];

    const minLen = Math.min(aChildren.length, bChildren.length);
    for (let i = 0; i < minLen; i++) {
      diffs.push(...this.findDifferences(aChildren[i], bChildren[i], [...path, 'children', String(i)]));
    }

    return diffs;
  }

  private markAsHole(template: TemplateNode, path: string[], holeName: string): void {
    let current: TemplateNode = template;

    for (let i = 0; i < path.length - 1; i++) {
      const key = path[i];
      if (key === 'children') {
        const index = parseInt(path[++i], 10);
        if (current.children && current.children[index]) {
          current = current.children[index];
        } else {
          return;
        }
      }
    }

    current.isHole = true;
    current.holeName = holeName;
  }

  private inferType(value: unknown): TypeSignature {
    if (value === null || value === undefined) {
      return { kind: 'primitive', name: 'null' };
    }

    switch (typeof value) {
      case 'string':
        return { kind: 'primitive', name: 'string' };
      case 'number':
        return { kind: 'primitive', name: 'number' };
      case 'boolean':
        return { kind: 'primitive', name: 'boolean' };
      case 'object':
        if (Array.isArray(value)) {
          return { kind: 'array', elementType: { kind: 'primitive', name: 'unknown' } };
        }
        return { kind: 'object', properties: {} };
      default:
        return { kind: 'primitive', name: 'unknown' };
    }
  }

  private categorizeTemplates(templates: ParameterizedTemplate[]): Map<string, ParameterizedTemplate[]> {
    const categories = new Map<string, ParameterizedTemplate[]>();

    for (const template of templates) {
      const category = this.determineCategory(template);
      const existing = categories.get(category) ?? [];
      existing.push(template);
      categories.set(category, existing);
    }

    return categories;
  }

  private determineCategory(template: ParameterizedTemplate): string {
    const type = template.template.type;

    // Map AST types to semantic categories
    const categoryMap: Record<string, string> = {
      Declaration: 'declaration',
      IfStatement: 'control-flow',
      ForLoop: 'iteration',
      WhileLoop: 'iteration',
      ReturnStatement: 'return',
      FunctionCall: 'invocation',
      Assignment: 'assignment',
    };

    return categoryMap[type] ?? 'general';
  }

  private generateConceptName(category: string): string {
    const nameMap: Record<string, string> = {
      declaration: 'Variable Declaration Pattern',
      'control-flow': 'Conditional Logic Pattern',
      iteration: 'Loop Pattern',
      return: 'Return Statement Pattern',
      invocation: 'Function Call Pattern',
      assignment: 'Assignment Pattern',
      general: 'General Pattern',
    };

    return nameMap[category] ?? 'Unknown Pattern';
  }

  private generateConceptDescription(category: string, templates: ParameterizedTemplate[]): string {
    return `A ${category} pattern abstracted from ${templates.length} template(s)`;
  }
}

/**
 * Factory function to create an Abstractor
 */
export function createAbstractor(): Abstractor {
  return new AbstractorImpl();
}
