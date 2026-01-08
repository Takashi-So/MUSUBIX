/**
 * RewriteRuleSet - Equivalence Rewrite Rules for E-Graph
 *
 * Provides built-in and custom rewrite rules for AST optimization.
 * Used by E-Graph for equality saturation.
 *
 * @module @nahisaho/musubix-library-learner
 * @see TSK-LL-104
 * @see DES-LL-104
 * @see REQ-LL-104
 *
 * @example
 * ```typescript
 * import { createRewriteRuleSet } from './RewriteRuleSet.js';
 *
 * const ruleSet = createRewriteRuleSet();
 * const result = ruleSet.rewrite(ast);
 * console.log(`Applied ${result.rulesApplied.length} rules`);
 * ```
 */

import type { ASTNode } from '../types.js';

// =============================================================================
// Types
// =============================================================================

/**
 * Pattern for matching AST nodes
 */
export type Pattern = Record<string, unknown>;

/**
 * Rewrite rule definition
 */
export interface RewriteRule {
  /** Unique identifier */
  id: string;
  /** Human-readable name */
  name: string;
  /** Pattern to match */
  pattern: Pattern;
  /** Replacement template */
  replacement: Pattern;
  /** Rule description */
  description?: string;
  /** Rule category */
  category?: string;
  /** Priority (higher = applied first) */
  priority?: number;
}

/**
 * Result of rewrite operation
 */
export interface RewriteResult {
  /** Rewritten AST */
  rewritten: ASTNode;
  /** Rules that were applied */
  rulesApplied: string[];
  /** Number of iterations */
  iterationCount: number;
  /** Whether any changes were made */
  changed: boolean;
}

/**
 * Configuration for RewriteRuleSet
 */
export interface RewriteRuleSetConfig {
  /** Maximum rewrite iterations */
  maxIterations?: number;
  /** Enable built-in rules */
  enableBuiltinRules?: boolean;
}

/**
 * RewriteRuleSet interface
 */
export interface RewriteRuleSet {
  /** Add a custom rule */
  addRule(rule: RewriteRule): void;

  /** Remove a rule by ID */
  removeRule(id: string): void;

  /** Get a rule by ID */
  getRule(id: string): RewriteRule | undefined;

  /** List all rules, optionally filtered by category */
  listRules(category?: string): RewriteRule[];

  /** Get total rule count */
  getRuleCount(): number;

  /** Rewrite an AST using rules */
  rewrite(ast: ASTNode): RewriteResult;
}

// =============================================================================
// Built-in Rules
// =============================================================================

const BUILTIN_RULES: RewriteRule[] = [
  // Arithmetic: Addition with zero
  {
    id: 'add-zero-right',
    name: 'x + 0 = x (right)',
    pattern: { type: 'BinaryExpression', operator: '+', right: { type: 'Literal', value: 0 } },
    replacement: { $ref: 'left' },
    description: 'Adding zero on the right has no effect',
    category: 'arithmetic',
    priority: 10,
  },
  {
    id: 'add-zero-left',
    name: '0 + x = x (left)',
    pattern: { type: 'BinaryExpression', operator: '+', left: { type: 'Literal', value: 0 } },
    replacement: { $ref: 'right' },
    description: 'Adding zero on the left has no effect',
    category: 'arithmetic',
    priority: 10,
  },

  // Arithmetic: Multiplication with one
  {
    id: 'mul-one-right',
    name: 'x * 1 = x (right)',
    pattern: { type: 'BinaryExpression', operator: '*', right: { type: 'Literal', value: 1 } },
    replacement: { $ref: 'left' },
    description: 'Multiplying by one on the right has no effect',
    category: 'arithmetic',
    priority: 10,
  },
  {
    id: 'mul-one-left',
    name: '1 * x = x (left)',
    pattern: { type: 'BinaryExpression', operator: '*', left: { type: 'Literal', value: 1 } },
    replacement: { $ref: 'right' },
    description: 'Multiplying by one on the left has no effect',
    category: 'arithmetic',
    priority: 10,
  },

  // Arithmetic: Multiplication with zero
  {
    id: 'mul-zero-right',
    name: 'x * 0 = 0 (right)',
    pattern: { type: 'BinaryExpression', operator: '*', right: { type: 'Literal', value: 0 } },
    replacement: { type: 'Literal', value: 0 },
    description: 'Multiplying by zero results in zero',
    category: 'arithmetic',
    priority: 10,
  },
  {
    id: 'mul-zero-left',
    name: '0 * x = 0 (left)',
    pattern: { type: 'BinaryExpression', operator: '*', left: { type: 'Literal', value: 0 } },
    replacement: { type: 'Literal', value: 0 },
    description: 'Zero multiplied by anything is zero',
    category: 'arithmetic',
    priority: 10,
  },

  // Arithmetic: Subtraction
  {
    id: 'sub-zero',
    name: 'x - 0 = x',
    pattern: { type: 'BinaryExpression', operator: '-', right: { type: 'Literal', value: 0 } },
    replacement: { $ref: 'left' },
    description: 'Subtracting zero has no effect',
    category: 'arithmetic',
    priority: 10,
  },
  {
    id: 'sub-self',
    name: 'x - x = 0',
    pattern: { type: 'BinaryExpression', operator: '-', $constraint: 'left === right' },
    replacement: { type: 'Literal', value: 0 },
    description: 'Subtracting a value from itself equals zero',
    category: 'arithmetic',
    priority: 9,
  },

  // Arithmetic: Division
  {
    id: 'div-one',
    name: 'x / 1 = x',
    pattern: { type: 'BinaryExpression', operator: '/', right: { type: 'Literal', value: 1 } },
    replacement: { $ref: 'left' },
    description: 'Dividing by one has no effect',
    category: 'arithmetic',
    priority: 10,
  },
  {
    id: 'div-self',
    name: 'x / x = 1',
    pattern: { type: 'BinaryExpression', operator: '/', $constraint: 'left === right' },
    replacement: { type: 'Literal', value: 1 },
    description: 'Dividing a value by itself equals one',
    category: 'arithmetic',
    priority: 9,
  },

  // Boolean: Identity
  {
    id: 'and-true-right',
    name: 'x && true = x',
    pattern: { type: 'LogicalExpression', operator: '&&', right: { type: 'Literal', value: true } },
    replacement: { $ref: 'left' },
    description: 'AND with true on right has no effect',
    category: 'boolean',
    priority: 10,
  },
  {
    id: 'and-true-left',
    name: 'true && x = x',
    pattern: { type: 'LogicalExpression', operator: '&&', left: { type: 'Literal', value: true } },
    replacement: { $ref: 'right' },
    description: 'AND with true on left has no effect',
    category: 'boolean',
    priority: 10,
  },
  {
    id: 'or-false-right',
    name: 'x || false = x',
    pattern: { type: 'LogicalExpression', operator: '||', right: { type: 'Literal', value: false } },
    replacement: { $ref: 'left' },
    description: 'OR with false on right has no effect',
    category: 'boolean',
    priority: 10,
  },
  {
    id: 'or-false-left',
    name: 'false || x = x',
    pattern: { type: 'LogicalExpression', operator: '||', left: { type: 'Literal', value: false } },
    replacement: { $ref: 'right' },
    description: 'OR with false on left has no effect',
    category: 'boolean',
    priority: 10,
  },

  // Boolean: Absorption
  {
    id: 'and-false',
    name: 'x && false = false',
    pattern: { type: 'LogicalExpression', operator: '&&', right: { type: 'Literal', value: false } },
    replacement: { type: 'Literal', value: false },
    description: 'AND with false is always false',
    category: 'boolean',
    priority: 10,
  },
  {
    id: 'or-true',
    name: 'x || true = true',
    pattern: { type: 'LogicalExpression', operator: '||', right: { type: 'Literal', value: true } },
    replacement: { type: 'Literal', value: true },
    description: 'OR with true is always true',
    category: 'boolean',
    priority: 10,
  },

  // Boolean: Double negation
  {
    id: 'double-not',
    name: '!!x = x',
    pattern: {
      type: 'UnaryExpression',
      operator: '!',
      argument: { type: 'UnaryExpression', operator: '!', $capture: 'inner' },
    },
    replacement: { $ref: 'inner.argument' },
    description: 'Double negation cancels out',
    category: 'boolean',
    priority: 10,
  },

  // Conditional
  {
    id: 'ternary-true',
    name: 'true ? a : b = a',
    pattern: { type: 'ConditionalExpression', test: { type: 'Literal', value: true } },
    replacement: { $ref: 'consequent' },
    description: 'Ternary with true condition returns consequent',
    category: 'conditional',
    priority: 10,
  },
  {
    id: 'ternary-false',
    name: 'false ? a : b = b',
    pattern: { type: 'ConditionalExpression', test: { type: 'Literal', value: false } },
    replacement: { $ref: 'alternate' },
    description: 'Ternary with false condition returns alternate',
    category: 'conditional',
    priority: 10,
  },

  // Commutativity
  {
    id: 'add-commute',
    name: 'a + b = b + a',
    pattern: { type: 'BinaryExpression', operator: '+', $commutative: true },
    replacement: { $swap: ['left', 'right'] },
    description: 'Addition is commutative',
    category: 'commutativity',
    priority: 1,
  },
  {
    id: 'mul-commute',
    name: 'a * b = b * a',
    pattern: { type: 'BinaryExpression', operator: '*', $commutative: true },
    replacement: { $swap: ['left', 'right'] },
    description: 'Multiplication is commutative',
    category: 'commutativity',
    priority: 1,
  },

  // Associativity
  {
    id: 'add-assoc',
    name: '(a + b) + c = a + (b + c)',
    pattern: {
      type: 'BinaryExpression',
      operator: '+',
      left: { type: 'BinaryExpression', operator: '+' },
    },
    replacement: { $reassociate: true },
    description: 'Addition is associative',
    category: 'associativity',
    priority: 1,
  },
  {
    id: 'mul-assoc',
    name: '(a * b) * c = a * (b * c)',
    pattern: {
      type: 'BinaryExpression',
      operator: '*',
      left: { type: 'BinaryExpression', operator: '*' },
    },
    replacement: { $reassociate: true },
    description: 'Multiplication is associative',
    category: 'associativity',
    priority: 1,
  },
];

// =============================================================================
// Default Implementation
// =============================================================================

/**
 * Default RewriteRuleSet implementation
 */
export class DefaultRewriteRuleSet implements RewriteRuleSet {
  private rules: Map<string, RewriteRule> = new Map();
  private config: Required<RewriteRuleSetConfig>;

  constructor(config: RewriteRuleSetConfig = {}) {
    this.config = {
      maxIterations: config.maxIterations ?? 100,
      enableBuiltinRules: config.enableBuiltinRules ?? true,
    };

    if (this.config.enableBuiltinRules) {
      BUILTIN_RULES.forEach((rule) => this.rules.set(rule.id, rule));
    }
  }

  /**
   * Add a custom rule
   */
  addRule(rule: RewriteRule): void {
    if (!rule.id || !rule.name || !rule.pattern || !rule.replacement) {
      throw new Error('Invalid rule: missing required fields (id, name, pattern, replacement)');
    }

    if (this.rules.has(rule.id)) {
      throw new Error(`Duplicate rule ID: ${rule.id}`);
    }

    this.rules.set(rule.id, rule);
  }

  /**
   * Remove a rule by ID
   */
  removeRule(id: string): void {
    this.rules.delete(id);
  }

  /**
   * Get a rule by ID
   */
  getRule(id: string): RewriteRule | undefined {
    return this.rules.get(id);
  }

  /**
   * List all rules, optionally filtered by category
   */
  listRules(category?: string): RewriteRule[] {
    const allRules = Array.from(this.rules.values());
    if (category) {
      return allRules.filter((r) => r.category === category);
    }
    return allRules;
  }

  /**
   * Get total rule count
   */
  getRuleCount(): number {
    return this.rules.size;
  }

  /**
   * Rewrite an AST using rules
   */
  rewrite(ast: ASTNode): RewriteResult {
    const rulesApplied: string[] = [];
    let current = this.cloneAST(ast);
    let changed = false;
    let iterationCount = 0;

    // Sort rules by priority (higher first)
    const sortedRules = this.listRules().sort((a, b) => (b.priority ?? 0) - (a.priority ?? 0));

    for (let i = 0; i < this.config.maxIterations; i++) {
      iterationCount++;
      let iterationChanged = false;

      for (const rule of sortedRules) {
        const result = this.applyRule(current, rule);
        if (result.changed) {
          current = result.ast;
          rulesApplied.push(rule.id);
          iterationChanged = true;
          changed = true;
          break; // Start over with new AST
        }
      }

      if (!iterationChanged) {
        break; // No more rules apply
      }
    }

    return {
      rewritten: current,
      rulesApplied,
      iterationCount,
      changed,
    };
  }

  // ===========================================================================
  // Private Methods
  // ===========================================================================

  /**
   * Apply a single rule to an AST
   */
  private applyRule(ast: ASTNode, rule: RewriteRule): { ast: ASTNode; changed: boolean } {
    const match = this.matchPattern(ast, rule.pattern);
    if (match.matches) {
      const replaced = this.applyReplacement(ast, rule.replacement, match.bindings);
      return { ast: replaced, changed: true };
    }

    // Try to apply to children
    const astObj = ast as unknown as Record<string, unknown>;
    if (astObj.left) {
      const leftResult = this.applyRule(astObj.left as ASTNode, rule);
      if (leftResult.changed) {
        return {
          ast: { ...ast, left: leftResult.ast } as unknown as ASTNode,
          changed: true,
        };
      }
    }
    if (astObj.right) {
      const rightResult = this.applyRule(astObj.right as ASTNode, rule);
      if (rightResult.changed) {
        return {
          ast: { ...ast, right: rightResult.ast } as unknown as ASTNode,
          changed: true,
        };
      }
    }
    if (astObj.argument) {
      const argResult = this.applyRule(astObj.argument as ASTNode, rule);
      if (argResult.changed) {
        return {
          ast: { ...ast, argument: argResult.ast } as unknown as ASTNode,
          changed: true,
        };
      }
    }

    return { ast, changed: false };
  }

  /**
   * Match a pattern against an AST node
   */
  private matchPattern(
    ast: ASTNode,
    pattern: Pattern
  ): { matches: boolean; bindings: Record<string, ASTNode> } {
    const bindings: Record<string, ASTNode> = {};
    const astObj = ast as unknown as Record<string, unknown>;

    for (const [key, value] of Object.entries(pattern)) {
      if (key.startsWith('$')) continue; // Skip meta keys

      if (typeof value === 'object' && value !== null) {
        // Nested pattern
        if (!astObj[key]) {
          return { matches: false, bindings };
        }
        const nested = this.matchPattern(astObj[key] as ASTNode, value as Pattern);
        if (!nested.matches) {
          return { matches: false, bindings };
        }
        Object.assign(bindings, nested.bindings);
      } else {
        // Direct value comparison
        if (astObj[key] !== value) {
          return { matches: false, bindings };
        }
      }
    }

    // Capture the matched node parts for replacement
    bindings['left'] = astObj.left as ASTNode;
    bindings['right'] = astObj.right as ASTNode;
    bindings['argument'] = astObj.argument as ASTNode;
    bindings['consequent'] = astObj.consequent as ASTNode;
    bindings['alternate'] = astObj.alternate as ASTNode;

    return { matches: true, bindings };
  }

  /**
   * Apply a replacement template
   */
  private applyReplacement(
    _original: ASTNode,
    replacement: Pattern,
    bindings: Record<string, ASTNode>
  ): ASTNode {
    // Handle reference to captured binding
    if ('$ref' in replacement) {
      const ref = replacement['$ref'] as string;
      return bindings[ref] ?? _original;
    }

    // Handle direct replacement
    const result: Record<string, unknown> = {};
    for (const [key, value] of Object.entries(replacement)) {
      if (key.startsWith('$')) continue;
      result[key] = value;
    }

    return result as unknown as ASTNode;
  }

  /**
   * Deep clone an AST
   */
  private cloneAST(ast: ASTNode): ASTNode {
    return JSON.parse(JSON.stringify(ast));
  }
}

// =============================================================================
// Factory Function
// =============================================================================

/**
 * Create a new RewriteRuleSet instance
 */
export function createRewriteRuleSet(config: RewriteRuleSetConfig = {}): RewriteRuleSet {
  return new DefaultRewriteRuleSet(config);
}
