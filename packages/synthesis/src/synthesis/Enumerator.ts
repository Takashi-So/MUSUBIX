/**
 * Enumerator
 * @module @nahisaho/musubix-synthesis
 * @description Exhaustive program enumeration
 */

import type {
  EnumerationOptions,
  Example,
  Expression,
  IDSL,
  IEnumerator,
  Program,
  Specification,
  TypeSignature,
} from '../types.js';

/**
 * Generate unique IDs
 */
let programIdCounter = 0;
function generateProgramId(): string {
  return `prog-${++programIdCounter}`;
}

/**
 * Reset ID counter (for testing)
 */
export function resetProgramIdCounter(): void {
  programIdCounter = 0;
}

/**
 * Enumeration options for sync enumerate
 */
export interface EnumerateOptions {
  maxDepth: number;
  maxPrograms?: number;
  targetType?: TypeSignature;
}

/**
 * Enumerator implementation
 */
export class Enumerator implements IEnumerator {
  private readonly dsl: IDSL;

  constructor(dsl: IDSL) {
    this.dsl = dsl;
  }

  /**
   * Enumerate programs synchronously
   */
  enumerate(options: EnumerateOptions): Program[] {
    const { maxDepth, maxPrograms, targetType } = options;
    const programs: Program[] = [];
    const seen = new Set<string>();

    for (let depth = 0; depth <= maxDepth; depth++) {
      for (const expr of this.enumerateAtDepthSync(depth, targetType)) {
        if (maxPrograms && programs.length >= maxPrograms) {
          return programs;
        }
        
        // Avoid duplicates
        const serialized = JSON.stringify(expr);
        if (seen.has(serialized)) {
          continue;
        }
        seen.add(serialized);
        
        programs.push({
          id: generateProgramId(),
          expression: expr,
          cost: this.computeExpressionCost(expr),
        });
      }
    }

    return programs;
  }

  /**
   * Enumerate expressions at a given depth
   */
  enumerateExpressions(depth: number): Expression[] {
    return Array.from(this.enumerateAtDepthSync(depth));
  }

  /**
   * Get the depth of an expression
   */
  getExpressionDepth(expr: Expression): number {
    switch (expr.kind) {
      case 'constant':
      case 'variable':
        return 0;
      case 'application':
        if (expr.args.length === 0) {
          return 1;
        }
        return 1 + Math.max(...expr.args.map((a) => this.getExpressionDepth(a)));
      case 'lambda':
        return 1 + this.getExpressionDepth(expr.body);
      default:
        return 0;
    }
  }

  /**
   * Count programs at a given depth
   */
  countPrograms(depth: number): number {
    let count = 0;
    for (let d = 0; d <= depth; d++) {
      for (const _ of this.enumerateAtDepthSync(d)) {
        count++;
      }
    }
    return count;
  }

  /**
   * Enumerate all programs up to given depth/cost (async generator)
   */
  async *enumerateAsync(
    options: EnumerationOptions
  ): AsyncGenerator<Program, void, unknown> {
    const { maxDepth, maxCost = Infinity, targetType } = options;

    for (let depth = 0; depth <= maxDepth; depth++) {
      for (const expr of this.enumerateAtDepthSync(depth, targetType)) {
        const cost = this.computeExpressionCost(expr);
        if (cost <= maxCost) {
          yield {
            id: generateProgramId(),
            expression: expr,
            cost,
          };
        }
      }
    }
  }

  /**
   * Enumerate programs that might satisfy the spec
   */
  async *enumerateForSpec(
    spec: Specification,
    options: EnumerationOptions
  ): AsyncGenerator<Program, void, unknown> {
    const { maxDepth, maxCost = Infinity, yieldInterval = 100 } = options;
    const targetType = spec.outputType;

    let count = 0;
    for (let depth = 0; depth <= maxDepth; depth++) {
      for (const expr of this.enumerateAtDepthSync(depth, targetType)) {
        const cost = this.computeExpressionCost(expr);
        if (cost <= maxCost) {
          const program: Program = {
            id: generateProgramId(),
            expression: expr,
            cost,
          };

          // Check if program satisfies any examples (early filter)
          if (this.mightSatisfyExamples(program, spec.examples)) {
            yield program;
          }

          count++;
          if (count % yieldInterval === 0) {
            await new Promise((r) => setTimeout(r, 0));
          }
        }
      }
    }
  }

  /**
   * Enumerate expressions at a specific depth (sync)
   */
  private *enumerateAtDepthSync(
    depth: number,
    targetType?: TypeSignature
  ): Generator<Expression, void, unknown> {
    if (depth === 0) {
      // Constants only at depth 0
      for (const [, constant] of this.dsl.constants) {
        if (!targetType || this.typeMatches(constant.type, targetType)) {
          yield { kind: 'constant', name: constant.name };
        }
      }
    } else if (depth === 1) {
      // At depth 1: input variables + operator applications with depth-0 args
      // Input variable is included at depth 1 since it requires one level of complexity
      yield { kind: 'variable', name: 'input' };
      
      // Applications of operators with depth-0 arguments
      for (const [, operator] of this.dsl.operators) {
        if (targetType && !this.typeMatches(operator.outputType, targetType)) {
          continue;
        }

        // Generate all combinations of arguments with depth 0 (constants only)
        for (const args of this.enumerateArgumentsAtDepth(
          operator.inputTypes,
          0
        )) {
          yield { kind: 'application', operator: operator.name, args };
        }
      }
    } else {
      // Applications of operators at depth > 1
      for (const [, operator] of this.dsl.operators) {
        if (targetType && !this.typeMatches(operator.outputType, targetType)) {
          continue;
        }

        // Generate all combinations of arguments
        for (const args of this.enumerateArguments(
          operator.inputTypes,
          depth - 1
        )) {
          yield { kind: 'application', operator: operator.name, args };
        }
      }
    }
  }

  /**
   * Enumerate arguments at exactly a specific depth (for avoiding duplicates)
   */
  private *enumerateArgumentsAtDepth(
    inputTypes: TypeSignature[],
    exactDepth: number
  ): Generator<Expression[], void, unknown> {
    if (inputTypes.length === 0) {
      yield [];
      return;
    }

    if (inputTypes.length === 1) {
      for (const expr of this.enumerateAtDepthSync(exactDepth, inputTypes[0])) {
        yield [expr];
      }
      return;
    }

    // For multiple arguments, enumerate combinations at same depth
    const firstType = inputTypes[0];
    const restTypes = inputTypes.slice(1);

    for (const firstExpr of this.enumerateAtDepthSync(exactDepth, firstType)) {
      for (const restExprs of this.enumerateArgumentsAtDepth(restTypes, exactDepth)) {
        yield [firstExpr, ...restExprs];
      }
    }
  }

  /**
   * Enumerate all combinations of arguments for an operator
   */
  private *enumerateArguments(
    inputTypes: TypeSignature[],
    maxArgDepth: number
  ): Generator<Expression[], void, unknown> {
    if (inputTypes.length === 0) {
      yield [];
      return;
    }

    if (inputTypes.length === 1) {
      for (let d = 0; d <= maxArgDepth; d++) {
        for (const expr of this.enumerateAtDepthSync(d, inputTypes[0])) {
          yield [expr];
        }
      }
      return;
    }

    // For multiple arguments, enumerate combinations
    const firstType = inputTypes[0];
    const restTypes = inputTypes.slice(1);

    for (let d = 0; d <= maxArgDepth; d++) {
      for (const firstExpr of this.enumerateAtDepthSync(d, firstType)) {
        for (const restExprs of this.enumerateArguments(restTypes, maxArgDepth)) {
          yield [firstExpr, ...restExprs];
        }
      }
    }
  }

  /**
   * Check if types match
   */
  private typeMatches(actual: TypeSignature, expected: TypeSignature): boolean {
    if (expected === 'any') return true;
    if (typeof actual === 'string' && typeof expected === 'string') {
      return actual === expected;
    }
    return false;
  }

  /**
   * Compute expression cost
   */
  private computeExpressionCost(expr: Expression): number {
    switch (expr.kind) {
      case 'constant':
        return 1;
      case 'variable':
        return 1;
      case 'application': {
        const operator = this.dsl.getOperator(expr.operator);
        const opCost = operator?.cost ?? 1;
        const argsCost = expr.args.reduce(
          (sum, arg) => sum + this.computeExpressionCost(arg),
          0
        );
        return opCost + argsCost;
      }
      case 'lambda':
        return 1 + this.computeExpressionCost(expr.body);
      default:
        return 1;
    }
  }

  /**
   * Quick check if program might satisfy examples
   */
  private mightSatisfyExamples(program: Program, examples: Example[]): boolean {
    if (examples.length === 0) return true;

    try {
      const result = this.dsl.execute(program, examples[0].input as Record<string, unknown>);
      return this.valuesEqual(result, examples[0].output);
    } catch {
      return false;
    }
  }

  /**
   * Check value equality
   */
  private valuesEqual(a: unknown, b: unknown): boolean {
    if (a === b) return true;
    if (typeof a !== typeof b) return false;
    if (Array.isArray(a) && Array.isArray(b)) {
      if (a.length !== b.length) return false;
      return a.every((v, i) => this.valuesEqual(v, b[i]));
    }
    if (typeof a === 'object' && a !== null && b !== null) {
      return JSON.stringify(a) === JSON.stringify(b);
    }
    return false;
  }
}
