/**
 * DSL Implementation
 * @module @nahisaho/musubix-synthesis
 * @description Domain-specific language for program synthesis
 * Traces to: REQ-SYN-001 (DSL Definition Framework)
 */

import type {
  Constant,
  DSLConfig,
  Expression,
  IDSL,
  Operator,
  Program,
  TypeDefinition,
  ValidationError,
  ValidationResult,
} from '../types.js';
import { ExecutionError, OperatorNotFoundError } from '../errors.js';

/**
 * DSL implementation
 */
export class DSL implements IDSL {
  readonly name: string;
  readonly operators: Map<string, Operator>;
  readonly constants: Map<string, Constant>;
  readonly types: Map<string, TypeDefinition>;

  constructor(config: DSLConfig) {
    this.name = config.name ?? 'dsl';
    
    // Convert arrays to maps for efficient lookup
    this.operators = new Map(config.operators.map(op => [op.name, op]));
    this.constants = new Map(config.constants.map(c => [c.name, c]));
    this.types = new Map(config.types.map(t => [t.name, t]));
  }

  /**
   * Execute a program with input
   */
  execute(program: Program, input: Record<string, unknown>): unknown {
    const variables = new Map(Object.entries(input));
    return this.evaluateExpression(program.expression, { input, variables });
  }

  /**
   * Validate a program
   */
  validate(program: Program): boolean {
    const errors: ValidationError[] = [];
    this.validateExpression(program.expression, errors, []);
    return errors.length === 0;
  }

  /**
   * Validate with detailed result
   */
  validateWithDetails(program: Program): ValidationResult {
    const errors: ValidationError[] = [];
    this.validateExpression(program.expression, errors, []);

    return {
      valid: errors.length === 0,
      errors,
    };
  }

  /**
   * Enumerate programs up to max depth
   */
  enumerate(maxDepth: number, maxResults?: number): Program[] {
    const programs: Program[] = [];
    this.enumerateExpressions(maxDepth, programs, maxResults);
    return programs;
  }

  /**
   * Get an operator by name
   */
  getOperator(name: string): Operator | undefined {
    return this.operators.get(name);
  }

  /**
   * Get a constant by name
   */
  getConstant(name: string): Constant | undefined {
    return this.constants.get(name);
  }

  /**
   * Get a type by name
   */
  getType(name: string): TypeDefinition | undefined {
    return this.types.get(name);
  }

  /**
   * Get all operators
   */
  getOperators(): Operator[] {
    return Array.from(this.operators.values());
  }

  /**
   * Get all constants
   */
  getConstants(): Constant[] {
    return Array.from(this.constants.values());
  }

  /**
   * Enumerate expressions up to max depth
   */
  private enumerateExpressions(
    maxDepth: number,
    programs: Program[],
    maxResults?: number
  ): void {
    // Add constants
    for (const constant of this.constants.values()) {
      if (maxResults && programs.length >= maxResults) return;
      programs.push({ expression: { kind: 'constant', name: constant.name } });
    }

    if (maxDepth < 2) return;

    // Add applications
    for (const operator of this.operators.values()) {
      if (maxResults && programs.length >= maxResults) return;
      
      // Generate combinations of arguments
      const argCombinations = this.generateArgCombinations(
        operator.inputTypes.length,
        maxDepth - 1,
        maxResults ? maxResults - programs.length : undefined
      );

      for (const args of argCombinations) {
        if (maxResults && programs.length >= maxResults) return;
        programs.push({
          expression: {
            kind: 'application',
            operator: operator.name,
            args,
          },
        });
      }
    }
  }

  /**
   * Generate argument combinations
   */
  private generateArgCombinations(
    arity: number,
    _depth: number,
    _maxResults?: number
  ): Expression[][] {
    if (arity === 0) return [[]];

    const baseExprs: Expression[] = Array.from(this.constants.values()).map(
      (c) => ({ kind: 'constant' as const, name: c.name })
    );

    // Simple: just use constants for now
    const result: Expression[][] = [];
    const gen = this.cartesianProduct(
      Array(arity).fill(baseExprs) as Expression[][]
    );

    for (const combo of gen) {
      result.push(combo);
    }

    return result;
  }

  /**
   * Cartesian product of arrays
   */
  private *cartesianProduct(arrays: Expression[][]): Generator<Expression[]> {
    if (arrays.length === 0) {
      yield [];
      return;
    }

    const [first, ...rest] = arrays;
    for (const item of first) {
      for (const combo of this.cartesianProduct(rest)) {
        yield [item, ...combo];
      }
    }
  }  /**
   * Evaluate an expression
   */
  private evaluateExpression(
    expr: Expression,
    context: { input: unknown; variables?: Map<string, unknown> }
  ): unknown {
    switch (expr.kind) {
      case 'constant': {
        const constant = this.constants.get(expr.name);
        if (!constant) {
          throw new ExecutionError(`Unknown constant: ${expr.name}`);
        }
        return constant.value;
      }

      case 'variable': {
        const value = context.variables?.get(expr.name);
        if (value === undefined) {
          throw new ExecutionError(`Unknown variable: ${expr.name}`);
        }
        return value;
      }

      case 'application': {
        const operator = this.operators.get(expr.operator);
        if (!operator) {
          throw new OperatorNotFoundError(expr.operator);
        }

        const args = expr.args.map((arg) =>
          this.evaluateExpression(arg, context)
        );

        const impl = operator.implementation ?? operator.semantics;
        if (!impl) {
          throw new ExecutionError(
            `Operator ${expr.operator} has no implementation defined`
          );
        }

        try {
          return impl(...args);
        } catch (error) {
          throw new ExecutionError(
            `Error executing operator ${expr.operator}: ${error}`,
            JSON.stringify(expr)
          );
        }
      }

      case 'lambda': {
        // Return a function that evaluates the body with the parameter bound
        return (arg: unknown) => {
          const newVariables = new Map(context.variables ?? []);
          newVariables.set(expr.parameter, arg);
          return this.evaluateExpression(expr.body, {
            input: context.input,
            variables: newVariables,
          });
        };
      }

      default:
        throw new ExecutionError(`Unknown expression kind: ${(expr as Expression).kind}`);
    }
  }

  /**
   * Validate an expression
   */
  private validateExpression(
    expr: Expression,
    errors: ValidationError[],
    path: number[]
  ): void {
    switch (expr.kind) {
      case 'constant': {
        if (!this.constants.has(expr.name)) {
          errors.push({
            message: `Unknown constant: ${expr.name}`,
            path,
          });
        }
        break;
      }

      case 'variable': {
        // Variables are always valid (checked at runtime)
        break;
      }

      case 'application': {
        if (!this.operators.has(expr.operator)) {
          errors.push({
            message: `Unknown operator: ${expr.operator}`,
            path,
          });
        } else {
          const operator = this.operators.get(expr.operator)!;
          if (expr.args.length !== operator.inputTypes.length) {
            errors.push({
              message: `Operator ${expr.operator} expects ${operator.inputTypes.length} arguments, got ${expr.args.length}`,
              path,
            });
          }
        }

        // Validate arguments
        for (let i = 0; i < expr.args.length; i++) {
          this.validateExpression(expr.args[i], errors, [...path, i]);
        }
        break;
      }

      case 'lambda': {
        this.validateExpression(expr.body, errors, [...path, 0]);
        break;
      }

      default:
        errors.push({
          message: `Unknown expression kind: ${(expr as Expression).kind}`,
          path,
        });
    }
  }
}
