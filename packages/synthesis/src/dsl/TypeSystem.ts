/**
 * Type System
 * @module @nahisaho/musubix-synthesis
 * @description Type checking and inference for DSL
 */

import type {
  Constant,
  DSLConfig,
  Expression,
  IDSL,
  ITypeSystem,
  Operator,
  Program,
  TypeCheckError,
  TypeCheckResult,
  TypeContext,
  TypeSignature,
} from '../types.js';

/**
 * Type system implementation
 */
export class TypeSystem implements ITypeSystem {
  private readonly operators: Map<string, Operator>;
  private readonly constants: Map<string, Constant>;

  constructor(configOrDsl: DSLConfig | IDSL) {
    if ('getOperator' in configOrDsl) {
      // It's an IDSL
      this.operators = configOrDsl.operators;
      this.constants = configOrDsl.constants;
    } else {
      // It's a DSLConfig
      this.operators = new Map(configOrDsl.operators.map((op) => [op.name, op]));
      this.constants = new Map(configOrDsl.constants.map((c) => [c.name, c]));
    }
  }

  /**
   * Type check a program (returns boolean for simple check)
   */
  check(program: Program, env?: TypeContext | Record<string, TypeSignature>): boolean {
    const result = this.checkWithDetails(program, env);
    return result.valid;
  }

  /**
   * Type check a program with full results
   */
  checkWithDetails(program: Program, env?: TypeContext | Record<string, TypeSignature>): TypeCheckResult {
    const errors: TypeCheckError[] = [];
    const context = this.normalizeContext(env);

    const inferredType = this.inferExpression(
      program.expression,
      context,
      errors
    );

    return {
      valid: errors.length === 0,
      inferredType: inferredType ?? undefined,
      errors,
    };
  }

  /**
   * Infer the type of an expression
   */
  infer(expression: Expression, env?: TypeContext | Record<string, TypeSignature>): TypeSignature | null {
    const errors: TypeCheckError[] = [];
    const context = this.normalizeContext(env);
    return this.inferExpression(expression, context, errors);
  }

  /**
   * Normalize context from Record or TypeContext
   */
  private normalizeContext(env?: TypeContext | Record<string, TypeSignature>): TypeContext {
    if (!env) {
      return { variables: new Map() };
    }
    if ('variables' in env && env.variables instanceof Map) {
      return env as TypeContext;
    }
    // It's a Record<string, TypeSignature>
    const variables = new Map<string, TypeSignature>();
    for (const [key, value] of Object.entries(env)) {
      variables.set(key, value);
    }
    return { variables };
  }

  /**
   * Unify two types
   */
  unify(a: TypeSignature, b: TypeSignature): TypeSignature | null {
    // Same type
    if (this.typeEquals(a, b)) return a;

    // Any unifies with anything
    if (a === 'any') return b;
    if (b === 'any') return a;

    // Numeric subtyping
    if ((a === 'int' && b === 'float') || (a === 'float' && b === 'int')) {
      return 'float';
    }

    // Function types
    if (typeof a === 'object' && typeof b === 'object') {
      if (a.kind === 'function' && b.kind === 'function') {
        if (a.inputs.length !== b.inputs.length) return null;

        const unifiedInputs: TypeSignature[] = [];
        for (let i = 0; i < a.inputs.length; i++) {
          const unified = this.unify(a.inputs[i], b.inputs[i]);
          if (!unified) return null;
          unifiedInputs.push(unified);
        }

        const unifiedOutput = this.unify(a.output, b.output);
        if (!unifiedOutput) return null;

        return { kind: 'function', inputs: unifiedInputs, output: unifiedOutput };
      }

      // Generic types
      if (a.kind === 'generic' || b.kind === 'generic') {
        return a.kind === 'generic' ? b : a;
      }
    }

    return null;
  }

  /**
   * Check if sub is a subtype of sup
   */
  isSubtype(sub: TypeSignature, sup: TypeSignature): boolean {
    // Any is a supertype of everything
    if (sup === 'any') return true;

    // Exact match
    if (this.typeEquals(sub, sup)) return true;

    // Handle function types
    if (typeof sub === 'object' && typeof sup === 'object') {
      if (sub.kind === 'function' && sup.kind === 'function') {
        // Contravariant in inputs, covariant in output
        if (sub.inputs.length !== sup.inputs.length) return false;

        // Check inputs (contravariant)
        for (let i = 0; i < sub.inputs.length; i++) {
          if (!this.isSubtype(sup.inputs[i], sub.inputs[i])) return false;
        }

        // Check output (covariant)
        return this.isSubtype(sub.output, sup.output);
      }
    }

    // Numeric subtyping: int <: float
    if (sub === 'int' && sup === 'float') return true;

    return false;
  }

  /**
   * Check if two types are equal
   */
  private typeEquals(a: TypeSignature, b: TypeSignature): boolean {
    if (typeof a === 'string' && typeof b === 'string') {
      return a === b;
    }

    if (typeof a === 'object' && typeof b === 'object') {
      if (a.kind !== b.kind) return false;

      if (a.kind === 'function' && b.kind === 'function') {
        if (a.inputs.length !== b.inputs.length) return false;
        for (let i = 0; i < a.inputs.length; i++) {
          if (!this.typeEquals(a.inputs[i], b.inputs[i])) return false;
        }
        return this.typeEquals(a.output, b.output);
      }

      if (a.kind === 'generic' && b.kind === 'generic') {
        return a.name === b.name;
      }
    }

    return false;
  }

  /**
   * Infer expression type with error collection
   */
  private inferExpression(
    expr: Expression,
    context: TypeContext,
    errors: TypeCheckError[]
  ): TypeSignature | null {
    switch (expr.kind) {
      case 'constant': {
        const constant = this.constants.get(expr.name);
        if (!constant) {
          errors.push({ message: `Unknown constant: ${expr.name}` });
          return null;
        }
        return constant.type;
      }

      case 'variable': {
        if (expr.name === 'input') {
          return 'any'; // Input type is typically any or inferred from context
        }
        const type = context.variables.get(expr.name);
        if (!type) {
          errors.push({ message: `Unknown variable: ${expr.name}` });
          return null;
        }
        return type;
      }

      case 'application': {
        const operator = this.operators.get(expr.operator);
        if (!operator) {
          errors.push({ message: `Unknown operator: ${expr.operator}` });
          return null;
        }

        // Check argument count
        if (expr.args.length !== operator.inputTypes.length) {
          errors.push({
            message: `Operator ${expr.operator} expects ${operator.inputTypes.length} arguments, got ${expr.args.length}`,
          });
          return null;
        }

        // Check argument types
        for (let i = 0; i < expr.args.length; i++) {
          const argType = this.inferExpression(expr.args[i], context, errors);
          if (argType) {
            const expectedType = operator.inputTypes[i];
            if (!this.isSubtype(argType, expectedType)) {
              errors.push({
                message: `Argument ${i} type mismatch`,
                expected: this.typeToString(expectedType),
                actual: this.typeToString(argType),
              });
            }
          }
        }

        return operator.outputType;
      }

      case 'lambda': {
        // Add parameter to context
        const newContext: TypeContext = {
          variables: new Map(context.variables),
        };
        newContext.variables.set(expr.parameter, expr.parameterType);

        // Infer body type
        const bodyType = this.inferExpression(expr.body, newContext, errors);
        if (!bodyType) return null;

        return {
          kind: 'function',
          inputs: [expr.parameterType],
          output: bodyType,
        };
      }

      default:
        errors.push({ message: `Unknown expression kind` });
        return null;
    }
  }

  /**
   * Convert type to string
   */
  private typeToString(type: TypeSignature): string {
    if (typeof type === 'string') return type;
    if (type.kind === 'function') {
      const inputs = type.inputs.map((t) => this.typeToString(t)).join(', ');
      return `(${inputs}) -> ${this.typeToString(type.output)}`;
    }
    if (type.kind === 'generic') return type.name;
    return JSON.stringify(type);
  }
}
