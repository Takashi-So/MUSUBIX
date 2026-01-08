/**
 * TypeAnalyzer - Type-directed search and analysis
 *
 * REQ-LL-003: 型指向探索
 * DES-PHASE2-001: Abstraction Engine / TypeAnalyzer
 */

import type {
  TypeSignature,
  TypeContext,
  PatternCandidate,
} from '../types.js';

/**
 * TypeAnalyzer interface
 */
export interface TypeAnalyzer {
  /** Check if two types are compatible */
  isCompatible(source: TypeSignature, target: TypeSignature): boolean;

  /** Filter candidates by expected type */
  filterByType(candidates: PatternCandidate[], expectedType: TypeSignature): PatternCandidate[];

  /** Score a candidate by type match quality */
  scoreByTypeMatch(candidate: PatternCandidate, context: TypeContext): number;

  /** Infer type of an expression */
  inferType(expression: unknown): TypeSignature;

  /** Check if type A is subtype of type B */
  isSubtype(sub: TypeSignature, sup: TypeSignature): boolean;
}

/**
 * Default TypeAnalyzer implementation
 */
class TypeAnalyzerImpl implements TypeAnalyzer {
  isCompatible(source: TypeSignature, target: TypeSignature): boolean {
    // Same kind check
    if (source.kind !== target.kind) {
      // Special cases
      if (target.kind === 'union' && target.members) {
        return target.members.some((m) => this.isCompatible(source, m));
      }
      if (source.kind === 'primitive' && source.name === 'any') {
        return true;
      }
      if (target.kind === 'primitive' && target.name === 'any') {
        return true;
      }
      // unknown is compatible with anything (top type)
      if (source.kind === 'primitive' && source.name === 'unknown') {
        return true;
      }
      if (target.kind === 'primitive' && target.name === 'unknown') {
        return true;
      }
      return false;
    }

    switch (source.kind) {
      case 'primitive':
        return source.name === target.name || 
               target.name === 'any' || 
               source.name === 'any' ||
               source.name === 'unknown' ||
               target.name === 'unknown';

      case 'function':
        return this.isFunctionCompatible(source, target);

      case 'array':
        return this.isCompatible(
          source.elementType ?? { kind: 'primitive', name: 'unknown' },
          target.elementType ?? { kind: 'primitive', name: 'unknown' }
        );

      case 'object':
        return this.isObjectCompatible(source, target);

      case 'union':
        return this.isUnionCompatible(source, target);

      case 'intersection':
        return this.isIntersectionCompatible(source, target);

      case 'generic':
        // Generics match if they have the same type parameters
        return JSON.stringify(source.typeParams) === JSON.stringify(target.typeParams);

      default:
        return false;
    }
  }

  filterByType(candidates: PatternCandidate[], expectedType: TypeSignature): PatternCandidate[] {
    return candidates.filter((candidate) => {
      const candidateType = this.inferPatternType(candidate);
      return this.isCompatible(candidateType, expectedType);
    });
  }

  scoreByTypeMatch(candidate: PatternCandidate, context: TypeContext): number {
    const candidateType = this.inferPatternType(candidate);
    let score = 0;

    // Check compatibility with context variables
    for (const [name, type] of context.variables) {
      if (this.usesVariable(candidate, name)) {
        if (this.isCompatible(candidateType, type)) {
          score += 1;
        }
      }
    }

    // Check compatibility with context functions
    for (const [name, type] of context.functions) {
      if (this.usesFunction(candidate, name)) {
        if (this.isCompatible(candidateType, type)) {
          score += 1;
        }
      }
    }

    return score;
  }

  inferType(expression: unknown): TypeSignature {
    if (expression === null) {
      return { kind: 'primitive', name: 'null' };
    }

    if (expression === undefined) {
      return { kind: 'primitive', name: 'undefined' };
    }

    switch (typeof expression) {
      case 'string':
        return { kind: 'primitive', name: 'string' };
      case 'number':
        return { kind: 'primitive', name: 'number' };
      case 'boolean':
        return { kind: 'primitive', name: 'boolean' };
      case 'function':
        return { kind: 'function', paramTypes: [], returnType: { kind: 'primitive', name: 'unknown' } };
      case 'object':
        if (Array.isArray(expression)) {
          const elementType = expression.length > 0
            ? this.inferType(expression[0])
            : { kind: 'primitive' as const, name: 'unknown' };
          return { kind: 'array', elementType };
        }
        return this.inferObjectType(expression as Record<string, unknown>);
      default:
        return { kind: 'primitive', name: 'unknown' };
    }
  }

  isSubtype(sub: TypeSignature, sup: TypeSignature): boolean {
    // any is supertype of everything
    if (sup.kind === 'primitive' && sup.name === 'any') {
      return true;
    }

    // never is subtype of everything
    if (sub.kind === 'primitive' && sub.name === 'never') {
      return true;
    }

    // unknown is not subtype of anything except any and unknown
    if (sub.kind === 'primitive' && sub.name === 'unknown') {
      return sup.kind === 'primitive' && (sup.name === 'any' || sup.name === 'unknown');
    }

    return this.isCompatible(sub, sup);
  }

  // =========================================================================
  // Private methods
  // =========================================================================

  private isFunctionCompatible(source: TypeSignature, target: TypeSignature): boolean {
    // Contravariant parameter types, covariant return type
    const sourceParams = source.paramTypes ?? [];
    const targetParams = target.paramTypes ?? [];

    // Target can have fewer parameters (extra params are ignored)
    if (targetParams.length > sourceParams.length) {
      return false;
    }

    // Check parameter types (contravariant)
    for (let i = 0; i < targetParams.length; i++) {
      if (!this.isCompatible(targetParams[i], sourceParams[i])) {
        return false;
      }
    }

    // Check return type (covariant)
    const sourceReturn = source.returnType ?? { kind: 'primitive', name: 'void' };
    const targetReturn = target.returnType ?? { kind: 'primitive', name: 'void' };

    return this.isCompatible(sourceReturn, targetReturn);
  }

  private isObjectCompatible(source: TypeSignature, target: TypeSignature): boolean {
    const sourceProps = source.properties ?? {};
    const targetProps = target.properties ?? {};

    // Source must have all properties that target requires
    for (const [key, targetType] of Object.entries(targetProps)) {
      const sourceType = sourceProps[key];
      if (!sourceType) {
        return false;
      }
      if (!this.isCompatible(sourceType, targetType)) {
        return false;
      }
    }

    return true;
  }

  private isUnionCompatible(source: TypeSignature, target: TypeSignature): boolean {
    const sourceMembers = source.members ?? [];
    const targetMembers = target.members ?? [];

    // Every source member must be compatible with some target member
    return sourceMembers.every((sm) =>
      targetMembers.some((tm) => this.isCompatible(sm, tm))
    );
  }

  private isIntersectionCompatible(source: TypeSignature, target: TypeSignature): boolean {
    const sourceMembers = source.members ?? [];
    const targetMembers = target.members ?? [];

    // Source must satisfy all target intersection members
    return targetMembers.every((tm) =>
      sourceMembers.some((sm) => this.isCompatible(sm, tm))
    );
  }

  private inferPatternType(candidate: PatternCandidate): TypeSignature {
    // Infer type from pattern AST
    const ast = candidate.ast;

    switch (ast.type) {
      case 'Declaration':
        return { kind: 'primitive', name: 'void' };
      case 'ReturnStatement':
        return { kind: 'primitive', name: 'unknown' };
      case 'IfStatement':
      case 'ForLoop':
      case 'WhileLoop':
        return { kind: 'primitive', name: 'void' };
      case 'Expression':
        return this.inferType(ast.value);
      case 'NumberLiteral':
        return { kind: 'primitive', name: 'number' };
      case 'StringLiteral':
        return { kind: 'primitive', name: 'string' };
      case 'BooleanLiteral':
        return { kind: 'primitive', name: 'boolean' };
      case 'ArrayExpression':
        return { kind: 'array', elementType: { kind: 'primitive', name: 'unknown' } };
      case 'Identifier':
        return { kind: 'primitive', name: 'unknown' };
      default:
        return { kind: 'primitive', name: 'unknown' };
    }
  }

  private inferObjectType(obj: Record<string, unknown>): TypeSignature {
    const properties: Record<string, TypeSignature> = {};

    for (const [key, value] of Object.entries(obj)) {
      properties[key] = this.inferType(value);
    }

    return { kind: 'object', properties };
  }

  private usesVariable(candidate: PatternCandidate, name: string): boolean {
    // Check if the pattern uses a variable with the given name
    return this.astContains(candidate.ast, name);
  }

  private usesFunction(candidate: PatternCandidate, name: string): boolean {
    // Check if the pattern calls a function with the given name
    return this.astContains(candidate.ast, name);
  }

  private astContains(node: unknown, name: string): boolean {
    if (typeof node !== 'object' || node === null) {
      return node === name;
    }

    const obj = node as Record<string, unknown>;

    if (obj.name === name || obj.value === name) {
      return true;
    }

    if (Array.isArray(obj.children)) {
      return obj.children.some((child) => this.astContains(child, name));
    }

    return false;
  }
}

/**
 * Factory function to create a TypeAnalyzer
 */
export function createTypeAnalyzer(): TypeAnalyzer {
  return new TypeAnalyzerImpl();
}
