/**
 * @fileoverview TypeScript to Lean specification converter
 * @module @nahisaho/musubix-lean/converters
 * @traceability REQ-LEAN-TS-001 to REQ-LEAN-TS-004
 */

import { ok, err, type Result } from 'neverthrow';
import type {
  TypeScriptFunction,
  TypeScriptParameter,
  LeanFunctionSpec,
  LeanHypothesis,
  LeanExpression,
  Precondition,
  Postcondition,
  Invariant,
} from '../types.js';
import { TypeScriptSpecificationError } from '../errors.js';

/**
 * TypeScript to Lean type mapping
 * @traceability REQ-LEAN-TS-001
 */
const TYPE_MAPPING: Record<string, string> = {
  number: 'Int',
  string: 'String',
  boolean: 'Bool',
  void: 'Unit',
  undefined: 'Unit',
  null: 'Unit',
  any: 'α', // Generic type
  unknown: 'α',
  never: 'Empty',
  bigint: 'Int',
  symbol: 'String',
  object: 'α',
};

/**
 * Convert TypeScript type to Lean type
 * @traceability REQ-LEAN-TS-001
 */
export function convertTypeToLean(tsType: string): string {
  // Handle basic types
  const basicType = TYPE_MAPPING[tsType.toLowerCase()];
  if (basicType) {
    return basicType;
  }

  // Handle Array<T> or T[]
  const arrayMatch = tsType.match(/^Array<(.+)>$|^(.+)\[\]$/);
  if (arrayMatch) {
    const elementType = arrayMatch[1] || arrayMatch[2];
    return `List ${convertTypeToLean(elementType)}`;
  }

  // Handle T | null or T | undefined (Option type)
  const optionMatch = tsType.match(/^(.+?)\s*\|\s*(?:null|undefined)$/);
  if (optionMatch) {
    return `Option ${convertTypeToLean(optionMatch[1])}`;
  }

  // Handle Result<T, E>
  const resultMatch = tsType.match(/^Result<(.+?),\s*(.+?)>$/);
  if (resultMatch) {
    return `Except ${convertTypeToLean(resultMatch[2])} ${convertTypeToLean(resultMatch[1])}`;
  }

  // Handle Promise<T>
  const promiseMatch = tsType.match(/^Promise<(.+)>$/);
  if (promiseMatch) {
    return `IO ${convertTypeToLean(promiseMatch[1])}`;
  }

  // Handle Map<K, V>
  const mapMatch = tsType.match(/^Map<(.+?),\s*(.+?)>$/);
  if (mapMatch) {
    return `List (${convertTypeToLean(mapMatch[1])} × ${convertTypeToLean(mapMatch[2])})`;
  }

  // Handle Set<T>
  const setMatch = tsType.match(/^Set<(.+)>$/);
  if (setMatch) {
    return `List ${convertTypeToLean(setMatch[1])}`;
  }

  // Handle Record<K, V>
  const recordMatch = tsType.match(/^Record<(.+?),\s*(.+?)>$/);
  if (recordMatch) {
    return `List (${convertTypeToLean(recordMatch[1])} × ${convertTypeToLean(recordMatch[2])})`;
  }

  // Handle tuple types
  if (tsType.startsWith('[') && tsType.endsWith(']')) {
    const elements = tsType.slice(1, -1).split(',').map((t) => t.trim());
    const leanTypes = elements.map(convertTypeToLean);
    return `(${leanTypes.join(' × ')})`;
  }

  // Handle union types (simplified)
  if (tsType.includes('|')) {
    // For now, treat unions as the first type
    const firstType = tsType.split('|')[0].trim();
    return convertTypeToLean(firstType);
  }

  // Custom/unknown types become generic
  return tsType.charAt(0).toUpperCase() + tsType.slice(1);
}

/**
 * Convert parameter to Lean parameter declaration
 */
function convertParameter(param: TypeScriptParameter): string {
  const leanType = convertTypeToLean(param.type);
  if (param.optional) {
    return `(${param.name} : Option ${leanType})`;
  }
  return `(${param.name} : ${leanType})`;
}

/**
 * Convert precondition to Lean hypothesis
 * @traceability REQ-LEAN-TS-002
 */
function convertPrecondition(
  precondition: Precondition,
  index: number
): LeanHypothesis {
  const name = `h_pre_${index}`;
  const leanExpr = convertExpressionToLean(precondition.expression);

  return {
    name,
    type: leanExpr,
    leanCode: `${name} : ${leanExpr}`,
  };
}

/**
 * Convert postcondition to Lean expression
 * @traceability REQ-LEAN-TS-003
 */
function convertPostcondition(postcondition: Postcondition): LeanExpression {
  const leanExpr = convertExpressionToLean(postcondition.expression);

  return {
    type: leanExpr,
    leanCode: leanExpr,
  };
}

/**
 * Convert JavaScript/TypeScript expression to Lean expression
 */
function convertExpressionToLean(expr: string): string {
  return (
    expr
      // Comparison operators
      .replace(/===/g, '=')
      .replace(/!==/g, '≠')
      .replace(/!=/g, '≠')
      .replace(/>=/g, '≥')
      .replace(/<=/g, '≤')
      // Logical operators
      .replace(/&&/g, '∧')
      .replace(/\|\|/g, '∨')
      .replace(/!/g, '¬')
      // Array methods
      .replace(/\.length/g, '.length')
      .replace(/\.includes\(([^)]+)\)/g, '∈ $1')
      // Property access
      .replace(/\./g, '.')
      // Clean up whitespace
      .replace(/\s+/g, ' ')
      .trim()
  );
}

/**
 * Build Lean function specification from TypeScript function
 * @traceability REQ-LEAN-TS-001
 */
export function buildFunctionSpec(
  func: TypeScriptFunction
): Result<LeanFunctionSpec, TypeScriptSpecificationError> {
  try {
    const params = func.parameters.map(convertParameter).join(' ');
    const returnType = convertTypeToLean(func.returnType);
    const typeSignature = params
      ? `${params} → ${returnType}`
      : returnType;

    const preconditionHypotheses = func.preconditions.map((pre, i) =>
      convertPrecondition(pre, i)
    );

    const postconditionGoal: LeanExpression =
      func.postconditions.length > 0
        ? convertPostcondition(func.postconditions[0])
        : { type: 'True', leanCode: 'True' };

    // Build Lean code
    const hypothesesCode = preconditionHypotheses
      .map((h) => `  (${h.leanCode})`)
      .join('\n');

    const leanCode = `
/-- Specification for ${func.name}
    @file ${func.filePath}
-/
def ${func.name}_spec
${hypothesesCode}
  : ${postconditionGoal.leanCode} := by
  sorry -- TODO: Implement specification
`;

    return ok({
      functionName: func.name,
      typeSignature,
      preconditionHypotheses,
      postconditionGoal,
      leanCode,
    });
  } catch (error) {
    return err(
      new TypeScriptSpecificationError(
        func.name,
        error instanceof Error ? error.message : String(error)
      )
    );
  }
}

/**
 * Extract preconditions from JSDoc comments
 * @traceability REQ-LEAN-TS-002
 */
export function extractPreconditionsFromJSDoc(jsdoc: string): Precondition[] {
  const preconditions: Precondition[] = [];
  const preRegex = /@precondition\s+(.+?)(?=@|\*\/|$)/gi;

  let match;
  while ((match = preRegex.exec(jsdoc)) !== null) {
    const text = match[1].trim();
    // Try to parse as expression
    const exprMatch = text.match(/^{(.+?)}\s*(.*)$/);
    if (exprMatch) {
      preconditions.push({
        expression: exprMatch[1].trim(),
        description: exprMatch[2].trim() || exprMatch[1].trim(),
        source: 'jsdoc',
      });
    } else {
      preconditions.push({
        expression: text,
        description: text,
        source: 'jsdoc',
      });
    }
  }

  return preconditions;
}

/**
 * Extract postconditions from JSDoc comments
 * @traceability REQ-LEAN-TS-003
 */
export function extractPostconditionsFromJSDoc(jsdoc: string): Postcondition[] {
  const postconditions: Postcondition[] = [];
  const postRegex = /@postcondition\s+(.+?)(?=@|\*\/|$)/gi;

  let match;
  while ((match = postRegex.exec(jsdoc)) !== null) {
    const text = match[1].trim();
    const exprMatch = text.match(/^{(.+?)}\s*(.*)$/);
    if (exprMatch) {
      postconditions.push({
        expression: exprMatch[1].trim(),
        description: exprMatch[2].trim() || exprMatch[1].trim(),
        source: 'jsdoc',
      });
    } else {
      postconditions.push({
        expression: text,
        description: text,
        source: 'jsdoc',
      });
    }
  }

  return postconditions;
}

/**
 * Extract invariants from JSDoc comments
 * @traceability REQ-LEAN-TS-004
 */
export function extractInvariantsFromJSDoc(jsdoc: string): Invariant[] {
  const invariants: Invariant[] = [];
  const invRegex = /@invariant\s+(.+?)(?=@|\*\/|$)/gi;

  let match;
  while ((match = invRegex.exec(jsdoc)) !== null) {
    const text = match[1].trim();
    const exprMatch = text.match(/^{(.+?)}\s*(.*)$/);
    if (exprMatch) {
      invariants.push({
        expression: exprMatch[1].trim(),
        description: exprMatch[2].trim() || exprMatch[1].trim(),
      });
    } else {
      invariants.push({
        expression: text,
        description: text,
      });
    }
  }

  return invariants;
}

/**
 * TypeScriptSpecifier class implementation
 * @traceability REQ-LEAN-TS-001
 */
export class TypeScriptSpecifier {
  /**
   * Specify a TypeScript function as Lean specification
   */
  specify(
    func: TypeScriptFunction
  ): Result<LeanFunctionSpec, TypeScriptSpecificationError> {
    return buildFunctionSpec(func);
  }

  /**
   * Extract function signature info (simplified)
   */
  extractSignature(
    _code: string,
    _funcName: string
  ): { params: TypeScriptParameter[]; returnType: string } {
    // This would use ts-morph for real implementation
    return { params: [], returnType: 'void' };
  }

  /**
   * Infer preconditions from function body
   */
  inferPreconditions(_func: TypeScriptFunction): Precondition[] {
    // Would analyze type guards, validation checks
    return [];
  }

  /**
   * Infer postconditions from function body
   */
  inferPostconditions(_func: TypeScriptFunction): Postcondition[] {
    // Would analyze return statements, Result types
    return [];
  }

  /**
   * Convert type to Lean
   */
  convertType(tsType: string): string {
    return convertTypeToLean(tsType);
  }
}
