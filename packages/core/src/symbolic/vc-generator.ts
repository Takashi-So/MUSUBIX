/**
 * Verification Condition Generator
 *
 * Generates verification conditions (VCs) from requirements,
 * code, and domain models for formal verification.
 *
 * @packageDocumentation
 * @module symbolic/formal
 *
 * @see REQ-FV-005 - Verification Condition Generation
 * @see DES-SYMB-001 §4.8 - VerificationConditionGenerator
 * @see TSK-SYMB-010
 */

import type { Explanation, Evidence } from './types.js';
import type { EarsAstNode } from './ears-to-formal.js';

// ============================================================
// Verification Condition Types
// ============================================================

/**
 * Verification condition type
 */
export type VcType =
  | 'precondition'
  | 'postcondition'
  | 'invariant'
  | 'assertion'
  | 'type_constraint'
  | 'state_transition'
  | 'boundary';

/**
 * Verification condition status
 */
export type VcStatus = 'pending' | 'verified' | 'failed' | 'unknown' | 'timeout';

/**
 * Code element reference
 */
export interface CodeElementRef {
  /** File path */
  file?: string;
  /** Function/method name */
  function?: string;
  /** Line range */
  lineRange?: { start: number; end: number };
  /** Element type */
  elementType: 'function' | 'class' | 'method' | 'statement' | 'expression';
}

/**
 * Verification condition
 */
export interface VerificationCondition {
  /** Unique VC ID */
  id: string;
  /** VC type */
  type: VcType;
  /** Human-readable description */
  description: string;
  /** SMT-LIB expression */
  smtExpression: string;
  /** Source requirement ID(s) */
  requirementIds: string[];
  /** Code element this VC applies to */
  codeElement?: CodeElementRef;
  /** Dependencies on other VCs */
  dependencies?: string[];
  /** Current status */
  status: VcStatus;
  /** Generated at timestamp */
  generatedAt: string;
}

/**
 * VC generation result
 */
export interface VcGenerationResult {
  /** Generated verification conditions */
  conditions: VerificationCondition[];
  /** Combined SMT-LIB for all VCs */
  combinedSmtLib: string;
  /** Generation explanation */
  explanation: Explanation;
}

/**
 * Domain constraint for VC generation
 */
export interface DomainConstraint {
  /** Constraint name */
  name: string;
  /** Natural language description */
  description: string;
  /** Variables involved */
  variables: string[];
  /** SMT-LIB constraint expression */
  smtConstraint: string;
}

/**
 * Function contract for VC generation
 */
export interface FunctionContract {
  /** Function name */
  functionName: string;
  /** Preconditions */
  preconditions: string[];
  /** Postconditions */
  postconditions: string[];
  /** Invariants */
  invariants: string[];
  /** Parameter types and constraints */
  parameters: Array<{
    name: string;
    type: string;
    constraint?: string;
  }>;
  /** Return type and constraint */
  returns?: {
    type: string;
    constraint?: string;
  };
}

// ============================================================
// VC Generator
// ============================================================

/**
 * Configuration for VC generator
 */
export interface VcGeneratorConfig {
  /** Include boundary condition VCs */
  includeBoundaryChecks?: boolean;
  /** Include type constraint VCs */
  includeTypeConstraints?: boolean;
  /** Include state transition VCs */
  includeStateTransitions?: boolean;
  /** Maximum VCs per requirement */
  maxVcsPerRequirement?: number;
}

/**
 * Default configuration
 */
export const DEFAULT_VC_GENERATOR_CONFIG: VcGeneratorConfig = {
  includeBoundaryChecks: true,
  includeTypeConstraints: true,
  includeStateTransitions: true,
  maxVcsPerRequirement: 10,
};

let vcCounter = 0;

/**
 * Generate unique VC ID
 */
function generateVcId(): string {
  vcCounter++;
  const date = new Date().toISOString().slice(0, 10).replace(/-/g, '');
  return `VC-${date}-${String(vcCounter).padStart(4, '0')}`;
}

/**
 * Reset VC counter (for testing)
 */
export function resetVcCounter(): void {
  vcCounter = 0;
}

/**
 * Verification Condition Generator
 *
 * Generates verification conditions from various sources:
 * - EARS requirements (via AST)
 * - Function contracts
 * - Domain constraints
 * - Code analysis
 */
export class VerificationConditionGenerator {
  private readonly config: VcGeneratorConfig;

  constructor(config: Partial<VcGeneratorConfig> = {}) {
    this.config = { ...DEFAULT_VC_GENERATOR_CONFIG, ...config };
  }

  /**
   * Generate VCs from EARS AST nodes
   */
  fromEarsAst(astNodes: EarsAstNode[]): VcGenerationResult {
    const conditions: VerificationCondition[] = [];
    const evidence: Evidence[] = [];

    for (const ast of astNodes) {
      const vcs = this.generateFromAstNode(ast);
      conditions.push(...vcs);
      evidence.push({
        type: 'requirement',
        source: ast.requirementId,
        content: ast.originalText,
      });
    }

    return {
      conditions,
      combinedSmtLib: this.generateCombinedSmtLib(conditions),
      explanation: {
        summary: `Generated ${conditions.length} verification conditions from ${astNodes.length} EARS requirements`,
        reasoning: [
          `Analyzed ${astNodes.length} EARS AST nodes`,
          `Created VCs for preconditions, postconditions, and invariants`,
          conditions.length > 0 ? `Generated ${conditions.length} total VCs` : 'No VCs generated',
        ],
        evidence,
        relatedRequirements: astNodes.map((a) => a.requirementId),
      },
    };
  }

  /**
   * Generate VCs from function contracts
   */
  fromFunctionContract(contract: FunctionContract, requirementIds: string[]): VcGenerationResult {
    const conditions: VerificationCondition[] = [];

    // Precondition VCs
    for (let i = 0; i < contract.preconditions.length; i++) {
      conditions.push({
        id: generateVcId(),
        type: 'precondition',
        description: `Precondition ${i + 1} for ${contract.functionName}: ${contract.preconditions[i]}`,
        smtExpression: this.naturalToSmt(contract.preconditions[i]),
        requirementIds,
        codeElement: {
          function: contract.functionName,
          elementType: 'function',
        },
        status: 'pending',
        generatedAt: new Date().toISOString(),
      });
    }

    // Postcondition VCs
    for (let i = 0; i < contract.postconditions.length; i++) {
      conditions.push({
        id: generateVcId(),
        type: 'postcondition',
        description: `Postcondition ${i + 1} for ${contract.functionName}: ${contract.postconditions[i]}`,
        smtExpression: this.naturalToSmt(contract.postconditions[i]),
        requirementIds,
        codeElement: {
          function: contract.functionName,
          elementType: 'function',
        },
        status: 'pending',
        generatedAt: new Date().toISOString(),
      });
    }

    // Invariant VCs
    for (let i = 0; i < contract.invariants.length; i++) {
      conditions.push({
        id: generateVcId(),
        type: 'invariant',
        description: `Invariant ${i + 1} for ${contract.functionName}: ${contract.invariants[i]}`,
        smtExpression: this.naturalToSmt(contract.invariants[i]),
        requirementIds,
        codeElement: {
          function: contract.functionName,
          elementType: 'function',
        },
        status: 'pending',
        generatedAt: new Date().toISOString(),
      });
    }

    // Parameter constraint VCs
    if (this.config.includeTypeConstraints) {
      for (const param of contract.parameters) {
        if (param.constraint) {
          conditions.push({
            id: generateVcId(),
            type: 'type_constraint',
            description: `Type constraint for parameter ${param.name}: ${param.constraint}`,
            smtExpression: this.naturalToSmt(param.constraint),
            requirementIds,
            codeElement: {
              function: contract.functionName,
              elementType: 'function',
            },
            status: 'pending',
            generatedAt: new Date().toISOString(),
          });
        }
      }
    }

    return {
      conditions,
      combinedSmtLib: this.generateCombinedSmtLib(conditions),
      explanation: {
        summary: `Generated ${conditions.length} VCs from contract for ${contract.functionName}`,
        reasoning: [
          `${contract.preconditions.length} preconditions`,
          `${contract.postconditions.length} postconditions`,
          `${contract.invariants.length} invariants`,
        ],
        evidence: [],
        relatedRequirements: requirementIds,
      },
    };
  }

  /**
   * Generate VCs from domain constraints
   */
  fromDomainConstraints(
    constraints: DomainConstraint[],
    requirementIds: string[],
  ): VcGenerationResult {
    const conditions: VerificationCondition[] = [];

    for (const constraint of constraints) {
      conditions.push({
        id: generateVcId(),
        type: 'invariant',
        description: `Domain constraint: ${constraint.description}`,
        smtExpression: constraint.smtConstraint,
        requirementIds,
        status: 'pending',
        generatedAt: new Date().toISOString(),
      });
    }

    return {
      conditions,
      combinedSmtLib: this.generateCombinedSmtLib(conditions),
      explanation: {
        summary: `Generated ${conditions.length} VCs from domain constraints`,
        reasoning: constraints.map((c) => `Constraint: ${c.name}`),
        evidence: [],
        relatedRequirements: requirementIds,
      },
    };
  }

  /**
   * Generate boundary condition VCs
   */
  generateBoundaryVcs(
    variableName: string,
    minValue: number | undefined,
    maxValue: number | undefined,
    requirementIds: string[],
  ): VerificationCondition[] {
    if (!this.config.includeBoundaryChecks) {
      return [];
    }

    const conditions: VerificationCondition[] = [];

    if (minValue !== undefined) {
      conditions.push({
        id: generateVcId(),
        type: 'boundary',
        description: `${variableName} must be >= ${minValue}`,
        smtExpression: `(>= ${variableName} ${minValue})`,
        requirementIds,
        status: 'pending',
        generatedAt: new Date().toISOString(),
      });
    }

    if (maxValue !== undefined) {
      conditions.push({
        id: generateVcId(),
        type: 'boundary',
        description: `${variableName} must be <= ${maxValue}`,
        smtExpression: `(<= ${variableName} ${maxValue})`,
        requirementIds,
        status: 'pending',
        generatedAt: new Date().toISOString(),
      });
    }

    return conditions;
  }

  /**
   * Generate VCs from AST node
   */
  private generateFromAstNode(ast: EarsAstNode): VerificationCondition[] {
    const conditions: VerificationCondition[] = [];
    const systemId = ast.system.replace(/[^a-zA-Z0-9_]/g, '_').toLowerCase();

    switch (ast.pattern) {
      case 'ubiquitous': {
        // Always must hold
        conditions.push({
          id: generateVcId(),
          type: 'invariant',
          description: `System ${ast.system} shall always: ${ast.requirement}`,
          smtExpression: `(=> ${systemId}_active requirement_holds)`,
          requirementIds: [ast.requirementId],
          status: 'pending',
          generatedAt: new Date().toISOString(),
        });
        break;
      }

      case 'event-driven': {
        // Precondition: event occurred
        conditions.push({
          id: generateVcId(),
          type: 'precondition',
          description: `Event trigger: ${ast.event}`,
          smtExpression: `event_${ast.event?.replace(/[^a-zA-Z0-9_]/g, '_').toLowerCase()}_occurred`,
          requirementIds: [ast.requirementId],
          status: 'pending',
          generatedAt: new Date().toISOString(),
        });

        // Postcondition: requirement holds
        conditions.push({
          id: generateVcId(),
          type: 'postcondition',
          description: `Response: ${ast.requirement}`,
          smtExpression: `(=> event_occurred requirement_holds)`,
          requirementIds: [ast.requirementId],
          status: 'pending',
          generatedAt: new Date().toISOString(),
        });
        break;
      }

      case 'state-driven': {
        // State-based invariant
        conditions.push({
          id: generateVcId(),
          type: 'invariant',
          description: `While ${ast.state}, ${ast.system} shall: ${ast.requirement}`,
          smtExpression: `(=> (and ${systemId}_active state_holds) requirement_holds)`,
          requirementIds: [ast.requirementId],
          status: 'pending',
          generatedAt: new Date().toISOString(),
        });
        break;
      }

      case 'unwanted': {
        // Negation - shall NOT
        conditions.push({
          id: generateVcId(),
          type: 'assertion',
          description: `${ast.system} shall NOT: ${ast.unwantedBehavior}`,
          smtExpression: `(=> ${systemId}_active (not unwanted_behavior))`,
          requirementIds: [ast.requirementId],
          status: 'pending',
          generatedAt: new Date().toISOString(),
        });
        break;
      }

      case 'optional': {
        // Conditional
        conditions.push({
          id: generateVcId(),
          type: 'precondition',
          description: `Condition: ${ast.condition}`,
          smtExpression: `condition_${ast.condition?.replace(/[^a-zA-Z0-9_]/g, '_').toLowerCase()}_true`,
          requirementIds: [ast.requirementId],
          status: 'pending',
          generatedAt: new Date().toISOString(),
        });

        conditions.push({
          id: generateVcId(),
          type: 'postcondition',
          description: `If condition, then: ${ast.requirement}`,
          smtExpression: `(=> condition_true requirement_holds)`,
          requirementIds: [ast.requirementId],
          status: 'pending',
          generatedAt: new Date().toISOString(),
        });
        break;
      }
    }

    return conditions;
  }

  /**
   * Convert natural language constraint to SMT (simplified)
   */
  private naturalToSmt(natural: string): string {
    // Simple pattern matching for common constraints
    const lower = natural.toLowerCase();

    // "x > 0" patterns
    const comparisonMatch = natural.match(/(\w+)\s*(>=|<=|>|<|=|!=)\s*(\d+)/);
    if (comparisonMatch) {
      const [, varName, op, value] = comparisonMatch;
      const smtOp = op === '!=' ? 'distinct' : op === '=' ? '=' : op;
      return `(${smtOp} ${varName} ${value})`;
    }

    // "x is positive"
    if (lower.includes('positive')) {
      const varMatch = natural.match(/(\w+)\s+is\s+positive/i);
      if (varMatch) {
        return `(> ${varMatch[1]} 0)`;
      }
    }

    // "x is not null" or "x is defined"
    if (lower.includes('not null') || lower.includes('defined')) {
      const varMatch = natural.match(/(\w+)\s+is\s+(not null|defined)/i);
      if (varMatch) {
        return `(not (= ${varMatch[1]} null))`;
      }
    }

    // Default: create a named predicate
    const predName = natural.replace(/[^a-zA-Z0-9_]/g, '_').toLowerCase();
    return `${predName}_holds`;
  }

  /**
   * Generate combined SMT-LIB for all VCs
   */
  private generateCombinedSmtLib(conditions: VerificationCondition[]): string {
    if (conditions.length === 0) {
      return '; No verification conditions\n';
    }

    let smtLib = `; Combined Verification Conditions\n`;
    smtLib += `; Generated: ${new Date().toISOString()}\n`;
    smtLib += `; Total VCs: ${conditions.length}\n\n`;
    smtLib += `(set-logic QF_LIA)\n\n`;

    // Collect variables from expressions
    const variables = new Set<string>();
    for (const vc of conditions) {
      const matches = vc.smtExpression.match(/[a-z_][a-z0-9_]*/gi);
      if (matches) {
        for (const m of matches) {
          if (!['and', 'or', 'not', 'true', 'false', '=>', 'distinct'].includes(m)) {
            variables.add(m);
          }
        }
      }
    }

    // Declare variables
    smtLib += `; Variable declarations\n`;
    for (const v of variables) {
      smtLib += `(declare-const ${v} Bool)\n`;
    }
    smtLib += '\n';

    // Add assertions
    smtLib += `; Verification conditions\n`;
    for (const vc of conditions) {
      smtLib += `; ${vc.id}: ${vc.description}\n`;
      smtLib += `(assert ${vc.smtExpression})\n`;
    }

    smtLib += '\n(check-sat)\n';
    smtLib += '(get-model)\n';

    return smtLib;
  }
}

/**
 * Create VC generator
 */
export function createVerificationConditionGenerator(
  config?: Partial<VcGeneratorConfig>,
): VerificationConditionGenerator {
  return new VerificationConditionGenerator(config);
}
