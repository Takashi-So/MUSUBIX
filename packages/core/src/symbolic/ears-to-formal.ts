/**
 * EARS to Formal Specification Converter
 *
 * Converts EARS (Easy Approach to Requirements Syntax) requirements
 * to formal specifications in SMT-LIB format for verification.
 *
 * @packageDocumentation
 * @module symbolic/formal
 *
 * @see REQ-FV-001 - EARS→Formal Transformation
 * @see DES-SYMB-001 §4.4 - EarsToFormalSpecConverter
 * @see TSK-SYMB-009
 */

import type { Explanation, Evidence, EarsRequirement } from './types.js';

// ============================================================
// EARS Pattern Types
// ============================================================

/**
 * EARS pattern types
 */
export type EarsPatternType =
  | 'ubiquitous'
  | 'event-driven'
  | 'state-driven'
  | 'unwanted'
  | 'optional';

/**
 * EARS AST Node - Structured representation of EARS requirement
 */
export interface EarsAstNode {
  /** Requirement ID */
  requirementId: string;
  /** Pattern type */
  pattern: EarsPatternType;
  /** System/actor name */
  system: string;
  /** The main requirement action */
  requirement: string;
  /** Trigger event (for event-driven) */
  event?: string;
  /** State condition (for state-driven) */
  state?: string;
  /** Precondition (for optional) */
  condition?: string;
  /** Behavior to avoid (for unwanted) */
  unwantedBehavior?: string;
  /** Original text */
  originalText: string;
  /** Parsed at timestamp */
  parsedAt: string;
}

/**
 * SMT-LIB output with metadata
 */
export interface SmtLibOutput {
  /** SMT-LIB formatted string */
  smtLib: string;
  /** Source requirement ID */
  requirementId: string;
  /** Variables declared */
  variables: SmtVariable[];
  /** Assertions generated */
  assertions: SmtAssertion[];
  /** Generation explanation */
  explanation: Explanation;
}

/**
 * SMT variable declaration
 */
export interface SmtVariable {
  name: string;
  type: 'Bool' | 'Int' | 'Real' | 'String' | `(Array ${string} ${string})`;
  description?: string;
}

/**
 * SMT assertion
 */
export interface SmtAssertion {
  /** Assertion name/label */
  label: string;
  /** SMT-LIB expression */
  expression: string;
  /** Derived from */
  source: 'requirement' | 'constraint' | 'invariant';
}

/**
 * Formal specification (combined output)
 */
export interface FormalSpecification {
  /** All parsed AST nodes */
  astNodes: EarsAstNode[];
  /** All SMT-LIB outputs */
  smtOutputs: SmtLibOutput[];
  /** Combined SMT-LIB file content */
  combinedSmtLib: string;
  /** Overall explanation */
  explanation: Explanation;
}

// ============================================================
// EARS Parser
// ============================================================

/**
 * EARS pattern regex definitions
 */
const EARS_PATTERNS = {
  // THE <system> SHALL <requirement>
  ubiquitous: /^THE\s+(.+?)\s+SHALL\s+(.+)$/i,
  // WHEN <event>, THE <system> SHALL <response>
  eventDriven: /^WHEN\s+(.+?),\s+THE\s+(.+?)\s+SHALL\s+(.+)$/i,
  // WHILE <state>, THE <system> SHALL <response>
  stateDriven: /^WHILE\s+(.+?),\s+THE\s+(.+?)\s+SHALL\s+(.+)$/i,
  // THE <system> SHALL NOT <behavior>
  unwanted: /^THE\s+(.+?)\s+SHALL\s+NOT\s+(.+)$/i,
  // IF <condition>, THEN THE <system> SHALL <response>
  optional: /^IF\s+(.+?),\s+THEN\s+THE\s+(.+?)\s+SHALL\s+(.+)$/i,
};

/**
 * Parse single EARS requirement text into AST
 */
export function parseEarsRequirement(
  requirementId: string,
  text: string,
): { success: true; ast: EarsAstNode } | { success: false; error: string } {
  const trimmedText = text.trim();

  // Try each pattern
  const eventMatch = trimmedText.match(EARS_PATTERNS.eventDriven);
  if (eventMatch) {
    return {
      success: true,
      ast: {
        requirementId,
        pattern: 'event-driven',
        event: eventMatch[1].trim(),
        system: eventMatch[2].trim(),
        requirement: eventMatch[3].trim(),
        originalText: trimmedText,
        parsedAt: new Date().toISOString(),
      },
    };
  }

  const stateMatch = trimmedText.match(EARS_PATTERNS.stateDriven);
  if (stateMatch) {
    return {
      success: true,
      ast: {
        requirementId,
        pattern: 'state-driven',
        state: stateMatch[1].trim(),
        system: stateMatch[2].trim(),
        requirement: stateMatch[3].trim(),
        originalText: trimmedText,
        parsedAt: new Date().toISOString(),
      },
    };
  }

  const optionalMatch = trimmedText.match(EARS_PATTERNS.optional);
  if (optionalMatch) {
    return {
      success: true,
      ast: {
        requirementId,
        pattern: 'optional',
        condition: optionalMatch[1].trim(),
        system: optionalMatch[2].trim(),
        requirement: optionalMatch[3].trim(),
        originalText: trimmedText,
        parsedAt: new Date().toISOString(),
      },
    };
  }

  const unwantedMatch = trimmedText.match(EARS_PATTERNS.unwanted);
  if (unwantedMatch) {
    return {
      success: true,
      ast: {
        requirementId,
        pattern: 'unwanted',
        system: unwantedMatch[1].trim(),
        unwantedBehavior: unwantedMatch[2].trim(),
        requirement: `NOT ${unwantedMatch[2].trim()}`,
        originalText: trimmedText,
        parsedAt: new Date().toISOString(),
      },
    };
  }

  const ubiquitousMatch = trimmedText.match(EARS_PATTERNS.ubiquitous);
  if (ubiquitousMatch) {
    return {
      success: true,
      ast: {
        requirementId,
        pattern: 'ubiquitous',
        system: ubiquitousMatch[1].trim(),
        requirement: ubiquitousMatch[2].trim(),
        originalText: trimmedText,
        parsedAt: new Date().toISOString(),
      },
    };
  }

  return {
    success: false,
    error: `Unable to parse EARS pattern from: "${trimmedText}"`,
  };
}

// ============================================================
// SMT-LIB Generator
// ============================================================

/**
 * Sanitize identifier for SMT-LIB
 */
function sanitizeSmtId(s: string): string {
  return s
    .replace(/[^a-zA-Z0-9_]/g, '_')
    .replace(/^[0-9]/, '_$&')
    .toLowerCase();
}

/**
 * Extract variables from requirement text
 */
function extractVariables(requirement: string, system: string): SmtVariable[] {
  const variables: SmtVariable[] = [];

  // Add system state variable
  variables.push({
    name: `${sanitizeSmtId(system)}_active`,
    type: 'Bool',
    description: `${system} is active`,
  });

  // Extract potential numeric values
  const numericMatches = requirement.match(/\d+/g);
  if (numericMatches) {
    numericMatches.forEach((num, idx) => {
      variables.push({
        name: `value_${idx}`,
        type: 'Int',
        description: `Numeric value ${num} from requirement`,
      });
    });
  }

  // Extract potential state/property references
  const stateWords = ['valid', 'invalid', 'exists', 'available', 'ready', 'complete'];
  stateWords.forEach((word) => {
    if (requirement.toLowerCase().includes(word)) {
      variables.push({
        name: `is_${word}`,
        type: 'Bool',
        description: `State: ${word}`,
      });
    }
  });

  return variables;
}

/**
 * Generate SMT-LIB from EARS AST node
 */
export function generateSmtLib(ast: EarsAstNode): SmtLibOutput {
  const systemId = sanitizeSmtId(ast.system);
  const reqId = sanitizeSmtId(ast.requirementId);
  const variables = extractVariables(ast.requirement, ast.system);
  const assertions: SmtAssertion[] = [];

  // Generate SMT-LIB header
  let smtLib = `; SMT-LIB for ${ast.requirementId}\n`;
  smtLib += `; Pattern: ${ast.pattern}\n`;
  smtLib += `; Original: ${ast.originalText}\n`;
  smtLib += `(set-logic QF_LIA)\n\n`;

  // Declare variables
  smtLib += `; Variable declarations\n`;
  for (const v of variables) {
    smtLib += `(declare-const ${v.name} ${v.type})\n`;
  }
  smtLib += '\n';

  // Generate pattern-specific assertions
  smtLib += `; Assertions for ${ast.pattern} pattern\n`;

  switch (ast.pattern) {
    case 'ubiquitous': {
      // Always true when system is active
      const assertionExpr = `(=> ${systemId}_active requirement_${reqId}_holds)`;
      assertions.push({
        label: `req_${reqId}`,
        expression: assertionExpr,
        source: 'requirement',
      });
      smtLib += `(declare-const requirement_${reqId}_holds Bool)\n`;
      smtLib += `(assert ${assertionExpr})\n`;
      break;
    }

    case 'event-driven': {
      // When event occurs and system active, requirement holds
      const eventId = sanitizeSmtId(ast.event ?? 'event');
      smtLib += `(declare-const ${eventId}_occurred Bool)\n`;
      smtLib += `(declare-const requirement_${reqId}_holds Bool)\n`;
      const assertionExpr = `(=> (and ${systemId}_active ${eventId}_occurred) requirement_${reqId}_holds)`;
      assertions.push({
        label: `req_${reqId}`,
        expression: assertionExpr,
        source: 'requirement',
      });
      smtLib += `(assert ${assertionExpr})\n`;
      break;
    }

    case 'state-driven': {
      // While state holds and system active, requirement holds
      const stateId = sanitizeSmtId(ast.state ?? 'state');
      smtLib += `(declare-const ${stateId}_holds Bool)\n`;
      smtLib += `(declare-const requirement_${reqId}_holds Bool)\n`;
      const assertionExpr = `(=> (and ${systemId}_active ${stateId}_holds) requirement_${reqId}_holds)`;
      assertions.push({
        label: `req_${reqId}`,
        expression: assertionExpr,
        source: 'requirement',
      });
      smtLib += `(assert ${assertionExpr})\n`;
      break;
    }

    case 'unwanted': {
      // System shall NOT exhibit behavior
      smtLib += `(declare-const unwanted_${reqId}_behavior Bool)\n`;
      const assertionExpr = `(=> ${systemId}_active (not unwanted_${reqId}_behavior))`;
      assertions.push({
        label: `req_${reqId}`,
        expression: assertionExpr,
        source: 'requirement',
      });
      smtLib += `(assert ${assertionExpr})\n`;
      break;
    }

    case 'optional': {
      // If condition then requirement holds
      const conditionId = sanitizeSmtId(ast.condition ?? 'condition');
      smtLib += `(declare-const ${conditionId}_true Bool)\n`;
      smtLib += `(declare-const requirement_${reqId}_holds Bool)\n`;
      const assertionExpr = `(=> (and ${systemId}_active ${conditionId}_true) requirement_${reqId}_holds)`;
      assertions.push({
        label: `req_${reqId}`,
        expression: assertionExpr,
        source: 'requirement',
      });
      smtLib += `(assert ${assertionExpr})\n`;
      break;
    }
  }

  // Add check-sat
  smtLib += '\n(check-sat)\n';
  smtLib += '(get-model)\n';

  const evidence: Evidence[] = [
    {
      type: 'requirement',
      source: ast.requirementId,
      content: ast.originalText,
    },
  ];

  return {
    smtLib,
    requirementId: ast.requirementId,
    variables,
    assertions,
    explanation: {
      summary: `Generated SMT-LIB specification for ${ast.pattern} requirement ${ast.requirementId}`,
      reasoning: [
        `Parsed EARS ${ast.pattern} pattern`,
        `Identified system: ${ast.system}`,
        `Generated ${variables.length} variables and ${assertions.length} assertions`,
      ],
      evidence,
      relatedRequirements: [ast.requirementId],
    },
  };
}

// ============================================================
// Main Converter Class
// ============================================================

/**
 * Configuration for EARS to Formal Spec converter
 */
export interface EarsToFormalConfig {
  /** Include comments in output */
  includeComments?: boolean;
  /** Target SMT solver */
  targetSolver?: 'z3' | 'cvc5' | 'generic';
  /** Logic to use */
  logic?: string;
}

/**
 * Default configuration
 */
export const DEFAULT_EARS_TO_FORMAL_CONFIG: EarsToFormalConfig = {
  includeComments: true,
  targetSolver: 'z3',
  logic: 'QF_LIA',
};

/**
 * EARS to Formal Specification Converter
 *
 * Transforms EARS requirements into SMT-LIB formal specifications
 * for use with theorem provers like Z3.
 */
export class EarsToFormalSpecConverter {
  private readonly config: EarsToFormalConfig;

  constructor(config: Partial<EarsToFormalConfig> = {}) {
    this.config = { ...DEFAULT_EARS_TO_FORMAL_CONFIG, ...config };
  }

  /**
   * Parse EARS requirement text
   */
  parse(
    requirementId: string,
    text: string,
  ): { success: true; ast: EarsAstNode } | { success: false; error: string } {
    return parseEarsRequirement(requirementId, text);
  }

  /**
   * Convert single EARS requirement to SMT-LIB
   */
  convert(requirement: EarsRequirement): SmtLibOutput {
    const parseResult = this.parse(requirement.id, requirement.text);

    if (!parseResult.success) {
      // Return empty SMT-LIB with error explanation
      return {
        smtLib: `; Error: ${parseResult.error}\n`,
        requirementId: requirement.id,
        variables: [],
        assertions: [],
        explanation: {
          summary: `Failed to parse requirement ${requirement.id}`,
          reasoning: [parseResult.error],
          evidence: [],
          relatedRequirements: [requirement.id],
        },
      };
    }

    return generateSmtLib(parseResult.ast);
  }

  /**
   * Convert multiple EARS requirements to formal specification
   */
  convertAll(requirements: EarsRequirement[]): FormalSpecification {
    const astNodes: EarsAstNode[] = [];
    const smtOutputs: SmtLibOutput[] = [];
    const errors: string[] = [];

    for (const req of requirements) {
      const parseResult = this.parse(req.id, req.text);

      if (parseResult.success) {
        astNodes.push(parseResult.ast);
        smtOutputs.push(generateSmtLib(parseResult.ast));
      } else {
        errors.push(`${req.id}: ${parseResult.error}`);
      }
    }

    // Generate combined SMT-LIB
    const combinedSmtLib = this.generateCombinedSmtLib(smtOutputs);

    return {
      astNodes,
      smtOutputs,
      combinedSmtLib,
      explanation: {
        summary: `Converted ${astNodes.length}/${requirements.length} EARS requirements to SMT-LIB`,
        reasoning: [
          `Successfully parsed ${astNodes.length} requirements`,
          errors.length > 0 ? `Failed to parse ${errors.length} requirements` : '',
          `Generated combined SMT-LIB specification`,
        ].filter(Boolean),
        evidence: requirements.map((r) => ({
          type: 'requirement' as const,
          source: r.id,
          content: r.text,
        })),
        relatedRequirements: requirements.map((r) => r.id),
      },
    };
  }

  /**
   * Generate combined SMT-LIB file
   */
  private generateCombinedSmtLib(outputs: SmtLibOutput[]): string {
    if (outputs.length === 0) {
      return '; No requirements to verify\n';
    }

    let combined = `; Combined SMT-LIB Specification\n`;
    combined += `; Generated: ${new Date().toISOString()}\n`;
    combined += `; Requirements: ${outputs.length}\n\n`;
    combined += `(set-logic ${this.config.logic})\n\n`;

    // Collect all unique variables
    const allVariables = new Map<string, SmtVariable>();
    for (const output of outputs) {
      for (const v of output.variables) {
        if (!allVariables.has(v.name)) {
          allVariables.set(v.name, v);
        }
      }
    }

    // Declare all variables
    combined += `; Variable declarations\n`;
    for (const v of allVariables.values()) {
      combined += `(declare-const ${v.name} ${v.type})`;
      if (v.description && this.config.includeComments) {
        combined += ` ; ${v.description}`;
      }
      combined += '\n';
    }
    combined += '\n';

    // Add all assertions
    for (const output of outputs) {
      combined += `; Assertions for ${output.requirementId}\n`;
      // Extract assertions from the individual SMT-LIB (simplified approach)
      const assertionLines = output.smtLib
        .split('\n')
        .filter((line) => line.startsWith('(declare-const') || line.startsWith('(assert'));
      for (const line of assertionLines) {
        combined += line + '\n';
      }
      combined += '\n';
    }

    combined += '(check-sat)\n';
    combined += '(get-model)\n';

    return combined;
  }
}

/**
 * Create EARS to Formal Spec converter
 */
export function createEarsToFormalSpecConverter(
  config?: Partial<EarsToFormalConfig>,
): EarsToFormalSpecConverter {
  return new EarsToFormalSpecConverter(config);
}
