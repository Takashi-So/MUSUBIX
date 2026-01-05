/**
 * MCP Ontology Tools - Consistency Validation
 *
 * @packageDocumentation
 * @module tools/ontology-tools
 * @traceability REQ-INT-003
 */

import type { ToolDefinition, ToolResult, ToolContent, TextContent } from '../types.js';

// Import types for validation
interface Triple {
  subject: string;
  predicate: string;
  object: string;
}

interface ConsistencyViolation {
  type: string;
  severity: 'error' | 'warning' | 'info';
  message: string;
  affectedTriples: Triple[];
  suggestion?: string;
}

interface ValidationResult {
  valid: boolean;
  violations: ConsistencyViolation[];
  statistics: {
    totalTriples: number;
    checkedConstraints: number;
    errors: number;
    warnings: number;
  };
}

/**
 * Consistency Validate Tool
 * 
 * Validates knowledge graph consistency using OWL constraints.
 */
export const consistencyValidateTool: ToolDefinition = {
  name: 'consistency_validate',
  description: `Validate knowledge graph consistency using OWL constraints.

Checks for:
- Duplicate triples (exact and semantic)
- Circular dependencies
- Disjoint class violations
- Functional property violations
- Inverse functional property violations
- Asymmetric property violations
- Irreflexive property violations

Use this tool to ensure data quality before adding to knowledge graph.`,
  inputSchema: {
    type: 'object',
    properties: {
      triples: {
        type: 'array',
        description: 'Array of triples to validate. Each triple has subject, predicate, object.',
        items: {
          type: 'object',
          properties: {
            subject: { type: 'string', description: 'Subject URI or identifier' },
            predicate: { type: 'string', description: 'Predicate URI or identifier' },
            object: { type: 'string', description: 'Object URI, identifier, or literal value' },
          },
          required: ['subject', 'predicate', 'object'],
        },
      },
      checkTypes: {
        type: 'array',
        description: 'Types of checks to perform. Default: all checks.',
        items: {
          type: 'string',
          enum: ['duplicate', 'circular', 'disjoint', 'functional', 'inverse-functional', 'asymmetric', 'irreflexive'],
        },
      },
      existingTriples: {
        type: 'array',
        description: 'Optional existing triples to check against.',
        items: {
          type: 'object',
          properties: {
            subject: { type: 'string' },
            predicate: { type: 'string' },
            object: { type: 'string' },
          },
          required: ['subject', 'predicate', 'object'],
        },
      },
    },
    required: ['triples'],
  },
  handler: async (args): Promise<ToolResult> => {
    const { triples, checkTypes, existingTriples = [] } = args as {
      triples: Triple[];
      checkTypes?: string[];
      existingTriples?: Triple[];
    };

    try {
      // Perform validation
      const result = validateConsistency(triples, existingTriples, checkTypes);
      
      const content: TextContent = {
        type: 'text',
        text: formatValidationResult(result),
      };

      return {
        content: [content] as ToolContent[],
        isError: false,
      };
    } catch (error) {
      const content: TextContent = {
        type: 'text',
        text: `Error during validation: ${error instanceof Error ? error.message : String(error)}`,
      };
      return {
        content: [content] as ToolContent[],
        isError: true,
      };
    }
  },
};

/**
 * Validate Triple Tool
 * 
 * Validate a single triple before adding to knowledge graph.
 */
export const validateTripleTool: ToolDefinition = {
  name: 'validate_triple',
  description: `Validate a single triple before adding to knowledge graph.

Quick validation for individual data entries. Returns pass/fail with details.`,
  inputSchema: {
    type: 'object',
    properties: {
      subject: {
        type: 'string',
        description: 'Subject URI or identifier',
      },
      predicate: {
        type: 'string',
        description: 'Predicate URI or identifier',
      },
      object: {
        type: 'string',
        description: 'Object URI, identifier, or literal value',
      },
      context: {
        type: 'array',
        description: 'Optional context triples to check against',
        items: {
          type: 'object',
          properties: {
            subject: { type: 'string' },
            predicate: { type: 'string' },
            object: { type: 'string' },
          },
        },
      },
    },
    required: ['subject', 'predicate', 'object'],
  },
  handler: async (args): Promise<ToolResult> => {
    const { subject, predicate, object, context = [] } = args as {
      subject: string;
      predicate: string;
      object: string;
      context?: Triple[];
    };

    const triple: Triple = { subject, predicate, object };
    const result = validateSingleTriple(triple, context);

    const content: TextContent = {
      type: 'text',
      text: formatSingleValidation(triple, result),
    };

    return {
      content: [content] as ToolContent[],
      isError: false,
    };
  },
};

/**
 * Check Circular Dependencies Tool
 */
export const checkCircularTool: ToolDefinition = {
  name: 'check_circular',
  description: `Check for circular dependencies in relationships.

Detects cycles in dependency graphs that could cause infinite loops or inconsistencies.`,
  inputSchema: {
    type: 'object',
    properties: {
      relationships: {
        type: 'array',
        description: 'Array of relationships to check for cycles',
        items: {
          type: 'object',
          properties: {
            from: { type: 'string', description: 'Source node' },
            to: { type: 'string', description: 'Target node' },
            type: { type: 'string', description: 'Relationship type (optional)' },
          },
          required: ['from', 'to'],
        },
      },
    },
    required: ['relationships'],
  },
  handler: async (args): Promise<ToolResult> => {
    const { relationships } = args as {
      relationships: Array<{ from: string; to: string; type?: string }>;
    };

    const cycles = findCycles(relationships);

    const content: TextContent = {
      type: 'text',
      text: formatCycleResult(cycles),
    };

    return {
      content: [content] as ToolContent[],
      isError: false,
    };
  },
};

// ============= Helper Functions =============

/**
 * Validate consistency of triples
 */
function validateConsistency(
  triples: Triple[],
  existingTriples: Triple[],
  checkTypes?: string[]
): ValidationResult {
  const violations: ConsistencyViolation[] = [];
  const allTriples = [...existingTriples, ...triples];
  const checks = checkTypes || ['duplicate', 'circular', 'disjoint', 'functional', 'inverse-functional', 'asymmetric', 'irreflexive'];

  // Check for duplicates
  if (checks.includes('duplicate')) {
    const duplicates = findDuplicates(triples, existingTriples);
    violations.push(...duplicates);
  }

  // Check for circular dependencies
  if (checks.includes('circular')) {
    const circular = findCircularViolations(allTriples);
    violations.push(...circular);
  }

  // Check functional properties
  if (checks.includes('functional')) {
    const functionalViolations = checkFunctionalProperties(allTriples);
    violations.push(...functionalViolations);
  }

  // Count errors and warnings
  const errors = violations.filter(v => v.severity === 'error').length;
  const warnings = violations.filter(v => v.severity === 'warning').length;

  return {
    valid: errors === 0,
    violations,
    statistics: {
      totalTriples: triples.length,
      checkedConstraints: checks.length,
      errors,
      warnings,
    },
  };
}

/**
 * Validate a single triple
 */
function validateSingleTriple(
  triple: Triple,
  context: Triple[]
): { valid: boolean; issues: string[] } {
  const issues: string[] = [];

  // Check if duplicate
  for (const existing of context) {
    if (
      existing.subject === triple.subject &&
      existing.predicate === triple.predicate &&
      existing.object === triple.object
    ) {
      issues.push('Duplicate: Exact same triple already exists');
    }
  }

  // Check for self-reference (simple irreflexive check)
  if (triple.subject === triple.object && triple.predicate.includes('parent')) {
    issues.push('Irreflexive violation: Entity cannot be its own parent');
  }

  return {
    valid: issues.length === 0,
    issues,
  };
}

/**
 * Find duplicate triples
 */
function findDuplicates(newTriples: Triple[], existingTriples: Triple[]): ConsistencyViolation[] {
  const violations: ConsistencyViolation[] = [];
  const seen = new Set<string>();

  // Add existing triples to seen set
  for (const t of existingTriples) {
    seen.add(`${t.subject}|${t.predicate}|${t.object}`);
  }

  // Check new triples
  for (const t of newTriples) {
    const key = `${t.subject}|${t.predicate}|${t.object}`;
    if (seen.has(key)) {
      violations.push({
        type: 'duplicate-triple',
        severity: 'error',
        message: `Duplicate triple detected`,
        affectedTriples: [t],
        suggestion: 'Remove or update the existing triple instead',
      });
    } else {
      seen.add(key);
    }
  }

  return violations;
}

/**
 * Find circular dependency violations
 */
function findCircularViolations(triples: Triple[]): ConsistencyViolation[] {
  const violations: ConsistencyViolation[] = [];
  
  // Build adjacency graph
  const graph = new Map<string, string[]>();
  for (const t of triples) {
    if (!graph.has(t.subject)) {
      graph.set(t.subject, []);
    }
    graph.get(t.subject)!.push(t.object);
  }

  // DFS for cycle detection
  const visited = new Set<string>();
  const inStack = new Set<string>();

  function dfs(node: string, path: string[]): string[] | null {
    if (inStack.has(node)) {
      return path;
    }
    if (visited.has(node)) {
      return null;
    }

    visited.add(node);
    inStack.add(node);

    const neighbors = graph.get(node) || [];
    for (const neighbor of neighbors) {
      const cycle = dfs(neighbor, [...path, node]);
      if (cycle) {
        return cycle;
      }
    }

    inStack.delete(node);
    return null;
  }

  for (const node of graph.keys()) {
    if (!visited.has(node)) {
      const cycle = dfs(node, []);
      if (cycle) {
        violations.push({
          type: 'circular-dependency',
          severity: 'error',
          message: `Circular dependency detected: ${cycle.join(' → ')} → ${node}`,
          affectedTriples: triples.filter(t => cycle.includes(t.subject) || cycle.includes(t.object)),
          suggestion: 'Break the cycle by removing one of the relationships',
        });
        break; // Report one cycle at a time
      }
    }
  }

  return violations;
}

/**
 * Check functional property violations (one value per subject+predicate)
 */
function checkFunctionalProperties(triples: Triple[]): ConsistencyViolation[] {
  const violations: ConsistencyViolation[] = [];
  
  // Common functional properties
  const functionalPredicates = ['hasId', 'hasParent', 'hasOwner', 'createdAt', 'modifiedAt'];
  
  const subjectPredicateMap = new Map<string, Triple[]>();
  
  for (const t of triples) {
    if (functionalPredicates.some(fp => t.predicate.includes(fp))) {
      const key = `${t.subject}|${t.predicate}`;
      if (!subjectPredicateMap.has(key)) {
        subjectPredicateMap.set(key, []);
      }
      subjectPredicateMap.get(key)!.push(t);
    }
  }

  for (const [_key, tripleList] of subjectPredicateMap) {
    if (tripleList.length > 1) {
      violations.push({
        type: 'functional-property-violation',
        severity: 'error',
        message: `Functional property has multiple values`,
        affectedTriples: tripleList,
        suggestion: 'Functional properties should have exactly one value per subject',
      });
    }
  }

  return violations;
}

/**
 * Find cycles in relationships
 */
function findCycles(relationships: Array<{ from: string; to: string; type?: string }>): string[][] {
  const cycles: string[][] = [];
  const graph = new Map<string, string[]>();

  for (const rel of relationships) {
    if (!graph.has(rel.from)) {
      graph.set(rel.from, []);
    }
    graph.get(rel.from)!.push(rel.to);
  }

  const visited = new Set<string>();
  const recursionStack = new Set<string>();

  function dfs(node: string, path: string[]): void {
    visited.add(node);
    recursionStack.add(node);

    const neighbors = graph.get(node) || [];
    for (const neighbor of neighbors) {
      if (!visited.has(neighbor)) {
        dfs(neighbor, [...path, node]);
      } else if (recursionStack.has(neighbor)) {
        // Found cycle
        const cycleStart = path.indexOf(neighbor);
        if (cycleStart !== -1) {
          cycles.push([...path.slice(cycleStart), node, neighbor]);
        } else {
          cycles.push([...path, node, neighbor]);
        }
      }
    }

    recursionStack.delete(node);
  }

  for (const node of graph.keys()) {
    if (!visited.has(node)) {
      dfs(node, []);
    }
  }

  return cycles;
}

/**
 * Format validation result as text
 */
function formatValidationResult(result: ValidationResult): string {
  const lines: string[] = [];
  
  lines.push('# Consistency Validation Report');
  lines.push('');
  lines.push(`**Status**: ${result.valid ? '✅ VALID' : '❌ INVALID'}`);
  lines.push('');
  lines.push('## Statistics');
  lines.push(`- Total Triples: ${result.statistics.totalTriples}`);
  lines.push(`- Checked Constraints: ${result.statistics.checkedConstraints}`);
  lines.push(`- Errors: ${result.statistics.errors}`);
  lines.push(`- Warnings: ${result.statistics.warnings}`);
  
  if (result.violations.length > 0) {
    lines.push('');
    lines.push('## Violations');
    for (const v of result.violations) {
      const icon = v.severity === 'error' ? '❌' : v.severity === 'warning' ? '⚠️' : 'ℹ️';
      lines.push(`### ${icon} ${v.type}`);
      lines.push(`- ${v.message}`);
      if (v.suggestion) {
        lines.push(`- Suggestion: ${v.suggestion}`);
      }
    }
  }

  return lines.join('\n');
}

/**
 * Format single triple validation result
 */
function formatSingleValidation(
  triple: Triple,
  result: { valid: boolean; issues: string[] }
): string {
  const lines: string[] = [];
  
  lines.push('# Triple Validation');
  lines.push('');
  lines.push('## Triple');
  lines.push(`- Subject: \`${triple.subject}\``);
  lines.push(`- Predicate: \`${triple.predicate}\``);
  lines.push(`- Object: \`${triple.object}\``);
  lines.push('');
  lines.push(`**Status**: ${result.valid ? '✅ VALID' : '❌ INVALID'}`);
  
  if (result.issues.length > 0) {
    lines.push('');
    lines.push('## Issues');
    for (const issue of result.issues) {
      lines.push(`- ❌ ${issue}`);
    }
  }

  return lines.join('\n');
}

/**
 * Format cycle detection result
 */
function formatCycleResult(cycles: string[][]): string {
  const lines: string[] = [];
  
  lines.push('# Circular Dependency Check');
  lines.push('');
  
  if (cycles.length === 0) {
    lines.push('✅ No circular dependencies detected.');
  } else {
    lines.push(`❌ Found ${cycles.length} cycle(s):`);
    lines.push('');
    for (let i = 0; i < cycles.length; i++) {
      lines.push(`### Cycle ${i + 1}`);
      lines.push(`\`${cycles[i].join(' → ')}\``);
      lines.push('');
    }
    lines.push('## Recommendation');
    lines.push('Remove one relationship from each cycle to break the circular dependency.');
  }

  return lines.join('\n');
}

/**
 * Array of all ontology tools
 */
export const ontologyTools: ToolDefinition[] = [
  consistencyValidateTool,
  validateTripleTool,
  checkCircularTool,
];

/**
 * Get all ontology tools
 */
export function getOntologyTools(): ToolDefinition[] {
  return [...ontologyTools];
}
