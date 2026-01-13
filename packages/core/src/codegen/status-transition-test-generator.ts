/**
 * Status Transition Test Generator
 *
 * Generates comprehensive test cases for status transition code.
 * Tests both valid and invalid transitions following BP-TEST-005 pattern.
 *
 * @module codegen/status-transition-test-generator
 * @since v3.1.0
 */

import type { StatusMachineSpec, StatusTransition } from './status-transition-generator.js';

/**
 * Test generation options
 */
export interface StatusTestGeneratorOptions {
  /** Include describe/it blocks (default: true) */
  includeDescribe?: boolean;
  /** Generate table-driven tests (default: true) */
  useTableDrivenTests?: boolean;
  /** Include edge case tests (default: true) */
  includeEdgeCases?: boolean;
  /** Test framework (default: 'vitest') */
  testFramework?: 'vitest' | 'jest';
  /** Include JSDoc comments (default: true) */
  includeJSDoc?: boolean;
}

/**
 * Generated test result
 */
export interface StatusTestGenerationResult {
  /** Generated test code */
  code: string;
  /** File name suggestion */
  fileName: string;
  /** Number of test cases */
  testCount: number;
  /** Number of valid transition tests */
  validTransitionTests: number;
  /** Number of invalid transition tests */
  invalidTransitionTests: number;
}

/**
 * Default options
 */
const DEFAULT_OPTIONS: Required<StatusTestGeneratorOptions> = {
  includeDescribe: true,
  useTableDrivenTests: true,
  includeEdgeCases: true,
  testFramework: 'vitest',
  includeJSDoc: true,
};

/**
 * Status Transition Test Generator
 *
 * Generates comprehensive test cases for status transitions.
 */
export class StatusTransitionTestGenerator {
  private options: Required<StatusTestGeneratorOptions>;

  constructor(options?: StatusTestGeneratorOptions) {
    this.options = { ...DEFAULT_OPTIONS, ...options };
  }

  /**
   * Generate test code for status transitions
   */
  generate(spec: StatusMachineSpec): StatusTestGenerationResult {
    const lines: string[] = [];
    const name = spec.name;
    // statusTypeName reserved for future use in type-safe test generation
    // const statusTypeName = `${name}Status`;
    const kebabName = this.toKebabCase(name);

    // Imports
    lines.push(this.generateImports(name, kebabName));
    lines.push('');

    // Build transition data
    const validTransitions = spec.transitions;
    const invalidTransitions = this.computeInvalidTransitions(spec);

    let testCount = 0;

    // Main describe block
    if (this.options.includeDescribe) {
      if (this.options.includeJSDoc) {
        lines.push('/**');
        lines.push(` * ${name} Status Transition Tests`);
        lines.push(' *');
        lines.push(' * @pattern BP-TEST-005 Status Transition Testing');
        if (spec.requirementId) {
          lines.push(` * @requirement ${spec.requirementId}`);
        }
        lines.push(' */');
      }
      lines.push(`describe('${name}Status Transitions', () => {`);
    }

    // Valid transitions tests
    if (this.options.useTableDrivenTests) {
      lines.push(...this.generateTableDrivenValidTests(name, validTransitions));
      testCount += validTransitions.length;
    } else {
      lines.push(...this.generateIndividualValidTests(name, validTransitions));
      testCount += validTransitions.length;
    }
    lines.push('');

    // Invalid transitions tests
    if (this.options.useTableDrivenTests) {
      lines.push(...this.generateTableDrivenInvalidTests(name, invalidTransitions));
      testCount += invalidTransitions.length;
    } else {
      lines.push(...this.generateIndividualInvalidTests(name, invalidTransitions));
      testCount += invalidTransitions.length;
    }

    // Edge case tests
    if (this.options.includeEdgeCases) {
      lines.push('');
      lines.push(...this.generateEdgeCaseTests(name, spec));
      testCount += this.countEdgeCaseTests(spec);
    }

    // Close describe
    if (this.options.includeDescribe) {
      lines.push('});');
    }

    return {
      code: lines.join('\n'),
      fileName: `${kebabName}-status.test.ts`,
      testCount,
      validTransitionTests: validTransitions.length,
      invalidTransitionTests: invalidTransitions.length,
    };
  }

  /**
   * Generate import statements
   */
  private generateImports(name: string, kebabName: string): string {
    const imports: string[] = [];

    if (this.options.testFramework === 'vitest') {
      imports.push("import { describe, it, expect } from 'vitest';");
    } else {
      imports.push("import { describe, it, expect } from '@jest/globals';");
    }

    imports.push(`import {`);
    imports.push(`  ${name}Status,`);
    imports.push(`  canTransition${name}Status,`);
    imports.push(`  valid${name}Transitions,`);
    imports.push(`  getNext${name}Statuses,`);
    imports.push(`} from './${kebabName}-status.js';`);

    return imports.join('\n');
  }

  /**
   * Compute all invalid transitions
   */
  private computeInvalidTransitions(spec: StatusMachineSpec): StatusTransition[] {
    const invalid: StatusTransition[] = [];
    const validSet = new Set(
      spec.transitions.map((t) => `${t.from}->${t.to}`)
    );

    for (const fromStatus of spec.statuses) {
      for (const toStatus of spec.statuses) {
        const key = `${fromStatus.name}->${toStatus.name}`;
        if (!validSet.has(key) && fromStatus.name !== toStatus.name) {
          invalid.push({ from: fromStatus.name, to: toStatus.name });
        }
      }
    }

    return invalid;
  }

  /**
   * Generate table-driven valid transition tests
   */
  private generateTableDrivenValidTests(name: string, transitions: StatusTransition[]): string[] {
    const lines: string[] = [];

    lines.push(`  describe('valid transitions', () => {`);
    lines.push(`    const validCases: Array<{ from: ${name}Status; to: ${name}Status }> = [`);

    for (const t of transitions) {
      lines.push(`      { from: '${t.from}', to: '${t.to}' },`);
    }

    lines.push(`    ];`);
    lines.push('');
    lines.push(`    it.each(validCases)('should allow transition from $from to $to', ({ from, to }) => {`);
    lines.push(`      expect(canTransition${name}Status(from, to)).toBe(true);`);
    lines.push(`    });`);
    lines.push(`  });`);

    return lines;
  }

  /**
   * Generate individual valid transition tests
   */
  private generateIndividualValidTests(name: string, transitions: StatusTransition[]): string[] {
    const lines: string[] = [];

    lines.push(`  describe('valid transitions', () => {`);

    for (const t of transitions) {
      lines.push(`    it('should allow ${t.from} -> ${t.to}', () => {`);
      lines.push(`      expect(canTransition${name}Status('${t.from}', '${t.to}')).toBe(true);`);
      lines.push(`    });`);
    }

    lines.push(`  });`);

    return lines;
  }

  /**
   * Generate table-driven invalid transition tests
   */
  private generateTableDrivenInvalidTests(name: string, transitions: StatusTransition[]): string[] {
    const lines: string[] = [];

    if (transitions.length === 0) {
      return lines;
    }

    lines.push(`  describe('invalid transitions', () => {`);
    lines.push(`    const invalidCases: Array<{ from: ${name}Status; to: ${name}Status }> = [`);

    for (const t of transitions) {
      lines.push(`      { from: '${t.from}', to: '${t.to}' },`);
    }

    lines.push(`    ];`);
    lines.push('');
    lines.push(`    it.each(invalidCases)('should reject transition from $from to $to', ({ from, to }) => {`);
    lines.push(`      expect(canTransition${name}Status(from, to)).toBe(false);`);
    lines.push(`    });`);
    lines.push(`  });`);

    return lines;
  }

  /**
   * Generate individual invalid transition tests
   */
  private generateIndividualInvalidTests(name: string, transitions: StatusTransition[]): string[] {
    const lines: string[] = [];

    if (transitions.length === 0) {
      return lines;
    }

    lines.push(`  describe('invalid transitions', () => {`);

    for (const t of transitions) {
      lines.push(`    it('should reject ${t.from} -> ${t.to}', () => {`);
      lines.push(`      expect(canTransition${name}Status('${t.from}', '${t.to}')).toBe(false);`);
      lines.push(`    });`);
    }

    lines.push(`  });`);

    return lines;
  }

  /**
   * Generate edge case tests
   */
  private generateEdgeCaseTests(name: string, spec: StatusMachineSpec): string[] {
    const lines: string[] = [];
    const initialStatus = spec.statuses.find((s) => s.isInitial);
    const terminalStatuses = spec.statuses.filter((s) => s.isTerminal);

    lines.push(`  describe('edge cases', () => {`);

    // Self-transition test
    lines.push(`    it('should reject self-transition', () => {`);
    const firstStatus = spec.statuses[0];
    lines.push(`      expect(canTransition${name}Status('${firstStatus.name}', '${firstStatus.name}')).toBe(false);`);
    lines.push(`    });`);

    // Terminal status test
    if (terminalStatuses.length > 0) {
      const terminal = terminalStatuses[0];
      lines.push('');
      lines.push(`    it('should have no transitions from terminal status', () => {`);
      lines.push(`      const nextStatuses = getNext${name}Statuses('${terminal.name}');`);
      lines.push(`      expect(nextStatuses).toHaveLength(0);`);
      lines.push(`    });`);
    }

    // Initial status test
    if (initialStatus) {
      const initialTransitions = spec.transitions.filter(
        (t) => t.from === initialStatus.name
      );
      if (initialTransitions.length > 0) {
        lines.push('');
        lines.push(`    it('should allow transitions from initial status', () => {`);
        lines.push(`      const nextStatuses = getNext${name}Statuses('${initialStatus.name}');`);
        lines.push(`      expect(nextStatuses.length).toBeGreaterThan(0);`);
        lines.push(`    });`);
      }
    }

    // Transition map completeness test
    lines.push('');
    lines.push(`    it('should have transitions defined for all statuses', () => {`);
    lines.push(`      const statuses: ${name}Status[] = [${spec.statuses.map((s) => `'${s.name}'`).join(', ')}];`);
    lines.push(`      for (const status of statuses) {`);
    lines.push(`        expect(valid${name}Transitions[status]).toBeDefined();`);
    lines.push(`      }`);
    lines.push(`    });`);

    lines.push(`  });`);

    return lines;
  }

  /**
   * Count edge case tests
   */
  private countEdgeCaseTests(spec: StatusMachineSpec): number {
    let count = 2; // self-transition + completeness
    const terminalStatuses = spec.statuses.filter((s) => s.isTerminal);
    const initialStatus = spec.statuses.find((s) => s.isInitial);

    if (terminalStatuses.length > 0) count++;
    if (initialStatus && spec.transitions.some((t) => t.from === initialStatus.name)) count++;

    return count;
  }

  /**
   * Convert PascalCase to kebab-case
   */
  private toKebabCase(str: string): string {
    return str
      .replace(/([a-z])([A-Z])/g, '$1-$2')
      .replace(/([A-Z])([A-Z][a-z])/g, '$1-$2')
      .toLowerCase();
  }
}

/**
 * Generate status transition tests (convenience function)
 */
export function generateStatusTransitionTests(
  spec: StatusMachineSpec,
  options?: StatusTestGeneratorOptions
): StatusTestGenerationResult {
  const generator = new StatusTransitionTestGenerator(options);
  return generator.generate(spec);
}
