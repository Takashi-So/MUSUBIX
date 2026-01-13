/**
 * Status Machine Generator
 *
 * Generates TypeScript Status Machine files with transitions and validation
 *
 * @packageDocumentation
 * @module cli/generators/status-machine-generator
 *
 * @traceability REQ-SCF-003, REQ-SCF-004
 * @see DES-SCF-002 - Status Machine Generator Design
 * @see ADR-v3.3.0-001 - -sオプション構文決定（イコール区切り）
 */

import { writeFile, mkdir } from 'fs/promises';
import { join, dirname } from 'path';
import type { GeneratedFile } from './value-object-generator.js';

/**
 * Status transition definition
 */
export interface StatusTransition {
  from: string;
  to: string[];
}

/**
 * Status Machine specification
 */
export interface StatusMachineSpec {
  entityName: string;
  initialStatus?: string;
  statuses?: string[];
  transitions?: StatusTransition[];
}

/**
 * Generator configuration
 */
export interface StatusMachineGeneratorConfig {
  domain: string;
  outputDir: string;
  generateTests: boolean;
  generateEnum?: boolean;
}

// Re-export GeneratedFile from value-object-generator for consistency
export type { GeneratedFile } from './value-object-generator.js';

/**
 * Parse result from -s option
 */
export interface ParsedStatusOption {
  entityName: string;
  initialStatus: string;
}

/**
 * Status Machine Generator
 *
 * @description
 * Generates TypeScript Status Machine files following the pattern:
 * - Status type union
 * - Valid transitions map
 * - Transition validation function
 * - Transition execution function
 */
export class StatusMachineGenerator {
  constructor(private config: StatusMachineGeneratorConfig) {}

  /**
   * Generate Status Machine files
   */
  async generate(specs: StatusMachineSpec[]): Promise<GeneratedFile[]> {
    const files: GeneratedFile[] = [];

    for (const spec of specs) {
      const content = this.generateStatusMachineContent(spec);
      const fileName = this.toKebabCase(spec.entityName) + '-status.ts';
      const filePath = join(this.config.outputDir, 'src/statuses', fileName);

      files.push({
        path: filePath,
        content,
        type: 'status-machine',
      });
    }

    return files;
  }

  /**
   * Generate test files for Status Machines
   */
  async generateTests(specs: StatusMachineSpec[]): Promise<GeneratedFile[]> {
    if (!this.config.generateTests) {
      return [];
    }

    const files: GeneratedFile[] = [];

    for (const spec of specs) {
      const content = this.generateTestContent(spec);
      const fileName = this.toKebabCase(spec.entityName) + '-status.test.ts';
      const filePath = join(this.config.outputDir, '__tests__', fileName);

      files.push({
        path: filePath,
        content,
        type: 'test',
      });
    }

    return files;
  }

  /**
   * Write generated files to disk
   */
  async writeFiles(files: GeneratedFile[]): Promise<void> {
    for (const file of files) {
      await mkdir(dirname(file.path), { recursive: true });
      await writeFile(file.path, file.content, 'utf-8');
    }
  }

  /**
   * Parse -s option string (ADR-v3.3.0-001: イコール区切り)
   *
   * @example
   * parseStatusOption("Order=draft,Task=pending")
   * // Returns Map { "Order" => "draft", "Task" => "pending" }
   */
  static parseStatusOption(input: string): Map<string, string> {
    const map = new Map<string, string>();

    if (!input || input.trim() === '') {
      return map;
    }

    for (const pair of input.split(',')) {
      const trimmed = pair.trim();
      const eqIndex = trimmed.indexOf('=');

      if (eqIndex > 0) {
        const entity = trimmed.substring(0, eqIndex).trim();
        const status = trimmed.substring(eqIndex + 1).trim();

        if (entity && status) {
          map.set(entity, status);
        }
      } else {
        // No initial status specified - just entity name
        if (trimmed) {
          map.set(trimmed, '');
        }
      }
    }

    return map;
  }

  /**
   * Get default statuses for an entity
   */
  getDefaultStatuses(_entityName: string): string[] {
    return ['draft', 'active', 'completed', 'cancelled'];
  }

  /**
   * Generate default transitions
   */
  getDefaultTransitions(statuses: string[]): StatusTransition[] {
    if (statuses.length === 0) return [];

    const transitions: StatusTransition[] = [];

    // Default pattern: draft -> active -> completed, any -> cancelled
    if (statuses.includes('draft') && statuses.includes('active')) {
      transitions.push({ from: 'draft', to: ['active', 'cancelled'] });
    }

    if (statuses.includes('active') && statuses.includes('completed')) {
      transitions.push({ from: 'active', to: ['completed', 'cancelled'] });
    }

    if (statuses.includes('completed')) {
      transitions.push({ from: 'completed', to: [] });
    }

    if (statuses.includes('cancelled')) {
      transitions.push({ from: 'cancelled', to: [] });
    }

    // Fill in any missing statuses with empty transitions
    for (const status of statuses) {
      if (!transitions.find((t) => t.from === status)) {
        const nextIndex = statuses.indexOf(status) + 1;
        const nextStatuses = nextIndex < statuses.length ? [statuses[nextIndex]] : [];
        transitions.push({ from: status, to: nextStatuses });
      }
    }

    return transitions;
  }

  /**
   * Generate Status Machine TypeScript content
   */
  private generateStatusMachineContent(spec: StatusMachineSpec): string {
    const name = spec.entityName;
    const nameLower = this.toCamelCase(name);
    const domain = this.config.domain;
    const statuses = spec.statuses || this.getDefaultStatuses(name);
    const initialStatus = spec.initialStatus || statuses[0];
    const transitions = spec.transitions || this.getDefaultTransitions(statuses);

    const statusUnion = statuses.map((s) => `'${s}'`).join(' | ');
    const statusList = statuses.map((s) => `'${s}'`).join(', ');

    const transitionsMap = transitions
      .map((t) => {
        const toList = t.to.map((s) => `'${s}'`).join(', ');
        return `  '${t.from}': [${toList}],`;
      })
      .join('\n');

    const enumContent = this.config.generateEnum
      ? this.generateEnumContent(name, statuses)
      : '';

    return `/**
 * ${name} Status Machine
 *
 * @traceability REQ-SCF-003
 * @domain ${domain}
 */

import type { Result } from '../types/common.js';
import { ok, err } from '../types/common.js';
import { StatusTransitionError } from '../types/errors.js';

/**
 * ${name} status type
 */
export type ${name}Status = ${statusUnion};

/**
 * List of all valid ${name} statuses
 */
export const ${nameLower}StatusList: readonly ${name}Status[] = [${statusList}] as const;

/**
 * Default initial status for ${name}
 */
export const ${nameLower}DefaultStatus: ${name}Status = '${initialStatus}';

/**
 * Valid status transitions for ${name}
 */
export const valid${name}Transitions: Record<${name}Status, ${name}Status[]> = {
${transitionsMap}
};

/**
 * Check if a status transition is valid
 *
 * @param from - Current status
 * @param to - Target status
 * @returns true if transition is valid
 */
export function canTransition${name}(from: ${name}Status, to: ${name}Status): boolean {
  return valid${name}Transitions[from]?.includes(to) ?? false;
}

/**
 * Perform status transition on an entity
 *
 * @param entity - Entity with status field
 * @param newStatus - Target status
 * @returns Result containing updated entity or StatusTransitionError
 */
export function transition${name}<T extends { status: ${name}Status }>(
  entity: T,
  newStatus: ${name}Status
): Result<T, StatusTransitionError> {
  if (!canTransition${name}(entity.status, newStatus)) {
    return err(
      new StatusTransitionError(
        \`Cannot transition ${name} from '\${entity.status}' to '\${newStatus}'\`
      )
    );
  }
  return ok({ ...entity, status: newStatus });
}

/**
 * Get available transitions from current status
 *
 * @param currentStatus - Current status
 * @returns Array of valid target statuses
 */
export function getAvailable${name}Transitions(currentStatus: ${name}Status): ${name}Status[] {
  return valid${name}Transitions[currentStatus] ?? [];
}

/**
 * Type guard for ${name}Status
 *
 * @param value - Value to check
 * @returns true if value is a valid ${name}Status
 */
export function is${name}Status(value: unknown): value is ${name}Status {
  return typeof value === 'string' && ${nameLower}StatusList.includes(value as ${name}Status);
}
${enumContent}
`;
  }

  /**
   * Generate enum content (optional)
   */
  private generateEnumContent(name: string, statuses: string[]): string {
    const enumEntries = statuses
      .map((s) => `  ${this.toPascalCase(s)} = '${s}',`)
      .join('\n');

    return `
/**
 * ${name} status enum (alternative to union type)
 */
export enum ${name}StatusEnum {
${enumEntries}
}
`;
  }

  /**
   * Generate test file content
   */
  private generateTestContent(spec: StatusMachineSpec): string {
    const name = spec.entityName;
    const nameLower = this.toCamelCase(name);
    const domain = this.config.domain;
    const statuses = spec.statuses || this.getDefaultStatuses(name);
    const initialStatus = spec.initialStatus || statuses[0];

    return `/**
 * ${name} Status Machine Tests
 *
 * @traceability TST-SCF-003
 * @domain ${domain}
 */

import { describe, it, expect } from 'vitest';
import {
  ${nameLower}StatusList,
  ${nameLower}DefaultStatus,
  valid${name}Transitions,
  canTransition${name},
  transition${name},
  getAvailable${name}Transitions,
  is${name}Status,
} from '../src/statuses/${this.toKebabCase(name)}-status.js';

describe('${name} Status Machine', () => {
  describe('${nameLower}StatusList', () => {
    it('should contain all statuses', () => {
      expect(${nameLower}StatusList).toContain('${statuses[0]}');
      expect(${nameLower}StatusList.length).toBeGreaterThan(0);
    });
  });

  describe('${nameLower}DefaultStatus', () => {
    it('should be ${initialStatus}', () => {
      expect(${nameLower}DefaultStatus).toBe('${initialStatus}');
    });
  });

  describe('canTransition${name}', () => {
    it('should allow valid transitions', () => {
      const fromStatus = Object.keys(valid${name}Transitions)[0] as string;
      const toStatuses = valid${name}Transitions[fromStatus as keyof typeof valid${name}Transitions];
      
      if (toStatuses && toStatuses.length > 0) {
        expect(canTransition${name}(fromStatus as any, toStatuses[0])).toBe(true);
      }
    });

    it('should reject invalid transitions', () => {
      // Find a status with no valid transitions
      const terminalStatus = Object.entries(valid${name}Transitions)
        .find(([_, to]) => to.length === 0)?.[0];
      
      if (terminalStatus) {
        expect(canTransition${name}(terminalStatus as any, '${statuses[0]}')).toBe(false);
      }
    });
  });

  describe('transition${name}', () => {
    it('should perform valid transition', () => {
      const entity = { id: '1', status: '${statuses[0]}' as const };
      const validTo = valid${name}Transitions['${statuses[0]}'];
      
      if (validTo && validTo.length > 0) {
        const result = transition${name}(entity, validTo[0]);
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.status).toBe(validTo[0]);
        }
      }
    });

    it('should reject invalid transition', () => {
      const terminalStatus = Object.entries(valid${name}Transitions)
        .find(([_, to]) => to.length === 0)?.[0];
      
      if (terminalStatus) {
        const entity = { id: '1', status: terminalStatus as any };
        const result = transition${name}(entity, '${statuses[0]}');
        expect(result.isErr()).toBe(true);
      }
    });
  });

  describe('getAvailable${name}Transitions', () => {
    it('should return valid transitions', () => {
      const available = getAvailable${name}Transitions('${statuses[0]}');
      expect(Array.isArray(available)).toBe(true);
    });
  });

  describe('is${name}Status', () => {
    it('should return true for valid status', () => {
      expect(is${name}Status('${statuses[0]}')).toBe(true);
    });

    it('should return false for invalid status', () => {
      expect(is${name}Status('invalid')).toBe(false);
      expect(is${name}Status(null)).toBe(false);
      expect(is${name}Status(123)).toBe(false);
    });
  });
});
`;
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

  /**
   * Convert PascalCase to camelCase
   */
  private toCamelCase(str: string): string {
    return str.charAt(0).toLowerCase() + str.slice(1);
  }

  /**
   * Convert kebab-case or snake_case to PascalCase
   */
  private toPascalCase(str: string): string {
    return str
      .split(/[-_]/)
      .map((word) => word.charAt(0).toUpperCase() + word.slice(1).toLowerCase())
      .join('');
  }
}

/**
 * Create Status Machine Generator instance
 */
export function createStatusMachineGenerator(
  config: StatusMachineGeneratorConfig
): StatusMachineGenerator {
  return new StatusMachineGenerator(config);
}
