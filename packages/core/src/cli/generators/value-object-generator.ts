/**
 * Value Object Generator
 *
 * Generates TypeScript Value Object files with validation, equality, and type guards
 *
 * @packageDocumentation
 * @module cli/generators/value-object-generator
 *
 * @traceability REQ-SCF-001, REQ-SCF-002
 * @see DES-SCF-001 - Value Object Generator Design
 */

import { writeFile, mkdir } from 'fs/promises';
import { join, dirname } from 'path';

/**
 * Validation rule for Value Objects
 */
export interface ValidationRule {
  type: 'range' | 'pattern' | 'length' | 'custom';
  params?: Record<string, unknown>;
  message?: string;
}

/**
 * Value Object specification
 */
export interface ValueObjectSpec {
  name: string;
  fields?: ValueObjectField[];
  validationType?: 'range' | 'format' | 'custom' | 'none';
  validationRules?: ValidationRule[];
}

/**
 * Value Object field definition
 */
export interface ValueObjectField {
  name: string;
  type: string;
  readonly?: boolean;
}

/**
 * Generator configuration
 */
export interface ValueObjectGeneratorConfig {
  domain: string;
  outputDir: string;
  generateTests: boolean;
}

/**
 * Generated file result
 */
export interface GeneratedFile {
  path: string;
  content: string;
  type: 'value-object' | 'status-machine' | 'entity' | 'repository' | 'test' | 'index' | 'unknown';
}

/**
 * Value Object Generator
 *
 * @description
 * Generates TypeScript Value Object files following the function-based pattern:
 * - Immutable interface definition
 * - Factory function with validation
 * - Equality comparison function
 * - Type guard function
 */
export class ValueObjectGenerator {
  constructor(private config: ValueObjectGeneratorConfig) {}

  /**
   * Generate Value Object files
   */
  async generate(specs: ValueObjectSpec[]): Promise<GeneratedFile[]> {
    const files: GeneratedFile[] = [];

    for (const spec of specs) {
      const content = this.generateValueObjectContent(spec);
      const fileName = this.toKebabCase(spec.name) + '.ts';
      const filePath = join(this.config.outputDir, 'src/value-objects', fileName);

      files.push({
        path: filePath,
        content,
        type: 'value-object',
      });
    }

    return files;
  }

  /**
   * Generate test files for Value Objects
   */
  async generateTests(specs: ValueObjectSpec[]): Promise<GeneratedFile[]> {
    if (!this.config.generateTests) {
      return [];
    }

    const files: GeneratedFile[] = [];

    for (const spec of specs) {
      const content = this.generateTestContent(spec);
      const fileName = this.toKebabCase(spec.name) + '.test.ts';
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
   * Generate Value Object TypeScript content
   */
  private generateValueObjectContent(spec: ValueObjectSpec): string {
    const name = spec.name;
    const nameLower = this.toCamelCase(name);
    const domain = this.config.domain;
    const fields = spec.fields || this.getDefaultFields(name);

    const fieldDefinitions = fields
      .map((f) => `  readonly ${f.name}: ${f.type};`)
      .join('\n');

    const fieldParams = fields.map((f) => `${f.name}: ${f.type}`).join(', ');

    const fieldAssignments = fields.map((f) => f.name).join(', ');

    const equalityChecks = fields
      .map((f) => `a.${f.name} === b.${f.name}`)
      .join(' && ');

    const typeGuardChecks = fields
      .map((f) => `'${f.name}' in value`)
      .join(' && ');

    const validation = this.generateValidation(spec, fields);

    return `/**
 * ${name} Value Object
 *
 * @traceability REQ-SCF-001
 * @domain ${domain}
 */

import type { Result } from '../types/common.js';
import { ok, err } from '../types/common.js';
import { ValidationError } from '../types/errors.js';

/**
 * ${name} Value Object interface
 */
export interface ${name} {
${fieldDefinitions}
}

/**
 * Create a new ${name} Value Object
 *
 * @param ${fieldParams.split(', ').map(p => p.split(':')[0]).join(', ')} - Value Object fields
 * @returns Result containing ${name} or ValidationError
 */
export function create${name}(${fieldParams}): Result<${name}, ValidationError> {
${validation}
  return ok({ ${fieldAssignments} });
}

/**
 * Check equality of two ${name} Value Objects
 *
 * @param a - First ${name}
 * @param b - Second ${name}
 * @returns true if equal
 */
export function ${nameLower}Equals(a: ${name}, b: ${name}): boolean {
  return ${equalityChecks};
}

/**
 * Type guard for ${name}
 *
 * @param value - Value to check
 * @returns true if value is ${name}
 */
export function is${name}(value: unknown): value is ${name} {
  return typeof value === 'object' && value !== null && ${typeGuardChecks};
}
`;
  }

  /**
   * Generate validation code
   */
  private generateValidation(spec: ValueObjectSpec, fields: ValueObjectField[]): string {
    if (spec.validationType === 'none' || !spec.validationRules?.length) {
      return '  // No validation rules defined';
    }

    const validations: string[] = [];

    for (const rule of spec.validationRules || []) {
      switch (rule.type) {
        case 'range':
          const { min, max, field } = rule.params as { min?: number; max?: number; field?: string };
          const rangeField = field || fields[0]?.name || 'value';
          if (min !== undefined && max !== undefined) {
            validations.push(
              `  if (${rangeField} < ${min} || ${rangeField} > ${max}) {\n    return err(new ValidationError('${spec.name} ${rangeField} must be between ${min} and ${max}'));\n  }`
            );
          } else if (min !== undefined) {
            validations.push(
              `  if (${rangeField} < ${min}) {\n    return err(new ValidationError('${spec.name} ${rangeField} must be at least ${min}'));\n  }`
            );
          } else if (max !== undefined) {
            validations.push(
              `  if (${rangeField} > ${max}) {\n    return err(new ValidationError('${spec.name} ${rangeField} must be at most ${max}'));\n  }`
            );
          }
          break;

        case 'pattern':
          const { pattern, field: patternField } = rule.params as { pattern: string; field?: string };
          const pField = patternField || fields[0]?.name || 'value';
          validations.push(
            `  if (!/${pattern}/.test(${pField})) {\n    return err(new ValidationError('${spec.name} ${pField} has invalid format'));\n  }`
          );
          break;

        case 'length':
          const { minLength, maxLength, field: lengthField } = rule.params as {
            minLength?: number;
            maxLength?: number;
            field?: string;
          };
          const lField = lengthField || fields[0]?.name || 'value';
          if (minLength !== undefined) {
            validations.push(
              `  if (${lField}.length < ${minLength}) {\n    return err(new ValidationError('${spec.name} ${lField} must be at least ${minLength} characters'));\n  }`
            );
          }
          if (maxLength !== undefined) {
            validations.push(
              `  if (${lField}.length > ${maxLength}) {\n    return err(new ValidationError('${spec.name} ${lField} must be at most ${maxLength} characters'));\n  }`
            );
          }
          break;
      }
    }

    return validations.length > 0 ? validations.join('\n\n') : '  // No validation rules defined';
  }

  /**
   * Generate test file content
   */
  private generateTestContent(spec: ValueObjectSpec): string {
    const name = spec.name;
    const nameLower = this.toCamelCase(name);
    const fields = spec.fields || this.getDefaultFields(name);
    const domain = this.config.domain;

    const validParams = fields
      .map((f) => this.getDefaultValue(f))
      .join(', ');

    return `/**
 * ${name} Value Object Tests
 *
 * @traceability TST-SCF-001
 * @domain ${domain}
 */

import { describe, it, expect } from 'vitest';
import { create${name}, ${nameLower}Equals, is${name} } from '../src/value-objects/${this.toKebabCase(name)}.js';

describe('${name}', () => {
  describe('create${name}', () => {
    it('should create valid ${name}', () => {
      const result = create${name}(${validParams});
      expect(result.isOk()).toBe(true);
    });

    it('should return error for invalid input', () => {
      // Add specific invalid input tests based on validation rules
    });
  });

  describe('${nameLower}Equals', () => {
    it('should return true for equal values', () => {
      const result1 = create${name}(${validParams});
      const result2 = create${name}(${validParams});
      
      if (result1.isOk() && result2.isOk()) {
        expect(${nameLower}Equals(result1.value, result2.value)).toBe(true);
      }
    });

    it('should return false for different values', () => {
      // Add test with different values
    });
  });

  describe('is${name}', () => {
    it('should return true for valid ${name} object', () => {
      const result = create${name}(${validParams});
      if (result.isOk()) {
        expect(is${name}(result.value)).toBe(true);
      }
    });

    it('should return false for invalid objects', () => {
      expect(is${name}(null)).toBe(false);
      expect(is${name}(undefined)).toBe(false);
      expect(is${name}({})).toBe(false);
      expect(is${name}('string')).toBe(false);
    });
  });
});
`;
  }

  /**
   * Get default fields based on Value Object name
   */
  private getDefaultFields(name: string): ValueObjectField[] {
    const lowerName = name.toLowerCase();

    // Common Value Object patterns
    if (lowerName.includes('price') || lowerName.includes('money') || lowerName.includes('amount')) {
      return [
        { name: 'amount', type: 'number', readonly: true },
        { name: 'currency', type: "'JPY' | 'USD'", readonly: true },
      ];
    }

    if (lowerName.includes('email')) {
      return [{ name: 'value', type: 'string', readonly: true }];
    }

    if (lowerName.includes('quantity') || lowerName.includes('count')) {
      return [{ name: 'value', type: 'number', readonly: true }];
    }

    if (lowerName.includes('date') || lowerName.includes('time')) {
      return [{ name: 'value', type: 'Date', readonly: true }];
    }

    if (lowerName.includes('address')) {
      return [
        { name: 'street', type: 'string', readonly: true },
        { name: 'city', type: 'string', readonly: true },
        { name: 'postalCode', type: 'string', readonly: true },
      ];
    }

    // Default: single value field
    return [{ name: 'value', type: 'string', readonly: true }];
  }

  /**
   * Get default value for a field (for test generation)
   */
  private getDefaultValue(field: ValueObjectField): string {
    switch (field.type) {
      case 'number':
        return '100';
      case 'string':
        return "'test-value'";
      case 'Date':
        return 'new Date()';
      case "'JPY' | 'USD'":
        return "'JPY'";
      default:
        if (field.type.includes('|')) {
          // Union type - pick first option
          const firstOption = field.type.split('|')[0].trim();
          return firstOption;
        }
        return "'test'";
    }
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
}

/**
 * Create Value Object Generator instance
 */
export function createValueObjectGenerator(
  config: ValueObjectGeneratorConfig
): ValueObjectGenerator {
  return new ValueObjectGenerator(config);
}
