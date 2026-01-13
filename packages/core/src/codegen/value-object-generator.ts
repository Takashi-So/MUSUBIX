/**
 * Value Object Generator
 *
 * Generates TypeScript Value Object code from specifications.
 *
 * @packageDocumentation
 * @module codegen/value-object-generator
 *
 * @see BP-CODE-003 - Value Objects
 * @see BP-CODE-004 - Function-based Value Objects
 * @see BP-CODE-005 - Result Type
 * @see TSK-GEN-001 - VO自動生成タスク
 */

/**
 * Value Object specification
 */
export interface ValueObjectSpec {
  /** Value Object name (PascalCase) */
  name: string;
  /** Description */
  description?: string;
  /** Properties */
  properties: VOProperty[];
  /** Validation rules */
  validations?: VOValidation[];
  /** Related requirement ID */
  requirementId?: string;
}

/**
 * Value Object property
 */
export interface VOProperty {
  /** Property name (camelCase) */
  name: string;
  /** TypeScript type */
  type: string;
  /** Description */
  description?: string;
  /** Whether this is readonly */
  readonly?: boolean;
}

/**
 * Validation rule
 */
export interface VOValidation {
  /** Target property */
  property: string;
  /** Validation type */
  type: 'min' | 'max' | 'minLength' | 'maxLength' | 'pattern' | 'custom';
  /** Validation value */
  value: number | string;
  /** Error message */
  message: string;
}

/**
 * Generator options
 */
export interface VOGeneratorOptions {
  /** Use Result type for factory functions */
  useResultType?: boolean;
  /** Include JSDoc comments */
  includeJSDoc?: boolean;
  /** Export style */
  exportStyle?: 'named' | 'default';
  /** Include test file */
  generateTest?: boolean;
}

const DEFAULT_OPTIONS: Required<VOGeneratorOptions> = {
  useResultType: true,
  includeJSDoc: true,
  exportStyle: 'named',
  generateTest: true,
};

/**
 * Generation result
 */
export interface VOGenerationResult {
  /** Generated main file content */
  code: string;
  /** Generated test file content (if requested) */
  testCode?: string;
  /** File name suggestion */
  fileName: string;
  /** Test file name */
  testFileName?: string;
}

/**
 * Value Object Generator
 *
 * Generates TypeScript Value Object code following best practices.
 */
export class ValueObjectGenerator {
  private options: Required<VOGeneratorOptions>;

  constructor(options?: VOGeneratorOptions) {
    this.options = { ...DEFAULT_OPTIONS, ...options };
  }

  /**
   * Generate Value Object code from specification
   */
  generate(spec: ValueObjectSpec): VOGenerationResult {
    const lines: string[] = [];
    const { name, description, properties, validations, requirementId } = spec;

    // Header comment
    if (this.options.includeJSDoc) {
      lines.push('/**');
      lines.push(` * ${name} Value Object`);
      if (description) {
        lines.push(` *`);
        lines.push(` * ${description}`);
      }
      lines.push(` *`);
      lines.push(` * @packageDocumentation`);
      if (requirementId) {
        lines.push(` * @see ${requirementId}`);
      }
      lines.push(` */`);
      lines.push('');
    }

    // Result type import if needed
    if (this.options.useResultType) {
      lines.push(`import { Result, ok, err } from './result.js';`);
      lines.push('');
    }

    // Validation error class
    lines.push(`export class ${name}ValidationError extends Error {`);
    lines.push(`  constructor(message: string) {`);
    lines.push(`    super(message);`);
    lines.push(`    this.name = '${name}ValidationError';`);
    lines.push(`  }`);
    lines.push(`}`);
    lines.push('');

    // Interface
    if (this.options.includeJSDoc) {
      lines.push('/**');
      lines.push(` * ${name} Value Object interface`);
      lines.push(' */');
    }
    lines.push(`export interface ${name} {`);
    for (const prop of properties) {
      if (this.options.includeJSDoc && prop.description) {
        lines.push(`  /** ${prop.description} */`);
      }
      const readonly = prop.readonly !== false ? 'readonly ' : '';
      lines.push(`  ${readonly}${prop.name}: ${prop.type};`);
    }
    lines.push(`}`);
    lines.push('');

    // Input type for factory
    lines.push(`export interface ${name}Input {`);
    for (const prop of properties) {
      lines.push(`  ${prop.name}: ${prop.type};`);
    }
    lines.push(`}`);
    lines.push('');

    // Factory function
    const returnType = this.options.useResultType
      ? `Result<${name}, ${name}ValidationError>`
      : name;

    if (this.options.includeJSDoc) {
      lines.push('/**');
      lines.push(` * Create a ${name} Value Object`);
      lines.push(` *`);
      lines.push(` * @param input - Input values`);
      lines.push(` * @returns ${this.options.useResultType ? 'Result with' : ''} ${name} or validation error`);
      lines.push(' */');
    }
    lines.push(`export function create${name}(input: ${name}Input): ${returnType} {`);

    // Validation logic
    if (validations && validations.length > 0) {
      for (const validation of validations) {
        const condition = this.generateValidationCondition(validation);
        if (this.options.useResultType) {
          lines.push(`  if (${condition}) {`);
          lines.push(`    return err(new ${name}ValidationError('${validation.message}'));`);
          lines.push(`  }`);
        } else {
          lines.push(`  if (${condition}) {`);
          lines.push(`    throw new ${name}ValidationError('${validation.message}');`);
          lines.push(`  }`);
        }
      }
      lines.push('');
    }

    // Return value
    if (this.options.useResultType) {
      lines.push(`  return ok({`);
    } else {
      lines.push(`  return {`);
    }
    for (const prop of properties) {
      lines.push(`    ${prop.name}: input.${prop.name},`);
    }
    if (this.options.useResultType) {
      lines.push(`  });`);
    } else {
      lines.push(`  };`);
    }
    lines.push(`}`);

    // Generate test code if requested
    let testCode: string | undefined;
    if (this.options.generateTest) {
      testCode = this.generateTestCode(spec);
    }

    const fileName = this.toKebabCase(name) + '.ts';
    const testFileName = this.toKebabCase(name) + '.test.ts';

    return {
      code: lines.join('\n'),
      testCode,
      fileName,
      testFileName,
    };
  }

  /**
   * Generate validation condition
   */
  private generateValidationCondition(validation: VOValidation): string {
    const prop = `input.${validation.property}`;
    
    switch (validation.type) {
      case 'min':
        return `${prop} < ${validation.value}`;
      case 'max':
        return `${prop} > ${validation.value}`;
      case 'minLength':
        return `${prop}.length < ${validation.value}`;
      case 'maxLength':
        return `${prop}.length > ${validation.value}`;
      case 'pattern':
        return `!/${validation.value}/.test(${prop})`;
      case 'custom':
        return String(validation.value);
      default:
        return 'false';
    }
  }

  /**
   * Generate test code
   */
  private generateTestCode(spec: ValueObjectSpec): string {
    const { name, properties, validations } = spec;
    const lines: string[] = [];

    lines.push(`/**`);
    lines.push(` * ${name} Value Object Tests`);
    lines.push(` */`);
    lines.push('');
    lines.push(`import { describe, it, expect } from 'vitest';`);
    lines.push(`import { create${name}, type ${name}Input } from './${this.toKebabCase(name)}.js';`);
    lines.push('');
    lines.push(`describe('${name}', () => {`);

    // Valid creation test
    lines.push(`  describe('create${name}', () => {`);
    lines.push(`    it('should create valid ${name}', () => {`);
    lines.push(`      const input: ${name}Input = {`);
    for (const prop of properties) {
      lines.push(`        ${prop.name}: ${this.getDefaultValue(prop.type)},`);
    }
    lines.push(`      };`);
    lines.push('');
    lines.push(`      const result = create${name}(input);`);
    if (this.options.useResultType) {
      lines.push(`      expect(result.isOk()).toBe(true);`);
      lines.push(`      if (result.isOk()) {`);
      for (const prop of properties) {
        lines.push(`        expect(result.value.${prop.name}).toBe(input.${prop.name});`);
      }
      lines.push(`      }`);
    } else {
      for (const prop of properties) {
        lines.push(`      expect(result.${prop.name}).toBe(input.${prop.name});`);
      }
    }
    lines.push(`    });`);

    // Validation tests
    if (validations && validations.length > 0) {
      lines.push('');
      for (const validation of validations) {
        lines.push(`    it('should reject when ${validation.property} ${this.getValidationDescription(validation)}', () => {`);
        lines.push(`      const input: ${name}Input = {`);
        for (const prop of properties) {
          if (prop.name === validation.property) {
            lines.push(`        ${prop.name}: ${this.getInvalidValue(prop.type, validation)},`);
          } else {
            lines.push(`        ${prop.name}: ${this.getDefaultValue(prop.type)},`);
          }
        }
        lines.push(`      };`);
        lines.push('');
        lines.push(`      const result = create${name}(input);`);
        if (this.options.useResultType) {
          lines.push(`      expect(result.isErr()).toBe(true);`);
          lines.push(`      if (result.isErr()) {`);
          lines.push(`        expect(result.error.message).toContain('${validation.message.slice(0, 20)}');`);
          lines.push(`      }`);
        } else {
          lines.push(`      expect(() => create${name}(input)).toThrow();`);
        }
        lines.push(`    });`);
      }
    }

    lines.push(`  });`);
    lines.push(`});`);

    return lines.join('\n');
  }

  /**
   * Get default value for a type
   */
  private getDefaultValue(type: string): string {
    if (type === 'string') return "'test'";
    if (type === 'number') return '100';
    if (type === 'boolean') return 'true';
    if (type.endsWith('[]')) return '[]';
    if (type === 'Date') return 'new Date()';
    return '{}';
  }

  /**
   * Get invalid value for validation testing
   */
  private getInvalidValue(type: string, validation: VOValidation): string {
    switch (validation.type) {
      case 'min':
        return String(Number(validation.value) - 1);
      case 'max':
        return String(Number(validation.value) + 1);
      case 'minLength':
        return "''";
      case 'maxLength':
        return "'x'.repeat(" + (Number(validation.value) + 1) + ')';
      case 'pattern':
        return "'invalid'";
      default:
        return this.getDefaultValue(type);
    }
  }

  /**
   * Get validation description for test name
   */
  private getValidationDescription(validation: VOValidation): string {
    switch (validation.type) {
      case 'min':
        return `is less than ${validation.value}`;
      case 'max':
        return `is greater than ${validation.value}`;
      case 'minLength':
        return `is shorter than ${validation.value} characters`;
      case 'maxLength':
        return `is longer than ${validation.value} characters`;
      case 'pattern':
        return `does not match pattern`;
      default:
        return 'is invalid';
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
}

/**
 * Generate Value Object from specification (convenience function)
 */
export function generateValueObject(
  spec: ValueObjectSpec,
  options?: VOGeneratorOptions
): VOGenerationResult {
  const generator = new ValueObjectGenerator(options);
  return generator.generate(spec);
}

/**
 * Parse Value Object specification from simple text format
 *
 * Format:
 * Name: Price
 * Description: Price value object
 * Properties:
 *   amount: number (min:100, max:1000000)
 *   currency: string = "JPY"
 */
export function parseVOSpec(text: string): ValueObjectSpec {
  const lines = text.split('\n').map((l) => l.trim()).filter((l) => l);
  const spec: ValueObjectSpec = {
    name: '',
    properties: [],
    validations: [],
  };

  let inProperties = false;

  for (const line of lines) {
    if (line.toLowerCase().startsWith('name:')) {
      spec.name = line.slice(5).trim();
    } else if (line.toLowerCase().startsWith('description:')) {
      spec.description = line.slice(12).trim();
    } else if (line.toLowerCase().startsWith('requirement:')) {
      spec.requirementId = line.slice(12).trim();
    } else if (line.toLowerCase().startsWith('properties:')) {
      inProperties = true;
    } else if (inProperties && line.includes(':')) {
      // Parse property line: name: type (validation)
      // Use indexOf to handle colons in validation specs like (min:100, max:1000000)
      const colonIndex = line.indexOf(':');
      const namePart = line.slice(0, colonIndex).trim();
      const rest = line.slice(colonIndex + 1).trim();
      const typeMatch = rest.match(/^(\w+(?:\[\])?)/);
      const type = typeMatch ? typeMatch[1] : 'string';

      spec.properties.push({
        name: namePart,
        type,
        readonly: true,
      });

      // Parse validations in parentheses
      const validationMatch = rest.match(/\(([^)]+)\)/);
      if (validationMatch) {
        const validations = validationMatch[1].split(',').map((v) => v.trim());
        for (const v of validations) {
          const vColonIndex = v.indexOf(':');
          if (vColonIndex === -1) continue;
          const vType = v.slice(0, vColonIndex).trim();
          const vValue = v.slice(vColonIndex + 1).trim();
          if (vType && vValue) {
            spec.validations!.push({
              property: namePart,
              type: vType as VOValidation['type'],
              value: isNaN(Number(vValue)) ? vValue : Number(vValue),
              message: `${namePart} ${vType} validation failed`,
            });
          }
        }
      }
    }
  }

  return spec;
}
