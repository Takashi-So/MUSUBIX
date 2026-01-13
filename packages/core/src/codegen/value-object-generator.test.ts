/**
 * Value Object Generator Tests
 *
 * @see TSK-GEN-001
 */

import { describe, it, expect } from 'vitest';
import {
  ValueObjectGenerator,
  generateValueObject,
  parseVOSpec,
  type ValueObjectSpec,
} from './value-object-generator.js';

describe('ValueObjectGenerator', () => {
  describe('generate', () => {
    it('should generate basic Value Object code', () => {
      const spec: ValueObjectSpec = {
        name: 'Price',
        description: 'Price value object for products',
        properties: [
          { name: 'amount', type: 'number', description: 'Price amount' },
          { name: 'currency', type: 'string', description: 'Currency code' },
        ],
      };

      const generator = new ValueObjectGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain('export interface Price');
      expect(result.code).toContain('readonly amount: number');
      expect(result.code).toContain('readonly currency: string');
      expect(result.code).toContain('export function createPrice');
      expect(result.fileName).toBe('price.ts');
    });

    it('should generate validation logic', () => {
      const spec: ValueObjectSpec = {
        name: 'Price',
        properties: [{ name: 'amount', type: 'number' }],
        validations: [
          { property: 'amount', type: 'min', value: 100, message: 'Price must be at least 100' },
          { property: 'amount', type: 'max', value: 1000000, message: 'Price must be at most 1000000' },
        ],
      };

      const generator = new ValueObjectGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain('input.amount < 100');
      expect(result.code).toContain('input.amount > 1000000');
      expect(result.code).toContain('Price must be at least 100');
    });

    it('should use Result type by default', () => {
      const spec: ValueObjectSpec = {
        name: 'Email',
        properties: [{ name: 'value', type: 'string' }],
      };

      const generator = new ValueObjectGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain("import { Result, ok, err }");
      expect(result.code).toContain('Result<Email, EmailValidationError>');
      expect(result.code).toContain('return ok({');
    });

    it('should support throwing errors when Result type disabled', () => {
      const spec: ValueObjectSpec = {
        name: 'Email',
        properties: [{ name: 'value', type: 'string' }],
        validations: [
          { property: 'value', type: 'pattern', value: '@', message: 'Invalid email' },
        ],
      };

      const generator = new ValueObjectGenerator({ useResultType: false });
      const result = generator.generate(spec);

      expect(result.code).not.toContain('import { Result');
      expect(result.code).toContain('throw new EmailValidationError');
    });

    it('should generate test code', () => {
      const spec: ValueObjectSpec = {
        name: 'Price',
        properties: [{ name: 'amount', type: 'number' }],
        validations: [
          { property: 'amount', type: 'min', value: 100, message: 'Price too low' },
        ],
      };

      const generator = new ValueObjectGenerator();
      const result = generator.generate(spec);

      expect(result.testCode).toBeDefined();
      expect(result.testCode).toContain("describe('Price'");
      expect(result.testCode).toContain('should create valid Price');
      expect(result.testCode).toContain('should reject when amount is less than 100');
      expect(result.testFileName).toBe('price.test.ts');
    });

    it('should skip test generation when disabled', () => {
      const spec: ValueObjectSpec = {
        name: 'Price',
        properties: [{ name: 'amount', type: 'number' }],
      };

      const generator = new ValueObjectGenerator({ generateTest: false });
      const result = generator.generate(spec);

      expect(result.testCode).toBeUndefined();
    });

    it('should include JSDoc comments by default', () => {
      const spec: ValueObjectSpec = {
        name: 'Price',
        description: 'Product price',
        properties: [{ name: 'amount', type: 'number', description: 'Amount in cents' }],
        requirementId: 'REQ-001',
      };

      const generator = new ValueObjectGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain('* Price Value Object');
      expect(result.code).toContain('* Product price');
      expect(result.code).toContain('* @see REQ-001');
      expect(result.code).toContain('/** Amount in cents */');
    });

    it('should skip JSDoc when disabled', () => {
      const spec: ValueObjectSpec = {
        name: 'Price',
        properties: [{ name: 'amount', type: 'number' }],
      };

      const generator = new ValueObjectGenerator({ includeJSDoc: false });
      const result = generator.generate(spec);

      expect(result.code).not.toContain('/**');
    });

    it('should handle multiple properties', () => {
      const spec: ValueObjectSpec = {
        name: 'Address',
        properties: [
          { name: 'street', type: 'string' },
          { name: 'city', type: 'string' },
          { name: 'postalCode', type: 'string' },
          { name: 'country', type: 'string' },
        ],
      };

      const generator = new ValueObjectGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain('readonly street: string');
      expect(result.code).toContain('readonly city: string');
      expect(result.code).toContain('readonly postalCode: string');
      expect(result.code).toContain('readonly country: string');
    });

    it('should handle string length validations', () => {
      const spec: ValueObjectSpec = {
        name: 'Username',
        properties: [{ name: 'value', type: 'string' }],
        validations: [
          { property: 'value', type: 'minLength', value: 3, message: 'Too short' },
          { property: 'value', type: 'maxLength', value: 20, message: 'Too long' },
        ],
      };

      const generator = new ValueObjectGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain('input.value.length < 3');
      expect(result.code).toContain('input.value.length > 20');
    });

    it('should handle pattern validation', () => {
      const spec: ValueObjectSpec = {
        name: 'Email',
        properties: [{ name: 'value', type: 'string' }],
        validations: [
          { property: 'value', type: 'pattern', value: '^.+@.+\\..+$', message: 'Invalid email' },
        ],
      };

      const generator = new ValueObjectGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain('!/^.+@.+\\..+$/.test(input.value)');
    });

    it('should convert PascalCase to kebab-case for file names', () => {
      const spec: ValueObjectSpec = {
        name: 'CustomerAddress',
        properties: [{ name: 'street', type: 'string' }],
      };

      const generator = new ValueObjectGenerator();
      const result = generator.generate(spec);

      expect(result.fileName).toBe('customer-address.ts');
    });
  });

  describe('generateValueObject', () => {
    it('should work as a convenience function', () => {
      const spec: ValueObjectSpec = {
        name: 'Money',
        properties: [
          { name: 'amount', type: 'number' },
          { name: 'currency', type: 'string' },
        ],
      };

      const result = generateValueObject(spec);

      expect(result.code).toContain('export interface Money');
      expect(result.code).toContain('export function createMoney');
    });
  });

  describe('parseVOSpec', () => {
    it('should parse simple spec text', () => {
      const text = `
Name: Price
Description: Product price value object
Properties:
  amount: number
  currency: string
      `;

      const spec = parseVOSpec(text);

      expect(spec.name).toBe('Price');
      expect(spec.description).toBe('Product price value object');
      expect(spec.properties).toHaveLength(2);
      expect(spec.properties[0].name).toBe('amount');
      expect(spec.properties[0].type).toBe('number');
    });

    it('should parse validations in parentheses', () => {
      const text = `
Name: Price
Properties:
  amount: number (min:100, max:1000000)
      `;

      const spec = parseVOSpec(text);

      expect(spec.validations).toHaveLength(2);
      expect(spec.validations![0].type).toBe('min');
      expect(spec.validations![0].value).toBe(100);
      expect(spec.validations![1].type).toBe('max');
      expect(spec.validations![1].value).toBe(1000000);
    });

    it('should parse requirement ID', () => {
      const text = `
Name: Email
Requirement: REQ-USER-001
Properties:
  value: string
      `;

      const spec = parseVOSpec(text);

      expect(spec.requirementId).toBe('REQ-USER-001');
    });

    it('should handle array types', () => {
      const text = `
Name: Tags
Properties:
  values: string[]
      `;

      const spec = parseVOSpec(text);

      expect(spec.properties[0].type).toBe('string[]');
    });
  });

  describe('validation error class', () => {
    it('should generate custom error class', () => {
      const spec: ValueObjectSpec = {
        name: 'Amount',
        properties: [{ name: 'value', type: 'number' }],
      };

      const generator = new ValueObjectGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain('export class AmountValidationError extends Error');
      expect(result.code).toContain("this.name = 'AmountValidationError'");
    });
  });

  describe('Input type', () => {
    it('should generate Input type for factory function', () => {
      const spec: ValueObjectSpec = {
        name: 'Point',
        properties: [
          { name: 'x', type: 'number' },
          { name: 'y', type: 'number' },
        ],
      };

      const generator = new ValueObjectGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain('export interface PointInput');
      expect(result.code).toContain('input: PointInput');
    });
  });
});
