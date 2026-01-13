/**
 * Value Object Generator Tests
 *
 * @traceability TST-SCF-001
 * @see REQ-SCF-001, REQ-SCF-002
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  ValueObjectGenerator,
  createValueObjectGenerator,
  type ValueObjectSpec,
  type ValueObjectGeneratorConfig,
} from '../value-object-generator.js';

describe('ValueObjectGenerator', () => {
  let generator: ValueObjectGenerator;
  let config: ValueObjectGeneratorConfig;

  beforeEach(() => {
    config = {
      domain: 'TEST',
      outputDir: '/tmp/test-project',
      generateTests: true,
    };
    generator = createValueObjectGenerator(config);
  });

  describe('generate', () => {
    it('should generate Value Object file for Price', async () => {
      const specs: ValueObjectSpec[] = [
        { name: 'Price' },
      ];

      const files = await generator.generate(specs);

      expect(files).toHaveLength(1);
      expect(files[0].path).toContain('price.ts');
      expect(files[0].type).toBe('value-object');
      expect(files[0].content).toContain('interface Price');
      expect(files[0].content).toContain('createPrice');
      expect(files[0].content).toContain('priceEquals');
      expect(files[0].content).toContain('isPrice');
    });

    it('should generate Value Object file for Email', async () => {
      const specs: ValueObjectSpec[] = [
        { name: 'Email' },
      ];

      const files = await generator.generate(specs);

      expect(files).toHaveLength(1);
      expect(files[0].content).toContain('interface Email');
      expect(files[0].content).toContain('value: string');
    });

    it('should generate multiple Value Objects', async () => {
      const specs: ValueObjectSpec[] = [
        { name: 'Price' },
        { name: 'Email' },
        { name: 'Quantity' },
      ];

      const files = await generator.generate(specs);

      expect(files).toHaveLength(3);
      expect(files.map(f => f.path)).toEqual(
        expect.arrayContaining([
          expect.stringContaining('price.ts'),
          expect.stringContaining('email.ts'),
          expect.stringContaining('quantity.ts'),
        ])
      );
    });

    it('should generate with custom fields', async () => {
      const specs: ValueObjectSpec[] = [
        {
          name: 'CustomVO',
          fields: [
            { name: 'id', type: 'string', readonly: true },
            { name: 'count', type: 'number', readonly: true },
          ],
        },
      ];

      const files = await generator.generate(specs);

      expect(files[0].content).toContain('readonly id: string');
      expect(files[0].content).toContain('readonly count: number');
    });

    it('should generate with validation rules', async () => {
      const specs: ValueObjectSpec[] = [
        {
          name: 'Price',
          validationType: 'range',
          validationRules: [
            {
              type: 'range',
              params: { min: 100, max: 1000000, field: 'amount' },
            },
          ],
        },
      ];

      const files = await generator.generate(specs);

      expect(files[0].content).toContain('amount < 100');
      expect(files[0].content).toContain('amount > 1000000');
      expect(files[0].content).toContain('ValidationError');
    });

    it('should handle empty specs array', async () => {
      const files = await generator.generate([]);
      expect(files).toHaveLength(0);
    });
  });

  describe('generateTests', () => {
    it('should generate test files when enabled', async () => {
      const specs: ValueObjectSpec[] = [
        { name: 'Price' },
      ];

      const files = await generator.generateTests(specs);

      expect(files).toHaveLength(1);
      expect(files[0].path).toContain('price.test.ts');
      expect(files[0].type).toBe('test');
      expect(files[0].content).toContain("describe('Price'");
      expect(files[0].content).toContain('createPrice');
    });

    it('should not generate test files when disabled', async () => {
      const noTestConfig: ValueObjectGeneratorConfig = {
        ...config,
        generateTests: false,
      };
      const noTestGenerator = createValueObjectGenerator(noTestConfig);

      const specs: ValueObjectSpec[] = [
        { name: 'Price' },
      ];

      const files = await noTestGenerator.generateTests(specs);
      expect(files).toHaveLength(0);
    });
  });

  describe('default field inference', () => {
    it('should infer Price fields correctly', async () => {
      const specs: ValueObjectSpec[] = [{ name: 'Price' }];
      const files = await generator.generate(specs);

      expect(files[0].content).toContain('amount: number');
      expect(files[0].content).toContain("currency: 'JPY' | 'USD'");
    });

    it('should infer Email fields correctly', async () => {
      const specs: ValueObjectSpec[] = [{ name: 'Email' }];
      const files = await generator.generate(specs);

      expect(files[0].content).toContain('value: string');
    });

    it('should infer Quantity fields correctly', async () => {
      const specs: ValueObjectSpec[] = [{ name: 'Quantity' }];
      const files = await generator.generate(specs);

      expect(files[0].content).toContain('value: number');
    });

    it('should infer Address fields correctly', async () => {
      const specs: ValueObjectSpec[] = [{ name: 'Address' }];
      const files = await generator.generate(specs);

      expect(files[0].content).toContain('street: string');
      expect(files[0].content).toContain('city: string');
      expect(files[0].content).toContain('postalCode: string');
    });
  });

  describe('traceability', () => {
    it('should include traceability comment', async () => {
      const specs: ValueObjectSpec[] = [{ name: 'Price' }];
      const files = await generator.generate(specs);

      expect(files[0].content).toContain('@traceability REQ-SCF-001');
      expect(files[0].content).toContain('@domain TEST');
    });
  });
});
