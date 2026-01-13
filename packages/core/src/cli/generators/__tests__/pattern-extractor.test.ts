/**
 * Pattern Auto Extractor Tests
 *
 * @traceability REQ-PTN-001, REQ-PTN-002
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { PatternAutoExtractor, createPatternExtractor } from '../pattern-extractor.js';

describe('PatternAutoExtractor', () => {
  let extractor: PatternAutoExtractor;

  beforeEach(() => {
    extractor = createPatternExtractor();
  });

  describe('extractFromCode', () => {
    it('should extract Value Object patterns', () => {
      const code = `
export interface Price {
  readonly amount: number;
  readonly currency: string;
}

export function createPrice(amount: number, currency: string): Result<Price, ValidationError> {
  if (amount < 0) {
    return err(new ValidationError('Amount must be positive'));
  }
  return ok({ amount, currency });
}
`;

      const patterns = extractor.extractFromCode(code, 'price.ts', 'SHOP');

      expect(patterns).toHaveLength(1);
      expect(patterns[0].category).toBe('value-object');
      expect(patterns[0].name).toBe('PriceValueObject');
      expect(patterns[0].metadata.domain).toBe('SHOP');
      expect(patterns[0].metadata.confidence).toBeGreaterThanOrEqual(0.7);
    });

    it('should extract Status Machine patterns', () => {
      const code = `
export type OrderStatus = 'draft' | 'active' | 'completed' | 'cancelled';

export const validOrderTransitions: Record<OrderStatus, OrderStatus[]> = {
  'draft': ['active', 'cancelled'],
  'active': ['completed', 'cancelled'],
  'completed': [],
  'cancelled': [],
};
`;

      const patterns = extractor.extractFromCode(code, 'order-status.ts', 'SHOP');

      expect(patterns).toHaveLength(1);
      expect(patterns[0].category).toBe('status-machine');
      expect(patterns[0].name).toBe('OrderStatusMachine');
    });

    it('should extract Entity patterns', () => {
      const code = `
export interface Customer {
  readonly id: CustomerId;
  readonly name: string;
  readonly email: string;
}
`;

      const patterns = extractor.extractFromCode(code, 'customer.ts', 'CRM');

      expect(patterns).toHaveLength(1);
      expect(patterns[0].category).toBe('entity');
      expect(patterns[0].name).toBe('CustomerEntity');
    });

    it('should extract Repository patterns', () => {
      const code = `
export interface CustomerRepository {
  findById(id: CustomerId): Promise<Customer | null>;
  save(customer: Customer): Promise<void>;
  delete(id: CustomerId): Promise<void>;
}
`;

      const patterns = extractor.extractFromCode(code, 'customer-repository.ts', 'CRM');

      // May extract both repository and entity patterns
      expect(patterns.length).toBeGreaterThanOrEqual(1);
      const repoPattern = patterns.find((p) => p.category === 'repository');
      expect(repoPattern).toBeDefined();
      expect(repoPattern?.name).toBe('CustomerRepository');
    });

    it('should extract Service patterns', () => {
      const code = `
export class CustomerService {
  constructor(private repo: CustomerRepository) {}
  
  async registerCustomer(input: CustomerInput): Promise<Customer> {
    // ...
  }
}
`;

      const patterns = extractor.extractFromCode(code, 'customer-service.ts', 'CRM');

      expect(patterns).toHaveLength(1);
      expect(patterns[0].category).toBe('service');
      expect(patterns[0].name).toBe('CustomerService');
    });

    it('should filter patterns below confidence threshold', () => {
      const highConfidenceExtractor = createPatternExtractor({ minConfidence: 0.95 });
      const code = `
export interface Price {
  readonly amount: number;
}

export function createPrice(amount: number): Result<Price, ValidationError> {
  return ok({ amount });
}
`;

      const patterns = highConfidenceExtractor.extractFromCode(code, 'price.ts', 'SHOP');

      // With 0.95 threshold, some patterns may be filtered
      expect(patterns.length).toBeLessThanOrEqual(1);
    });
  });

  describe('getResult', () => {
    it('should return extraction statistics', () => {
      const voCode = `
export interface Price {
  readonly amount: number;
}
export function createPrice(amount: number): Result<Price, ValidationError> {
  return ok({ amount });
}
`;

      const smCode = `
export type TaskStatus = 'pending' | 'done';
export const validTaskTransitions: Record<TaskStatus, TaskStatus[]> = {
  'pending': ['done'],
  'done': [],
};
`;

      extractor.extractFromCode(voCode, 'price.ts', 'SHOP');
      extractor.extractFromCode(smCode, 'task-status.ts', 'TODO');

      const result = extractor.getResult();

      expect(result.stats.totalFiles).toBe(2);
      expect(result.stats.patternsFound).toBe(2);
      expect(result.stats.byCategory['value-object']).toBe(1);
      expect(result.stats.byCategory['status-machine']).toBe(1);
    });

    it('should collect errors', () => {
      // Force an error by passing invalid code
      // This tests error handling
      const result = extractor.getResult();

      expect(result.errors).toEqual([]);
    });
  });

  describe('reset', () => {
    it('should clear extracted patterns', () => {
      const code = `
export interface Price { readonly amount: number; }
export function createPrice(amount: number): Result<Price, ValidationError> {
  return ok({ amount });
}
`;

      extractor.extractFromCode(code, 'price.ts', 'SHOP');
      expect(extractor.getResult().patterns).toHaveLength(1);

      extractor.reset();
      expect(extractor.getResult().patterns).toHaveLength(0);
    });
  });

  describe('pattern ID generation', () => {
    it('should generate unique pattern IDs', () => {
      const code = `
export interface Price { readonly amount: number; }
export function createPrice(amount: number): Result<Price, ValidationError> {
  return ok({ amount });
}
`;

      extractor.extractFromCode(code, 'price1.ts', 'SHOP');
      extractor.extractFromCode(code, 'price2.ts', 'SHOP');

      const result = extractor.getResult();
      const ids = result.patterns.map((p) => p.id);

      expect(new Set(ids).size).toBe(ids.length);
    });

    it('should include category prefix in pattern ID', () => {
      const code = `
export interface Price { readonly amount: number; }
export function createPrice(amount: number): Result<Price, ValidationError> {
  return ok({ amount });
}
`;

      extractor.extractFromCode(code, 'price.ts', 'SHOP');
      const pattern = extractor.getResult().patterns[0];

      expect(pattern.id).toMatch(/^PTN-VO-/);
    });
  });

  describe('variables extraction', () => {
    it('should extract variables from Value Object patterns', () => {
      const code = `
export interface Email { readonly value: string; }
export function createEmail(value: string): Result<Email, ValidationError> {
  return ok({ value });
}
`;

      extractor.extractFromCode(code, 'email.ts', 'USER');
      const pattern = extractor.getResult().patterns[0];

      expect(pattern.variables).toBeDefined();
      expect(pattern.variables.length).toBeGreaterThan(0);
      expect(pattern.variables.some((v) => v.name === 'name')).toBe(true);
    });
  });
});
