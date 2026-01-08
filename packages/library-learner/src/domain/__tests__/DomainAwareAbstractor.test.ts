/**
 * DomainAwareAbstractor Tests
 * @module @nahisaho/musubix-library-learner
 * @see TSK-LL-106
 * @see DES-LL-106
 * @see REQ-LL-106 Domain-aware pattern abstraction
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createDomainAwareAbstractor,
  type DomainAwareAbstractor,
  type DomainOntology,
} from '../DomainAwareAbstractor.js';
import type { LearnedPattern, ConcretePattern } from '../../types.js';

describe('DomainAwareAbstractor', () => {
  let abstractor: DomainAwareAbstractor;

  // Helper to create mock patterns
  const createPattern = (id: string, name: string): LearnedPattern => ({
    id,
    name,
    level: 1,
    content: {
      id,
      ast: { type: 'Expression', value: name },
      occurrenceCount: 5,
      locations: [],
    } as ConcretePattern,
    usageCount: 10,
    confidence: 0.8,
    createdAt: new Date(),
    lastUsedAt: new Date(),
    tags: [],
  });

  // Mock domain ontology
  const mockOntology: DomainOntology = {
    name: 'E-Commerce Domain',
    version: '1.0.0',
    concepts: [
      {
        id: 'ORDER',
        name: 'Order',
        description: 'Customer order',
        properties: ['orderId', 'customerId', 'items', 'total'],
        relations: [
          { type: 'hasMany', target: 'ORDER_ITEM' },
          { type: 'belongsTo', target: 'CUSTOMER' },
        ],
      },
      {
        id: 'ORDER_ITEM',
        name: 'OrderItem',
        description: 'Item in an order',
        properties: ['productId', 'quantity', 'price'],
        relations: [{ type: 'belongsTo', target: 'ORDER' }],
      },
      {
        id: 'CUSTOMER',
        name: 'Customer',
        description: 'Customer entity',
        properties: ['customerId', 'name', 'email'],
        relations: [{ type: 'hasMany', target: 'ORDER' }],
      },
    ],
    constraints: [
      { type: 'required', concept: 'ORDER', property: 'orderId' },
      { type: 'positive', concept: 'ORDER_ITEM', property: 'quantity' },
    ],
  };

  beforeEach(() => {
    abstractor = createDomainAwareAbstractor();
  });

  describe('Factory Function', () => {
    it('should create a DomainAwareAbstractor instance', () => {
      const instance = createDomainAwareAbstractor();
      expect(instance).toBeDefined();
      expect(typeof instance.loadOntology).toBe('function');
    });

    it('should create with custom config', () => {
      const instance = createDomainAwareAbstractor({
        strictMode: true,
        maxAbstractionDepth: 5,
      });
      expect(instance).toBeDefined();
    });
  });

  describe('loadOntology', () => {
    it('should load domain ontology', () => {
      expect(() => abstractor.loadOntology(mockOntology)).not.toThrow();
    });

    it('should validate ontology structure', () => {
      const invalidOntology = {
        name: 'Invalid',
        concepts: [], // Empty concepts
      } as unknown as DomainOntology;

      // Should not throw, but return validation result
      const result = abstractor.loadOntology(invalidOntology);
      expect(result.success).toBe(true); // Empty is valid
    });

    it('should replace existing ontology', () => {
      abstractor.loadOntology(mockOntology);
      const newOntology: DomainOntology = {
        name: 'New Domain',
        version: '2.0.0',
        concepts: [],
        constraints: [],
      };

      abstractor.loadOntology(newOntology);
      const loaded = abstractor.getLoadedOntology();

      expect(loaded?.name).toBe('New Domain');
    });
  });

  describe('abstractWithDomain', () => {
    beforeEach(() => {
      abstractor.loadOntology(mockOntology);
    });

    it('should abstract pattern with domain context', async () => {
      const pattern = createPattern('PAT-001', 'CreateOrder');

      const abstracted = await abstractor.abstractWithDomain(pattern);

      expect(abstracted).toBeDefined();
      expect(abstracted.domainConcepts).toBeDefined();
    });

    it('should identify related domain concepts', async () => {
      const pattern = createPattern('PAT-001', 'UpdateOrderItem');

      const abstracted = await abstractor.abstractWithDomain(pattern);

      // Should identify ORDER_ITEM concept
      expect(abstracted.domainConcepts).toContain('ORDER_ITEM');
    });

    it('should apply domain constraints', async () => {
      const pattern = createPattern('PAT-001', 'ValidateOrderTotal');

      const abstracted = await abstractor.abstractWithDomain(pattern);

      expect(abstracted.constraints).toBeDefined();
    });

    it('should handle patterns without domain match', async () => {
      const pattern = createPattern('PAT-001', 'CalculateTax');

      const abstracted = await abstractor.abstractWithDomain(pattern);

      // Should still return result, but with empty domain concepts
      expect(abstracted).toBeDefined();
      expect(abstracted.domainConcepts.length).toBe(0);
    });
  });

  describe('findRelatedConcepts', () => {
    beforeEach(() => {
      abstractor.loadOntology(mockOntology);
    });

    it('should find concepts by name', () => {
      const concepts = abstractor.findRelatedConcepts('Order');

      expect(concepts.length).toBeGreaterThan(0);
      expect(concepts.some((c) => c.id === 'ORDER')).toBe(true);
    });

    it('should find concepts by property', () => {
      const concepts = abstractor.findRelatedConcepts('customerId');

      expect(concepts.length).toBeGreaterThan(0);
    });

    it('should return empty for unknown terms', () => {
      const concepts = abstractor.findRelatedConcepts('XyzUnknown');

      expect(concepts).toEqual([]);
    });
  });

  describe('getConceptHierarchy', () => {
    beforeEach(() => {
      abstractor.loadOntology(mockOntology);
    });

    it('should return concept hierarchy', () => {
      const hierarchy = abstractor.getConceptHierarchy('ORDER');

      expect(hierarchy).toBeDefined();
      expect(hierarchy.concept.id).toBe('ORDER');
    });

    it('should include related concepts', () => {
      const hierarchy = abstractor.getConceptHierarchy('ORDER');

      expect(hierarchy.related.length).toBeGreaterThan(0);
    });
  });

  describe('Batch Operations', () => {
    beforeEach(() => {
      abstractor.loadOntology(mockOntology);
    });

    it('should abstract multiple patterns', async () => {
      const patterns = [
        createPattern('PAT-001', 'CreateOrder'),
        createPattern('PAT-002', 'UpdateCustomer'),
        createPattern('PAT-003', 'DeleteOrderItem'),
      ];

      const results = await abstractor.abstractBatch(patterns);

      expect(results).toHaveLength(3);
    });
  });

  describe('Statistics', () => {
    it('should track abstraction statistics', async () => {
      abstractor.loadOntology(mockOntology);
      const pattern = createPattern('PAT-001', 'CreateOrder');

      await abstractor.abstractWithDomain(pattern);
      const stats = abstractor.getStatistics();

      expect(stats.totalAbstractions).toBeGreaterThanOrEqual(1);
      expect(stats.ontologiesLoaded).toBe(1);
    });

    it('should reset statistics', () => {
      abstractor.loadOntology(mockOntology);
      abstractor.resetStatistics();

      const stats = abstractor.getStatistics();
      expect(stats.totalAbstractions).toBe(0);
    });
  });

  describe('Serialization', () => {
    it('should serialize to JSON', () => {
      abstractor.loadOntology(mockOntology);

      const json = abstractor.toJSON();
      expect(typeof json).toBe('string');

      const parsed = JSON.parse(json);
      expect(parsed.ontology).toBeDefined();
    });

    it('should deserialize from JSON', () => {
      const json = JSON.stringify({
        ontology: mockOntology,
        config: { strictMode: true },
      });

      expect(() => abstractor.fromJSON(json)).not.toThrow();

      const loaded = abstractor.getLoadedOntology();
      expect(loaded?.name).toBe('E-Commerce Domain');
    });
  });
});
