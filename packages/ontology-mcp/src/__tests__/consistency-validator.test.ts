/**
 * @fileoverview Tests for ConsistencyValidator
 * @traceability REQ-ONTO-001-F003
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { ConsistencyValidator, type TripleStore } from '../validation/consistency-validator.js';
import type { Triple } from '../types.js';

describe('ConsistencyValidator', () => {
  let validator: ConsistencyValidator;

  beforeEach(() => {
    validator = new ConsistencyValidator();
  });

  // Helper to create a mock store
  const createStore = (triples: Triple[]): TripleStore => ({
    getTriples: () => triples,
  });

  describe('validate', () => {
    it('should return consistent for empty store', () => {
      const store = createStore([]);
      const result = validator.validate(store);
      expect(result.consistent).toBe(true);
      expect(result.violations).toHaveLength(0);
    });

    it('should return consistent for valid triples', () => {
      const store = createStore([
        { subject: 'http://example.org/Person1', predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', object: 'http://example.org/Person' },
        { subject: 'http://example.org/Person1', predicate: 'http://example.org/name', object: 'John' },
      ]);
      const result = validator.validate(store);
      expect(result.consistent).toBe(true);
    });
  });

  describe('disjoint class checking', () => {
    it('should detect disjoint class membership violation', () => {
      const store = createStore([
        // Declare disjoint classes
        { subject: 'http://example.org/Cat', predicate: 'http://www.w3.org/2002/07/owl#disjointWith', object: 'http://example.org/Dog' },
        // Instance belongs to both
        { subject: 'http://example.org/Pet1', predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', object: 'http://example.org/Cat' },
        { subject: 'http://example.org/Pet1', predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', object: 'http://example.org/Dog' },
      ]);
      const result = validator.validate(store);
      expect(result.consistent).toBe(false);
      expect(result.violations.some(v => v.type === 'disjoint-class-membership')).toBe(true);
    });

    it('should not report when classes are not both used', () => {
      const store = createStore([
        { subject: 'http://example.org/Cat', predicate: 'http://www.w3.org/2002/07/owl#disjointWith', object: 'http://example.org/Dog' },
        { subject: 'http://example.org/Pet1', predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', object: 'http://example.org/Cat' },
        // Pet1 is only a Cat, not a Dog
      ]);
      const result = validator.validate(store);
      expect(result.consistent).toBe(true);
    });
  });

  describe('functional property checking', () => {
    it('should detect functional property violation', () => {
      const store = createStore([
        // Declare functional property
        { subject: 'http://example.org/hasMother', predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', object: 'http://www.w3.org/2002/07/owl#FunctionalProperty' },
        // Multiple values for functional property
        { subject: 'http://example.org/Person1', predicate: 'http://example.org/hasMother', object: 'http://example.org/Mother1' },
        { subject: 'http://example.org/Person1', predicate: 'http://example.org/hasMother', object: 'http://example.org/Mother2' },
      ]);
      const result = validator.validate(store);
      expect(result.consistent).toBe(false);
      expect(result.violations.some(v => v.type === 'functional-property-violation')).toBe(true);
    });

    it('should allow same value multiple times for functional property', () => {
      const store = createStore([
        { subject: 'http://example.org/hasMother', predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', object: 'http://www.w3.org/2002/07/owl#FunctionalProperty' },
        { subject: 'http://example.org/Person1', predicate: 'http://example.org/hasMother', object: 'http://example.org/Mother1' },
        { subject: 'http://example.org/Person1', predicate: 'http://example.org/hasMother', object: 'http://example.org/Mother1' },
      ]);
      const result = validator.validate(store);
      // Has duplicates (warning) but no functional violation (error)
      const functionalViolations = result.violations.filter(v => v.type === 'functional-property-violation');
      expect(functionalViolations).toHaveLength(0);
    });
  });

  describe('inverse functional property checking', () => {
    it('should detect inverse functional property violation', () => {
      const store = createStore([
        // Declare inverse functional property
        { subject: 'http://example.org/ssn', predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', object: 'http://www.w3.org/2002/07/owl#InverseFunctionalProperty' },
        // Same value used by multiple subjects
        { subject: 'http://example.org/Person1', predicate: 'http://example.org/ssn', object: '123-45-6789' },
        { subject: 'http://example.org/Person2', predicate: 'http://example.org/ssn', object: '123-45-6789' },
      ]);
      const result = validator.validate(store);
      expect(result.consistent).toBe(false);
      expect(result.violations.some(v => v.type === 'inverse-functional-violation')).toBe(true);
    });
  });

  describe('asymmetric property checking', () => {
    it('should detect asymmetric property violation', () => {
      const store = createStore([
        // Declare asymmetric property
        { subject: 'http://example.org/parentOf', predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', object: 'http://www.w3.org/2002/07/owl#AsymmetricProperty' },
        // Both directions exist (violation)
        { subject: 'http://example.org/Person1', predicate: 'http://example.org/parentOf', object: 'http://example.org/Person2' },
        { subject: 'http://example.org/Person2', predicate: 'http://example.org/parentOf', object: 'http://example.org/Person1' },
      ]);
      const result = validator.validate(store);
      expect(result.consistent).toBe(false);
      expect(result.violations.some(v => v.type === 'asymmetric-violation')).toBe(true);
    });
  });

  describe('irreflexive property checking', () => {
    it('should detect irreflexive property violation', () => {
      const store = createStore([
        // Declare irreflexive property
        { subject: 'http://example.org/parentOf', predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', object: 'http://www.w3.org/2002/07/owl#IrreflexiveProperty' },
        // Self-reference (violation)
        { subject: 'http://example.org/Person1', predicate: 'http://example.org/parentOf', object: 'http://example.org/Person1' },
      ]);
      const result = validator.validate(store);
      expect(result.consistent).toBe(false);
      expect(result.violations.some(v => v.type === 'irreflexive-violation')).toBe(true);
    });
  });

  describe('duplicate detection', () => {
    it('should detect duplicate triples', () => {
      const store = createStore([
        { subject: 'http://example.org/Person1', predicate: 'http://example.org/name', object: 'John' },
        { subject: 'http://example.org/Person1', predicate: 'http://example.org/name', object: 'John' },
      ]);
      const result = validator.validate(store);
      expect(result.violations.some(v => v.type === 'duplicate-triple')).toBe(true);
      // Duplicates are warnings, not errors
      expect(result.consistent).toBe(true);
    });
  });

  describe('circular dependency detection', () => {
    it('should detect subClassOf cycles', () => {
      const store = createStore([
        { subject: 'http://example.org/A', predicate: 'http://www.w3.org/2000/01/rdf-schema#subClassOf', object: 'http://example.org/B' },
        { subject: 'http://example.org/B', predicate: 'http://www.w3.org/2000/01/rdf-schema#subClassOf', object: 'http://example.org/C' },
        { subject: 'http://example.org/C', predicate: 'http://www.w3.org/2000/01/rdf-schema#subClassOf', object: 'http://example.org/A' },
      ]);
      const result = validator.validate(store);
      expect(result.consistent).toBe(false);
      expect(result.violations.some(v => v.type === 'circular-dependency')).toBe(true);
    });
  });

  describe('validateTriple', () => {
    it('should validate a valid triple', () => {
      const existingTriples: Triple[] = [];
      const triple: Triple = {
        subject: 'http://example.org/Person1',
        predicate: 'http://example.org/name',
        object: 'John',
      };
      const result = validator.validateTriple(triple, existingTriples);
      expect(result.valid).toBe(true);
      expect(result.errors).toHaveLength(0);
    });

    it('should detect duplicate triple', () => {
      const existingTriples: Triple[] = [
        { subject: 'http://example.org/Person1', predicate: 'http://example.org/name', object: 'John' },
      ];
      const triple: Triple = {
        subject: 'http://example.org/Person1',
        predicate: 'http://example.org/name',
        object: 'John',
      };
      const result = validator.validateTriple(triple, existingTriples);
      expect(result.valid).toBe(true);
      expect(result.duplicateOf).toBeDefined();
      expect(result.warnings.length).toBeGreaterThan(0);
    });

    it('should detect functional property violation before add', () => {
      const existingTriples: Triple[] = [
        { subject: 'http://example.org/hasMother', predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', object: 'http://www.w3.org/2002/07/owl#FunctionalProperty' },
        { subject: 'http://example.org/Person1', predicate: 'http://example.org/hasMother', object: 'http://example.org/Mother1' },
      ];
      const triple: Triple = {
        subject: 'http://example.org/Person1',
        predicate: 'http://example.org/hasMother',
        object: 'http://example.org/Mother2',
      };
      const result = validator.validateTriple(triple, existingTriples);
      expect(result.valid).toBe(false);
      expect(result.errors.some(e => e.includes('Functional property'))).toBe(true);
    });
  });

  describe('findDuplicates', () => {
    it('should find exact duplicate triples', () => {
      const triples: Triple[] = [
        { subject: 'http://example.org/a', predicate: 'http://example.org/p', object: 'value1' },
        { subject: 'http://example.org/a', predicate: 'http://example.org/p', object: 'value1' },
        { subject: 'http://example.org/b', predicate: 'http://example.org/p', object: 'value2' },
      ];
      const duplicates = validator.findDuplicates(triples);
      expect(duplicates).toHaveLength(1);
      expect(duplicates[0]).toHaveLength(2);
    });
  });

  describe('findSemanticDuplicates', () => {
    it('should find semantically equivalent triples', () => {
      const triples: Triple[] = [
        { subject: 'http://example.org/a', predicate: 'http://example.org/p', object: 'value' },
        { subject: 'https://example.org/a', predicate: 'http://example.org/p', object: 'value' },
      ];
      const duplicates = validator.findSemanticDuplicates(triples);
      expect(duplicates).toHaveLength(1);
    });

    it('should find URIs with trailing slash differences', () => {
      const triples: Triple[] = [
        { subject: 'http://example.org/a/', predicate: 'http://example.org/p', object: 'value' },
        { subject: 'http://example.org/a', predicate: 'http://example.org/p', object: 'value' },
      ];
      const duplicates = validator.findSemanticDuplicates(triples);
      expect(duplicates).toHaveLength(1);
    });
  });

  describe('suggestions', () => {
    it('should provide suggestions for violations', () => {
      const store = createStore([
        { subject: 'http://example.org/parentOf', predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', object: 'http://www.w3.org/2002/07/owl#IrreflexiveProperty' },
        { subject: 'http://example.org/Person1', predicate: 'http://example.org/parentOf', object: 'http://example.org/Person1' },
      ]);
      const result = validator.validate(store);
      expect(result.suggestions).toBeDefined();
      expect(result.suggestions!.length).toBeGreaterThan(0);
      expect(result.suggestions![0].suggestion).toBeDefined();
    });
  });

  describe('configuration', () => {
    it('should skip checks when disabled', () => {
      const validator = new ConsistencyValidator({
        checkDisjointClasses: false,
        checkDuplicates: false,
      });
      const store = createStore([
        { subject: 'http://example.org/Cat', predicate: 'http://www.w3.org/2002/07/owl#disjointWith', object: 'http://example.org/Dog' },
        { subject: 'http://example.org/Pet1', predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', object: 'http://example.org/Cat' },
        { subject: 'http://example.org/Pet1', predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', object: 'http://example.org/Dog' },
      ]);
      const result = validator.validate(store);
      expect(result.violations.filter(v => v.type === 'disjoint-class-membership')).toHaveLength(0);
    });
  });
});
