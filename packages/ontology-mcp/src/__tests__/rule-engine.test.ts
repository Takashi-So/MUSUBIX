/**
 * @fileoverview Tests for Rule Engine
 * @traceability TSK-ONTO-002
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { RuleEngine, type InferenceRuleDefinition } from '../inference/index.js';
import type { Triple } from '../types.js';

describe('RuleEngine', () => {
  let engine: RuleEngine;

  beforeEach(() => {
    engine = new RuleEngine();
  });

  describe('built-in rules', () => {
    it('should have RDFS and OWL rules loaded', () => {
      const rules = engine.getRules();
      expect(rules.length).toBeGreaterThan(0);
      
      const ruleIds = rules.map(r => r.id);
      expect(ruleIds).toContain('rdfs9');  // subClassOf transitivity
      expect(ruleIds).toContain('rdfs11'); // type inheritance
    });
  });

  describe('transitive closure', () => {
    it('should compute transitive closure for subClassOf', () => {
      const triples: Triple[] = [
        {
          subject: 'https://example.org/Cat',
          predicate: 'http://www.w3.org/2000/01/rdf-schema#subClassOf',
          object: 'https://example.org/Mammal',
        },
        {
          subject: 'https://example.org/Mammal',
          predicate: 'http://www.w3.org/2000/01/rdf-schema#subClassOf',
          object: 'https://example.org/Animal',
        },
      ];

      const { triples: result, stats } = engine.applyRules(triples);

      // Should infer Cat subClassOf Animal
      const inferred = result.find(t =>
        t.subject === 'https://example.org/Cat' &&
        t.object === 'https://example.org/Animal'
      );

      expect(inferred).toBeDefined();
      expect(stats.triplesInferred).toBeGreaterThan(0);
    });

    it('should handle longer transitive chains', () => {
      const triples: Triple[] = [
        {
          subject: 'https://example.org/A',
          predicate: 'http://www.w3.org/2000/01/rdf-schema#subClassOf',
          object: 'https://example.org/B',
        },
        {
          subject: 'https://example.org/B',
          predicate: 'http://www.w3.org/2000/01/rdf-schema#subClassOf',
          object: 'https://example.org/C',
        },
        {
          subject: 'https://example.org/C',
          predicate: 'http://www.w3.org/2000/01/rdf-schema#subClassOf',
          object: 'https://example.org/D',
        },
      ];

      const { triples: result } = engine.applyRules(triples);

      // Should infer A -> D
      const aToD = result.find(t =>
        t.subject === 'https://example.org/A' &&
        t.object === 'https://example.org/D'
      );
      expect(aToD).toBeDefined();
    });
  });

  describe('type inheritance', () => {
    it('should infer type through subClassOf', () => {
      const triples: Triple[] = [
        {
          subject: 'https://example.org/fluffy',
          predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
          object: 'https://example.org/Cat',
        },
        {
          subject: 'https://example.org/Cat',
          predicate: 'http://www.w3.org/2000/01/rdf-schema#subClassOf',
          object: 'https://example.org/Animal',
        },
      ];

      const { triples: result } = engine.applyRules(triples);

      // fluffy should also be of type Animal
      const inferredType = result.find(t =>
        t.subject === 'https://example.org/fluffy' &&
        t.predicate === 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type' &&
        t.object === 'https://example.org/Animal'
      );

      expect(inferredType).toBeDefined();
    });
  });

  describe('symmetric properties', () => {
    it('should infer symmetric relationships', () => {
      const triples: Triple[] = [
        {
          subject: 'https://example.org/friendOf',
          predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
          object: 'http://www.w3.org/2002/07/owl#SymmetricProperty',
        },
        {
          subject: 'https://example.org/alice',
          predicate: 'https://example.org/friendOf',
          object: 'https://example.org/bob',
        },
      ];

      const { triples: result } = engine.applyRules(triples);

      // Should infer bob friendOf alice
      const inverse = result.find(t =>
        t.subject === 'https://example.org/bob' &&
        t.predicate === 'https://example.org/friendOf' &&
        t.object === 'https://example.org/alice'
      );

      expect(inverse).toBeDefined();
    });
  });

  describe('owl:sameAs', () => {
    it('should compute sameAs transitivity', () => {
      const sameAs = 'http://www.w3.org/2002/07/owl#sameAs';
      const triples: Triple[] = [
        { subject: 'https://example.org/a', predicate: sameAs, object: 'https://example.org/b' },
        { subject: 'https://example.org/b', predicate: sameAs, object: 'https://example.org/c' },
      ];

      const { triples: result } = engine.applyRules(triples);

      // Should infer a sameAs c
      const inferred = result.find(t =>
        t.subject === 'https://example.org/a' &&
        t.predicate === sameAs &&
        t.object === 'https://example.org/c'
      );

      expect(inferred).toBeDefined();
    });

    it('should compute sameAs symmetry', () => {
      const sameAs = 'http://www.w3.org/2002/07/owl#sameAs';
      const triples: Triple[] = [
        { subject: 'https://example.org/x', predicate: sameAs, object: 'https://example.org/y' },
      ];

      const { triples: result } = engine.applyRules(triples);

      // Should infer y sameAs x
      const inverse = result.find(t =>
        t.subject === 'https://example.org/y' &&
        t.predicate === sameAs &&
        t.object === 'https://example.org/x'
      );

      expect(inverse).toBeDefined();
    });
  });

  describe('custom rules', () => {
    it('should allow adding custom rules', () => {
      const customRule: InferenceRuleDefinition = {
        id: 'custom-1',
        name: 'Custom Rule',
        priority: 50,
        conditions: [
          {
            type: 'triple-pattern',
            subject: { variable: 'x' },
            predicate: 'https://example.org/likes',
            object: { variable: 'y' },
          },
        ],
        actions: [
          {
            type: 'add-triple',
            subject: { variable: 'y' },
            predicate: 'https://example.org/likedBy',
            object: { variable: 'x' },
          },
        ],
      };

      engine.addRule(customRule);

      const triples: Triple[] = [
        {
          subject: 'https://example.org/alice',
          predicate: 'https://example.org/likes',
          object: 'https://example.org/pizza',
        },
      ];

      const { triples: result } = engine.applyRules(triples);

      // Should infer pizza likedBy alice
      const inferred = result.find(t =>
        t.subject === 'https://example.org/pizza' &&
        t.predicate === 'https://example.org/likedBy' &&
        t.object === 'https://example.org/alice'
      );

      expect(inferred).toBeDefined();
    });

    it('should remove rules', () => {
      const initialCount = engine.getRules().length;
      engine.removeRule('rdfs9');
      expect(engine.getRules().length).toBe(initialCount - 1);
    });
  });

  describe('statistics', () => {
    it('should track inference statistics', () => {
      const triples: Triple[] = [
        {
          subject: 'https://example.org/A',
          predicate: 'http://www.w3.org/2000/01/rdf-schema#subClassOf',
          object: 'https://example.org/B',
        },
        {
          subject: 'https://example.org/B',
          predicate: 'http://www.w3.org/2000/01/rdf-schema#subClassOf',
          object: 'https://example.org/C',
        },
      ];

      const { stats } = engine.applyRules(triples);

      expect(stats.rulesApplied).toBeGreaterThan(0);
      expect(stats.triplesInferred).toBeGreaterThan(0);
      expect(stats.iterationsUsed).toBeGreaterThanOrEqual(1);
      expect(stats.timeMs).toBeGreaterThanOrEqual(0);
    });
  });

  describe('fixpoint', () => {
    it('should reach fixpoint when no new triples can be inferred', () => {
      const triples: Triple[] = [
        {
          subject: 'https://example.org/X',
          predicate: 'https://example.org/unrelatedPredicate',
          object: 'https://example.org/Y',
        },
      ];

      const { triples: result, stats } = engine.applyRules(triples);

      // No inference rules apply, should return original
      expect(result.length).toBe(1);
      expect(stats.triplesInferred).toBe(0);
    });
  });
});
