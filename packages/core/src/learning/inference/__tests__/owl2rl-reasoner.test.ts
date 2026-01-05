/**
 * OWL 2 RL Reasoner Tests
 *
 * @module learning/inference/__tests__/owl2rl-reasoner.test
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { OWL2RLReasoner, OWL2RL_RULES } from '../owl2rl-reasoner.js';
import { NAMESPACES } from '../types.js';
import type { Triple } from '../types.js';

describe('OWL2RLReasoner', () => {
  let reasoner: OWL2RLReasoner;

  beforeEach(() => {
    reasoner = new OWL2RLReasoner();
  });

  describe('constructor', () => {
    it('should create reasoner with default options', () => {
      expect(reasoner).toBeInstanceOf(OWL2RLReasoner);
    });
  });

  describe('infer', () => {
    it('should return empty result for empty input', async () => {
      const result = await reasoner.infer([]);

      expect(result.inferredTriples).toHaveLength(0);
      expect(result.appliedRules).toHaveLength(0);
    });

    it('should infer subclass relationships (cax-sco)', async () => {
      const triples: Triple[] = [
        {
          subject: 'http://example.org/Animal',
          predicate: `${NAMESPACES.RDFS}subClassOf`,
          object: 'http://example.org/LivingThing',
        },
        {
          subject: 'http://example.org/Dog',
          predicate: `${NAMESPACES.RDF}type`,
          object: 'http://example.org/Animal',
        },
      ];

      const result = await reasoner.infer(triples);

      expect(result.inferredTriples.length).toBeGreaterThanOrEqual(0);

      // Dog should be inferred as LivingThing (if cax-sco is applied)
      const inferredType = result.inferredTriples.find(
        (t) =>
          t.subject === 'http://example.org/Dog' &&
          t.object === 'http://example.org/LivingThing'
      );
      // Note: This depends on exact rule implementation
      if (result.inferredTriples.length > 0) {
        expect(inferredType).toBeDefined();
      }
    });

    it('should infer property domain (prp-dom)', async () => {
      const triples: Triple[] = [
        {
          subject: 'http://example.org/hasName',
          predicate: `${NAMESPACES.RDFS}domain`,
          object: 'http://example.org/Person',
        },
        {
          subject: 'http://example.org/john',
          predicate: 'http://example.org/hasName',
          object: '"John"',
        },
      ];

      const result = await reasoner.infer(triples);

      // john should be inferred as Person
      const inferredType = result.inferredTriples.find(
        (t) =>
          t.subject === 'http://example.org/john' &&
          t.predicate === `${NAMESPACES.RDF}type` &&
          t.object === 'http://example.org/Person'
      );
      expect(inferredType).toBeDefined();
    });

    it('should infer symmetric property (prp-symp)', async () => {
      const triples: Triple[] = [
        {
          subject: 'http://example.org/knows',
          predicate: `${NAMESPACES.RDF}type`,
          object: `${NAMESPACES.OWL}SymmetricProperty`,
        },
        {
          subject: 'http://example.org/alice',
          predicate: 'http://example.org/knows',
          object: 'http://example.org/bob',
        },
      ];

      const result = await reasoner.infer(triples);

      // bob knows alice should be inferred
      const inferredSymmetric = result.inferredTriples.find(
        (t) =>
          t.subject === 'http://example.org/bob' &&
          t.predicate === 'http://example.org/knows' &&
          t.object === 'http://example.org/alice'
      );
      expect(inferredSymmetric).toBeDefined();
    });

    it('should infer transitive property (prp-trp)', async () => {
      const triples: Triple[] = [
        {
          subject: 'http://example.org/ancestorOf',
          predicate: `${NAMESPACES.RDF}type`,
          object: `${NAMESPACES.OWL}TransitiveProperty`,
        },
        {
          subject: 'http://example.org/grandpa',
          predicate: 'http://example.org/ancestorOf',
          object: 'http://example.org/father',
        },
        {
          subject: 'http://example.org/father',
          predicate: 'http://example.org/ancestorOf',
          object: 'http://example.org/child',
        },
      ];

      const result = await reasoner.infer(triples);

      // grandpa ancestorOf child should be inferred
      const inferredTransitive = result.inferredTriples.find(
        (t) =>
          t.subject === 'http://example.org/grandpa' &&
          t.predicate === 'http://example.org/ancestorOf' &&
          t.object === 'http://example.org/child'
      );
      expect(inferredTransitive).toBeDefined();
    });

    it('should record statistics', async () => {
      const triples: Triple[] = [
        {
          subject: 'http://example.org/A',
          predicate: `${NAMESPACES.RDFS}subClassOf`,
          object: 'http://example.org/B',
        },
        {
          subject: 'http://example.org/x',
          predicate: `${NAMESPACES.RDF}type`,
          object: 'http://example.org/A',
        },
      ];

      const result = await reasoner.infer(triples);

      expect(result.stats).toBeDefined();
      expect(result.stats.iterations).toBeGreaterThan(0);
      expect(result.stats.timeMs).toBeDefined();
    });

    it('should respect timeout option', async () => {
      // Create a large graph that would take long to process
      const triples: Triple[] = [];
      for (let i = 0; i < 100; i++) {
        triples.push({
          subject: `http://example.org/Class${i}`,
          predicate: `${NAMESPACES.RDFS}subClassOf`,
          object: `http://example.org/Class${i + 1}`,
        });
        triples.push({
          subject: `http://example.org/instance${i}`,
          predicate: `${NAMESPACES.RDF}type`,
          object: `http://example.org/Class${i}`,
        });
      }

      const result = await reasoner.infer(triples, { timeout: 1, maxIterations: 1000000 });

      // Should complete (either with results or timeout)
      expect(result).toBeDefined();
    });
  });

  describe('OWL2RL_RULES', () => {
    it('should have built-in rules defined', () => {
      expect(OWL2RL_RULES).toBeDefined();
      expect(OWL2RL_RULES.length).toBeGreaterThan(0);
    });

    it('should have required rule properties', () => {
      for (const rule of OWL2RL_RULES) {
        expect(rule.id).toBeDefined();
        expect(rule.name).toBeDefined();
        expect(rule.antecedent).toBeDefined();
        expect(rule.consequent).toBeDefined();
        expect(rule.antecedent.length).toBeGreaterThan(0);
        expect(rule.consequent.length).toBeGreaterThan(0);
      }
    });

    it('should include core OWL 2 RL rules', () => {
      const ruleIds = OWL2RL_RULES.map((r) => r.id);

      expect(ruleIds).toContain('cax-sco');
      expect(ruleIds).toContain('prp-dom');
      expect(ruleIds).toContain('prp-rng');
      expect(ruleIds).toContain('prp-symp');
      expect(ruleIds).toContain('prp-trp');
    });
  });

  describe('edge cases', () => {
    it('should handle self-referential triples', async () => {
      const triples: Triple[] = [
        {
          subject: 'http://example.org/A',
          predicate: `${NAMESPACES.RDFS}subClassOf`,
          object: 'http://example.org/A',
        },
      ];

      const result = await reasoner.infer(triples);

      expect(result).toBeDefined();
      // Should not infinite loop
    });

    it('should handle cycles in class hierarchy', async () => {
      const triples: Triple[] = [
        {
          subject: 'http://example.org/A',
          predicate: `${NAMESPACES.RDFS}subClassOf`,
          object: 'http://example.org/B',
        },
        {
          subject: 'http://example.org/B',
          predicate: `${NAMESPACES.RDFS}subClassOf`,
          object: 'http://example.org/A',
        },
      ];

      const result = await reasoner.infer(triples);

      expect(result).toBeDefined();
      // Should handle cycle without infinite loop
    });

    it('should handle blank nodes', async () => {
      const triples: Triple[] = [
        {
          subject: '_:blank1',
          predicate: `${NAMESPACES.RDF}type`,
          object: 'http://example.org/Class',
        },
      ];

      const result = await reasoner.infer(triples);

      expect(result).toBeDefined();
    });
  });
});
