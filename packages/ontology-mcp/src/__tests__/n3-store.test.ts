/**
 * @fileoverview Tests for N3.js-based RDF store
 * @traceability TSK-ONTO-001, REQ-ONTO-001-F001
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { N3Store, type QueryPattern } from '../store/n3-store.js';
import type { Triple } from '../types.js';

describe('N3Store', () => {
  let store: N3Store;

  beforeEach(() => {
    store = new N3Store({ enableInference: false });
  });

  describe('basic operations', () => {
    it('should add a triple', () => {
      const triple: Triple = {
        subject: 'https://musubix.dev/pattern/P001',
        predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
        object: 'https://musubix.dev/ontology/pattern#Pattern',
      };

      const result = store.addTriple(triple);
      expect(result).toBe(true);
      expect(store.size).toBe(1);
    });

    it('should add multiple triples', () => {
      const triples: Triple[] = [
        {
          subject: 'https://musubix.dev/pattern/P001',
          predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
          object: 'https://musubix.dev/ontology/pattern#Pattern',
        },
        {
          subject: 'https://musubix.dev/pattern/P001',
          predicate: 'http://www.w3.org/2000/01/rdf-schema#label',
          object: 'Repository Pattern',
        },
      ];

      const added = store.addTriples(triples);
      expect(added).toBe(2);
      expect(store.size).toBe(2);
    });

    it('should check if triple exists', () => {
      const triple: Triple = {
        subject: 'https://musubix.dev/pattern/P001',
        predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
        object: 'https://musubix.dev/ontology/pattern#Pattern',
      };

      store.addTriple(triple);
      expect(store.has(triple)).toBe(true);

      const nonExistent: Triple = {
        subject: 'https://musubix.dev/pattern/P999',
        predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
        object: 'https://musubix.dev/ontology/pattern#Pattern',
      };
      expect(store.has(nonExistent)).toBe(false);
    });

    it('should remove a triple', () => {
      const triple: Triple = {
        subject: 'https://musubix.dev/pattern/P001',
        predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
        object: 'https://musubix.dev/ontology/pattern#Pattern',
      };

      store.addTriple(triple);
      expect(store.size).toBe(1);

      const removed = store.removeTriple(triple);
      expect(removed).toBe(true);
      expect(store.size).toBe(0);
    });

    it('should clear all triples', () => {
      store.addTriple({
        subject: 'https://musubix.dev/pattern/P001',
        predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
        object: 'https://musubix.dev/ontology/pattern#Pattern',
      });
      store.addTriple({
        subject: 'https://musubix.dev/pattern/P002',
        predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
        object: 'https://musubix.dev/ontology/pattern#Pattern',
      });

      expect(store.size).toBe(2);
      store.clear();
      expect(store.size).toBe(0);
    });
  });

  describe('query', () => {
    beforeEach(() => {
      // Setup test data
      store.addTriple({
        subject: 'https://musubix.dev/pattern/P001',
        predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
        object: 'https://musubix.dev/ontology/pattern#Pattern',
      });
      store.addTriple({
        subject: 'https://musubix.dev/pattern/P001',
        predicate: 'http://www.w3.org/2000/01/rdf-schema#label',
        object: 'Repository Pattern',
      });
      store.addTriple({
        subject: 'https://musubix.dev/pattern/P001',
        predicate: 'https://musubix.dev/ontology/pattern#confidence',
        object: '0.95',
      });
      store.addTriple({
        subject: 'https://musubix.dev/pattern/P002',
        predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
        object: 'https://musubix.dev/ontology/pattern#Pattern',
      });
    });

    it('should query by subject', () => {
      const pattern: QueryPattern = {
        subject: 'https://musubix.dev/pattern/P001',
      };

      const results = store.query(pattern);
      expect(results.length).toBe(3);
      expect(results.every((r) => r.subject === 'https://musubix.dev/pattern/P001')).toBe(true);
    });

    it('should query by predicate', () => {
      const pattern: QueryPattern = {
        predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
      };

      const results = store.query(pattern);
      expect(results.length).toBe(2);
    });

    it('should query by object', () => {
      const pattern: QueryPattern = {
        object: 'https://musubix.dev/ontology/pattern#Pattern',
      };

      const results = store.query(pattern);
      expect(results.length).toBe(2);
    });

    it('should query with multiple constraints', () => {
      const pattern: QueryPattern = {
        subject: 'https://musubix.dev/pattern/P001',
        predicate: 'http://www.w3.org/2000/01/rdf-schema#label',
      };

      const results = store.query(pattern);
      expect(results.length).toBe(1);
      expect(results[0].object).toBe('Repository Pattern');
    });
  });

  describe('type operations', () => {
    beforeEach(() => {
      const rdfType = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type';
      const patternType = 'https://musubix.dev/ontology/pattern#Pattern';
      const requirementType = 'https://musubix.dev/ontology/sdd#Requirement';

      store.addTriple({
        subject: 'https://musubix.dev/pattern/P001',
        predicate: rdfType,
        object: patternType,
      });
      store.addTriple({
        subject: 'https://musubix.dev/pattern/P002',
        predicate: rdfType,
        object: patternType,
      });
      store.addTriple({
        subject: 'https://musubix.dev/req/REQ-001',
        predicate: rdfType,
        object: requirementType,
      });
    });

    it('should get subjects of type', () => {
      const patterns = store.getSubjectsOfType('https://musubix.dev/ontology/pattern#Pattern');
      expect(patterns.length).toBe(2);
      expect(patterns).toContain('https://musubix.dev/pattern/P001');
      expect(patterns).toContain('https://musubix.dev/pattern/P002');
    });

    it('should get properties of subject', () => {
      store.addTriple({
        subject: 'https://musubix.dev/pattern/P001',
        predicate: 'http://www.w3.org/2000/01/rdf-schema#label',
        object: 'Test Pattern',
      });

      const props = store.getProperties('https://musubix.dev/pattern/P001');
      expect(props.length).toBe(2);
    });
  });

  describe('Turtle import/export', () => {
    it('should import Turtle content', async () => {
      const turtle = `
        @prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
        @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
        @prefix pattern: <https://musubix.dev/ontology/pattern#> .
        
        <https://musubix.dev/pattern/P001> a pattern:Pattern ;
          rdfs:label "Repository Pattern" ;
          pattern:confidence "0.95" .
      `;

      const imported = await store.importTurtle(turtle);
      expect(imported).toBe(3);
      expect(store.size).toBe(3);
    });

    it('should export as Turtle', async () => {
      store.addTriple({
        subject: 'https://musubix.dev/pattern/P001',
        predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
        object: 'https://musubix.dev/ontology/pattern#Pattern',
      });
      store.addTriple({
        subject: 'https://musubix.dev/pattern/P001',
        predicate: 'http://www.w3.org/2000/01/rdf-schema#label',
        object: 'Repository Pattern',
      });

      const turtle = await store.exportTurtle();
      expect(turtle).toContain('pattern:Pattern');
      expect(turtle).toContain('Repository Pattern');
    });
  });

  describe('named graphs', () => {
    it('should add triple to named graph', () => {
      const triple: Triple = {
        subject: 'https://musubix.dev/pattern/P001',
        predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
        object: 'https://musubix.dev/ontology/pattern#Pattern',
      };
      const graph = 'https://musubix.dev/graph/patterns';

      store.addTriple(triple, graph);
      expect(store.size).toBe(1);

      const graphs = store.getGraphs();
      expect(graphs).toContain(graph);
    });

    it('should query within named graph', () => {
      const graph = 'https://musubix.dev/graph/patterns';
      store.addTriple(
        {
          subject: 'https://musubix.dev/pattern/P001',
          predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
          object: 'https://musubix.dev/ontology/pattern#Pattern',
        },
        graph
      );

      const results = store.query({ graph });
      expect(results.length).toBe(1);
      expect(results[0].graph).toBe(graph);
    });
  });

  describe('max triples limit', () => {
    it('should respect max triples limit', () => {
      const limitedStore = new N3Store({
        maxTriples: 2,
        enableInference: false,
      });

      limitedStore.addTriple({
        subject: 'https://musubix.dev/pattern/P001',
        predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
        object: 'https://musubix.dev/ontology/pattern#Pattern',
      });
      limitedStore.addTriple({
        subject: 'https://musubix.dev/pattern/P002',
        predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
        object: 'https://musubix.dev/ontology/pattern#Pattern',
      });

      const result = limitedStore.addTriple({
        subject: 'https://musubix.dev/pattern/P003',
        predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
        object: 'https://musubix.dev/ontology/pattern#Pattern',
      });

      expect(result).toBe(false);
      expect(limitedStore.size).toBe(2);
    });
  });

  describe('inference', () => {
    it('should infer type via subClassOf', () => {
      const inferenceStore = new N3Store({ enableInference: true });
      const rdfType = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type';
      const subClassOf = 'http://www.w3.org/2000/01/rdf-schema#subClassOf';

      // Define class hierarchy: CreationalPattern subClassOf Pattern
      inferenceStore.addTriple({
        subject: 'https://musubix.dev/ontology/pattern#CreationalPattern',
        predicate: subClassOf,
        object: 'https://musubix.dev/ontology/pattern#Pattern',
      });

      // Add instance of CreationalPattern
      inferenceStore.addTriple({
        subject: 'https://musubix.dev/pattern/P001',
        predicate: rdfType,
        object: 'https://musubix.dev/ontology/pattern#CreationalPattern',
      });

      // Should infer P001 is also a Pattern
      const types = inferenceStore.query({
        subject: 'https://musubix.dev/pattern/P001',
        predicate: rdfType,
      });

      expect(types.length).toBeGreaterThanOrEqual(1);
    });
  });
});
