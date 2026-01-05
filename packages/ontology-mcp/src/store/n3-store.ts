/**
 * @fileoverview N3.js-based RDF triple store
 * @traceability TSK-ONTO-001, REQ-ONTO-001-F001
 */

import * as N3 from 'n3';
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';
import type { Triple, OntologyStoreConfig } from '../types.js';

const { DataFactory, Store, Writer, Parser } = N3;
const { namedNode, literal, quad } = DataFactory;

/**
 * Query pattern for SPARQL-like queries
 */
export interface QueryPattern {
  subject?: string;
  predicate?: string;
  object?: string;
  graph?: string;
}

/**
 * N3 Query result (different from types.ts QueryResult)
 */
export interface N3QueryResult {
  subject: string;
  predicate: string;
  object: string;
  graph?: string;
}

/**
 * Inference rule
 */
export interface InferenceRule {
  id: string;
  name: string;
  pattern: QueryPattern;
  conclusion: (bindings: Record<string, string>) => Triple[];
}

/**
 * N3.js-based RDF store with inference support
 * 
 * @description
 * Provides a high-performance RDF triple store using N3.js.
 * Supports:
 * - Turtle/N-Triples/N-Quads parsing and serialization
 * - Pattern-based querying
 * - Basic RDFS inference
 * - Named graphs
 */
export class N3Store {
  private store: N3.Store;
  private config: OntologyStoreConfig;
  private dirty = false;
  private inferenceRules: InferenceRule[] = [];

  constructor(config: Partial<OntologyStoreConfig> = {}) {
    this.store = new Store();
    this.config = {
      storagePath: config.storagePath ?? './storage/ontology/n3-store.ttl',
      enableInference: config.enableInference ?? true,
      maxTriples: config.maxTriples ?? 100000,
    };

    if (this.config.enableInference) {
      this.initializeInferenceRules();
    }
  }

  /**
   * Initialize RDFS inference rules
   */
  private initializeInferenceRules(): void {
    // rdfs:subClassOf transitivity
    this.inferenceRules.push({
      id: 'rdfs-subclass-transitivity',
      name: 'RDFS SubClass Transitivity',
      pattern: {
        predicate: 'http://www.w3.org/2000/01/rdf-schema#subClassOf',
      },
      conclusion: (bindings) => {
        // A subClassOf B, B subClassOf C => A subClassOf C
        const results: Triple[] = [];
        const subClassOf = 'http://www.w3.org/2000/01/rdf-schema#subClassOf';
        
        // Find all superclasses of bindings.object
        const superQuads = this.store.getQuads(
          namedNode(bindings.object),
          namedNode(subClassOf),
          null,
          null
        );
        
        for (const superQuad of superQuads) {
          results.push({
            subject: bindings.subject,
            predicate: subClassOf,
            object: superQuad.object.value,
          });
        }
        
        return results;
      },
    });

    // rdf:type propagation via rdfs:subClassOf
    this.inferenceRules.push({
      id: 'rdfs-type-subclass',
      name: 'RDFS Type via SubClass',
      pattern: {
        predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
      },
      conclusion: (bindings) => {
        const results: Triple[] = [];
        const rdfType = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type';
        const subClassOf = 'http://www.w3.org/2000/01/rdf-schema#subClassOf';
        
        // Find all superclasses of bindings.object
        const superQuads = this.store.getQuads(
          namedNode(bindings.object),
          namedNode(subClassOf),
          null,
          null
        );
        
        for (const superQuad of superQuads) {
          results.push({
            subject: bindings.subject,
            predicate: rdfType,
            object: superQuad.object.value,
          });
        }
        
        return results;
      },
    });
  }

  /**
   * Load store from Turtle file
   */
  async load(): Promise<void> {
    try {
      const data = await readFile(this.config.storagePath, 'utf-8');
      const parser = new Parser();
      const quads = parser.parse(data);
      this.store = new Store(quads);
      this.dirty = false;
    } catch {
      // File doesn't exist - start with empty store
      this.store = new Store();
    }
  }

  /**
   * Save store to Turtle file
   */
  async save(): Promise<void> {
    if (!this.dirty) return;

    const dir = dirname(this.config.storagePath);
    await mkdir(dir, { recursive: true });

    const writer = new Writer({
      prefixes: {
        rdf: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#',
        rdfs: 'http://www.w3.org/2000/01/rdf-schema#',
        owl: 'http://www.w3.org/2002/07/owl#',
        xsd: 'http://www.w3.org/2001/XMLSchema#',
        sdd: 'https://musubix.dev/ontology/sdd#',
        pattern: 'https://musubix.dev/ontology/pattern#',
      },
    });

    const quads = this.store.getQuads(null, null, null, null);
    for (const q of quads) {
      writer.addQuad(q);
    }

    return new Promise((resolve, reject) => {
      writer.end((error, result) => {
        if (error) {
          reject(error);
        } else {
          writeFile(this.config.storagePath, result, 'utf-8')
            .then(() => {
              this.dirty = false;
              resolve();
            })
            .catch(reject);
        }
      });
    });
  }

  /**
   * Add a triple to the store
   */
  addTriple(triple: Triple, graph?: string): boolean {
    if (this.store.size >= this.config.maxTriples) {
      return false;
    }

    const subject = namedNode(triple.subject);
    const predicate = namedNode(triple.predicate);
    const object = triple.object.startsWith('http://') || triple.object.startsWith('https://')
      ? namedNode(triple.object)
      : literal(triple.object);
    const graphNode = graph ? namedNode(graph) : DataFactory.defaultGraph();

    this.store.addQuad(quad(subject, predicate, object, graphNode));
    this.dirty = true;

    // Apply inference if enabled
    if (this.config.enableInference) {
      this.applyInference(triple);
    }

    return true;
  }

  /**
   * Add multiple triples
   */
  addTriples(triples: Triple[], graph?: string): number {
    let added = 0;
    for (const triple of triples) {
      if (this.addTriple(triple, graph)) {
        added++;
      }
    }
    return added;
  }

  /**
   * Remove a triple from the store
   */
  removeTriple(triple: Triple, graph?: string): boolean {
    const subject = namedNode(triple.subject);
    const predicate = namedNode(triple.predicate);
    const object = triple.object.startsWith('http://') || triple.object.startsWith('https://')
      ? namedNode(triple.object)
      : literal(triple.object);
    const graphNode = graph ? namedNode(graph) : null;

    const quads = this.store.getQuads(subject, predicate, object, graphNode);
    if (quads.length === 0) return false;

    for (const q of quads) {
      this.store.removeQuad(q);
    }
    this.dirty = true;
    return true;
  }

  /**
   * Query triples by pattern
   */
  query(pattern: QueryPattern): N3QueryResult[] {
    const subject = pattern.subject ? namedNode(pattern.subject) : null;
    const predicate = pattern.predicate ? namedNode(pattern.predicate) : null;
    const object = pattern.object
      ? pattern.object.startsWith('http://') || pattern.object.startsWith('https://')
        ? namedNode(pattern.object)
        : literal(pattern.object)
      : null;
    const graph = pattern.graph ? namedNode(pattern.graph) : null;

    const quads = this.store.getQuads(subject, predicate, object, graph);

    return quads.map((q) => ({
      subject: q.subject.value,
      predicate: q.predicate.value,
      object: q.object.value,
      graph: q.graph.value || undefined,
    }));
  }

  /**
   * Check if a triple exists
   */
  has(triple: Triple, graph?: string): boolean {
    const subject = namedNode(triple.subject);
    const predicate = namedNode(triple.predicate);
    const object = triple.object.startsWith('http://') || triple.object.startsWith('https://')
      ? namedNode(triple.object)
      : literal(triple.object);
    const graphNode = graph ? namedNode(graph) : null;

    return this.store.getQuads(subject, predicate, object, graphNode).length > 0;
  }

  /**
   * Get all subjects of a given type
   */
  getSubjectsOfType(typeUri: string): string[] {
    const rdfType = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type';
    const quads = this.store.getQuads(null, namedNode(rdfType), namedNode(typeUri), null);
    return quads.map((q) => q.subject.value);
  }

  /**
   * Get all properties of a subject
   */
  getProperties(subject: string): N3QueryResult[] {
    const quads = this.store.getQuads(namedNode(subject), null, null, null);
    return quads.map((q) => ({
      subject: q.subject.value,
      predicate: q.predicate.value,
      object: q.object.value,
      graph: q.graph.value || undefined,
    }));
  }

  /**
   * Parse and import Turtle content
   */
  async importTurtle(content: string): Promise<number> {
    const parser = new Parser();
    const quads = parser.parse(content);
    
    let added = 0;
    for (const q of quads) {
      if (this.store.size >= this.config.maxTriples) break;
      this.store.addQuad(q);
      added++;
    }
    
    this.dirty = true;
    return added;
  }

  /**
   * Export store as Turtle
   */
  exportTurtle(prefixes?: Record<string, string>): Promise<string> {
    const writer = new Writer({
      prefixes: prefixes ?? {
        rdf: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#',
        rdfs: 'http://www.w3.org/2000/01/rdf-schema#',
        owl: 'http://www.w3.org/2002/07/owl#',
        sdd: 'https://musubix.dev/ontology/sdd#',
        pattern: 'https://musubix.dev/ontology/pattern#',
      },
    });

    const quads = this.store.getQuads(null, null, null, null);
    for (const q of quads) {
      writer.addQuad(q);
    }

    return new Promise((resolve, reject) => {
      writer.end((error, result) => {
        if (error) reject(error);
        else resolve(result);
      });
    });
  }

  /**
   * Apply inference rules for a triple
   */
  private applyInference(triple: Triple): void {
    const bindings = {
      subject: triple.subject,
      predicate: triple.predicate,
      object: triple.object,
    };

    for (const rule of this.inferenceRules) {
      // Check if pattern matches
      if (rule.pattern.predicate && rule.pattern.predicate !== triple.predicate) {
        continue;
      }
      if (rule.pattern.subject && rule.pattern.subject !== triple.subject) {
        continue;
      }
      if (rule.pattern.object && rule.pattern.object !== triple.object) {
        continue;
      }

      // Apply rule and add inferred triples
      const inferred = rule.conclusion(bindings);
      for (const inferredTriple of inferred) {
        if (!this.has(inferredTriple)) {
          this.addTriple(inferredTriple);
        }
      }
    }
  }

  /**
   * Clear all triples
   */
  clear(): void {
    this.store = new Store();
    this.dirty = true;
  }

  /**
   * Get triple count
   */
  get size(): number {
    return this.store.size;
  }

  /**
   * Get all named graphs
   */
  getGraphs(): string[] {
    const graphs = new Set<string>();
    const quads = this.store.getQuads(null, null, null, null);
    for (const q of quads) {
      if (q.graph.value) {
        graphs.add(q.graph.value);
      }
    }
    return Array.from(graphs);
  }
}
