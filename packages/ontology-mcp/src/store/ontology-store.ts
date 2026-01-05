/**
 * @fileoverview Ontology store with local persistence
 * @traceability TSK-ONTO-001, REQ-ONTO-001-F001
 */

import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';
import type { Ontology, Triple, OntologyStoreConfig } from '../types.js';

/**
 * Ontology store with local JSON persistence
 * 
 * @description
 * Manages ontology storage locally (no external communication).
 * Supports CRUD operations on ontologies and triples.
 */
export class OntologyStore {
  private ontologies: Map<string, Ontology> = new Map();
  private config: OntologyStoreConfig;
  private dirty = false;

  constructor(config: Partial<OntologyStoreConfig> = {}) {
    this.config = {
      storagePath: config.storagePath ?? './storage/ontology/store.json',
      enableInference: config.enableInference ?? true,
      maxTriples: config.maxTriples ?? 100000,
    };
  }

  /**
   * Load store from disk
   */
  async load(): Promise<void> {
    try {
      const data = await readFile(this.config.storagePath, 'utf-8');
      const parsed = JSON.parse(data) as { ontologies: Ontology[] };
      this.ontologies.clear();
      for (const onto of parsed.ontologies) {
        this.ontologies.set(onto.id, onto);
      }
      this.dirty = false;
    } catch {
      // File doesn't exist yet - start with empty store
      this.ontologies.clear();
    }
  }

  /**
   * Save store to disk
   */
  async save(): Promise<void> {
    if (!this.dirty) return;

    const dir = dirname(this.config.storagePath);
    await mkdir(dir, { recursive: true });

    const data = {
      version: '1.0.0',
      updatedAt: new Date().toISOString(),
      ontologies: Array.from(this.ontologies.values()),
    };

    await writeFile(this.config.storagePath, JSON.stringify(data, null, 2), 'utf-8');
    this.dirty = false;
  }

  /**
   * Create new ontology
   */
  create(id: string, namespace: string, prefixes: Record<string, string> = {}): Ontology {
    const now = new Date().toISOString();
    const ontology: Ontology = {
      id,
      namespace,
      prefixes,
      triples: [],
      createdAt: now,
      updatedAt: now,
    };
    this.ontologies.set(id, ontology);
    this.dirty = true;
    return ontology;
  }

  /**
   * Get ontology by ID
   */
  get(id: string): Ontology | undefined {
    return this.ontologies.get(id);
  }

  /**
   * Delete ontology
   */
  delete(id: string): boolean {
    const deleted = this.ontologies.delete(id);
    if (deleted) {
      this.dirty = true;
    }
    return deleted;
  }

  /**
   * Add triple to ontology
   */
  addTriple(ontologyId: string, triple: Triple): boolean {
    const ontology = this.ontologies.get(ontologyId);
    if (!ontology) return false;

    const totalTriples = Array.from(this.ontologies.values())
      .reduce((sum, o) => sum + o.triples.length, 0);
    
    if (totalTriples >= this.config.maxTriples) {
      return false;
    }

    ontology.triples.push(triple);
    ontology.updatedAt = new Date().toISOString();
    this.dirty = true;
    return true;
  }

  /**
   * Get all triples from ontology
   */
  getTriples(ontologyId: string): Triple[] {
    return this.ontologies.get(ontologyId)?.triples ?? [];
  }

  /**
   * List all ontologies
   */
  list(): Ontology[] {
    return Array.from(this.ontologies.values());
  }

  /**
   * Get total triple count
   */
  get tripleCount(): number {
    return Array.from(this.ontologies.values())
      .reduce((sum, o) => sum + o.triples.length, 0);
  }

  /**
   * Get ontology count
   */
  get size(): number {
    return this.ontologies.size;
  }
}
