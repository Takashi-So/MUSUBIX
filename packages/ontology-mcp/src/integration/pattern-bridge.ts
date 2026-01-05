/**
 * @fileoverview Pattern-Ontology Integration Bridge
 * @traceability TSK-INT-001, REQ-INT-001
 * 
 * Integrates Pattern Library Learning with Ontology Reasoning:
 * - Converts patterns to RDF triples for knowledge graph
 * - Applies inference rules to discover pattern relationships
 * - Enables semantic querying of pattern library
 */

import type { Pattern, ASTNode } from '@nahisaho/musubix-pattern-mcp';
import type { Triple } from '../types.js';
import { N3Store } from '../store/n3-store.js';
import { RuleEngine, type InferenceStats } from '../inference/rule-engine.js';

/**
 * Namespace URIs
 */
const NS = {
  pattern: 'https://musubix.dev/ontology/pattern#',
  sdd: 'https://musubix.dev/ontology/sdd#',
  rdf: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#',
  rdfs: 'http://www.w3.org/2000/01/rdf-schema#',
  owl: 'http://www.w3.org/2002/07/owl#',
};

/**
 * Pattern relationship types
 */
export type PatternRelation = 
  | 'subsumes'      // Pattern A is more general than B
  | 'specializes'   // Pattern A is more specific than B
  | 'similarTo'     // Patterns have high structural similarity
  | 'composedOf'    // Pattern A contains pattern B
  | 'usedWith'      // Patterns frequently appear together
  | 'derivedFrom';  // Pattern A was derived from B

/**
 * Pattern relationship with confidence
 */
export interface PatternRelationship {
  source: string;
  target: string;
  relation: PatternRelation;
  confidence: number;
  evidence?: string[];
}

/**
 * Integration query result
 */
export interface PatternQueryResult {
  patterns: Pattern[];
  relationships: PatternRelationship[];
  inferenceStats?: InferenceStats;
}

/**
 * Pattern-Ontology Bridge Configuration
 */
export interface BridgeConfig {
  /** Enable automatic inference */
  enableInference: boolean;
  /** Minimum confidence for relationships */
  minConfidence: number;
  /** Maximum inference iterations */
  maxInferenceIterations: number;
}

/**
 * Pattern-Ontology Integration Bridge
 * 
 * Provides bidirectional integration between:
 * - Pattern Library (structural code patterns)
 * - Ontology Store (semantic knowledge graph)
 */
export class PatternOntologyBridge {
  private store: N3Store;
  private ruleEngine: RuleEngine;
  private config: BridgeConfig;
  private patternCache: Map<string, Pattern> = new Map();

  constructor(store: N3Store, config?: Partial<BridgeConfig>) {
    this.store = store;
    this.config = {
      enableInference: config?.enableInference ?? true,
      minConfidence: config?.minConfidence ?? 0.5,
      maxInferenceIterations: config?.maxInferenceIterations ?? 5,
    };
    this.ruleEngine = new RuleEngine({
      maxIterations: this.config.maxInferenceIterations,
    });

    // Add pattern-specific inference rules
    this.addPatternInferenceRules();
  }

  /**
   * Add pattern-specific inference rules
   */
  private addPatternInferenceRules(): void {
    // Subsumption transitivity
    this.ruleEngine.addRule({
      id: 'pattern-subsumes-trans',
      name: 'Pattern Subsumption Transitivity',
      description: 'If A subsumes B and B subsumes C, then A subsumes C',
      priority: 90,
      conditions: [
        { type: 'transitive', predicate: `${NS.pattern}subsumes` },
      ],
      actions: [],
    });

    // Subsumes implies specializes inverse
    this.ruleEngine.addRule({
      id: 'pattern-subsumes-inverse',
      name: 'Subsumes-Specializes Inverse',
      description: 'If A subsumes B, then B specializes A',
      priority: 85,
      conditions: [
        { type: 'inverse', predicate1: `${NS.pattern}subsumes`, predicate2: `${NS.pattern}specializes` },
      ],
      actions: [],
    });

    // SimilarTo is symmetric
    this.ruleEngine.addRule({
      id: 'pattern-similar-sym',
      name: 'Pattern Similarity Symmetry',
      description: 'If A similarTo B, then B similarTo A',
      priority: 80,
      conditions: [
        { type: 'symmetric', predicate: `${NS.pattern}similarTo` },
      ],
      actions: [],
    });
  }

  /**
   * Import pattern into ontology
   */
  importPattern(pattern: Pattern): boolean {
    const patternUri = this.getPatternUri(pattern.id);

    // Store pattern in cache
    this.patternCache.set(pattern.id, pattern);

    // Create pattern entity triples
    const triples: Triple[] = [
      // Type declaration
      {
        subject: patternUri,
        predicate: `${NS.rdf}type`,
        object: `${NS.pattern}Pattern`,
      },
      // Name
      {
        subject: patternUri,
        predicate: `${NS.rdfs}label`,
        object: pattern.name,
      },
      // Language
      {
        subject: patternUri,
        predicate: `${NS.pattern}language`,
        object: pattern.language,
      },
      // AST root type
      {
        subject: patternUri,
        predicate: `${NS.pattern}astType`,
        object: pattern.ast.type,
      },
      // Frequency
      {
        subject: patternUri,
        predicate: `${NS.pattern}frequency`,
        object: String(pattern.frequency),
      },
      // Hole count
      {
        subject: patternUri,
        predicate: `${NS.pattern}holeCount`,
        object: String(pattern.holes.length),
      },
    ];

    // Add hole types
    for (const hole of pattern.holes) {
      triples.push({
        subject: patternUri,
        predicate: `${NS.pattern}hasHoleType`,
        object: hole.type,
      });
    }

    // Add AST structure classification
    const structureClass = this.classifyASTStructure(pattern.ast);
    triples.push({
      subject: patternUri,
      predicate: `${NS.pattern}structureClass`,
      object: structureClass,
    });

    // Add complexity metrics
    const complexity = this.calculateComplexity(pattern.ast);
    triples.push({
      subject: patternUri,
      predicate: `${NS.pattern}complexity`,
      object: String(complexity),
    });

    // Store triples
    return this.store.addTriples(triples) === triples.length;
  }

  /**
   * Import multiple patterns
   */
  importPatterns(patterns: Pattern[]): number {
    let imported = 0;
    for (const pattern of patterns) {
      if (this.importPattern(pattern)) {
        imported++;
      }
    }

    // Discover relationships after import
    if (this.config.enableInference) {
      this.discoverRelationships(patterns);
    }

    return imported;
  }

  /**
   * Discover relationships between patterns
   */
  discoverRelationships(patterns: Pattern[]): PatternRelationship[] {
    const relationships: PatternRelationship[] = [];

    for (let i = 0; i < patterns.length; i++) {
      for (let j = i + 1; j < patterns.length; j++) {
        const a = patterns[i];
        const b = patterns[j];

        // Check subsumption
        const subsumption = this.checkSubsumption(a, b);
        if (subsumption) {
          relationships.push(subsumption);
          this.addRelationshipTriple(subsumption);
        }

        // Check similarity
        const similarity = this.checkSimilarity(a, b);
        if (similarity && similarity.confidence >= this.config.minConfidence) {
          relationships.push(similarity);
          this.addRelationshipTriple(similarity);
        }

        // Check composition
        const composition = this.checkComposition(a, b);
        if (composition) {
          relationships.push(composition);
          this.addRelationshipTriple(composition);
        }
      }
    }

    // Apply inference rules
    if (this.config.enableInference) {
      this.applyInference();
    }

    return relationships;
  }

  /**
   * Check if pattern A subsumes pattern B
   */
  private checkSubsumption(a: Pattern, b: Pattern): PatternRelationship | null {
    // A subsumes B if A is more general (has more holes at same positions)
    if (a.ast.type !== b.ast.type) return null;
    if (a.language !== b.language) return null;

    const aHoleCount = a.holes.length;
    const bHoleCount = b.holes.length;

    // More holes = more general
    if (aHoleCount > bHoleCount) {
      const confidence = Math.min(1.0, (aHoleCount - bHoleCount) / Math.max(aHoleCount, 1) + 0.5);
      return {
        source: a.id,
        target: b.id,
        relation: 'subsumes',
        confidence,
        evidence: [`A has ${aHoleCount} holes, B has ${bHoleCount} holes`],
      };
    }

    return null;
  }

  /**
   * Check similarity between patterns
   */
  private checkSimilarity(a: Pattern, b: Pattern): PatternRelationship | null {
    if (a.language !== b.language) return null;

    // Calculate structural similarity
    const similarity = this.calculateASTSimilarity(a.ast, b.ast);

    if (similarity >= this.config.minConfidence) {
      return {
        source: a.id,
        target: b.id,
        relation: 'similarTo',
        confidence: similarity,
        evidence: [`Structural similarity: ${(similarity * 100).toFixed(1)}%`],
      };
    }

    return null;
  }

  /**
   * Check if pattern A contains pattern B
   */
  private checkComposition(a: Pattern, b: Pattern): PatternRelationship | null {
    if (a.language !== b.language) return null;

    // Check if B's AST structure appears in A's children
    const contains = this.containsStructure(a.ast, b.ast);

    if (contains) {
      return {
        source: a.id,
        target: b.id,
        relation: 'composedOf',
        confidence: 0.8,
        evidence: [`Pattern A contains structure of pattern B`],
      };
    }

    return null;
  }

  /**
   * Calculate AST similarity
   */
  private calculateASTSimilarity(a: ASTNode, b: ASTNode): number {
    if (a.type !== b.type) return 0;

    let matches = 1;
    let total = 1;

    // Compare children
    const maxChildren = Math.max(a.children.length, b.children.length);
    const minChildren = Math.min(a.children.length, b.children.length);

    total += maxChildren;
    matches += minChildren;

    // Recursively compare matching children
    for (let i = 0; i < minChildren; i++) {
      const childSim = this.calculateASTSimilarity(a.children[i], b.children[i]);
      matches += childSim;
      total += 1;
    }

    return matches / total;
  }

  /**
   * Check if AST A contains structure B
   */
  private containsStructure(a: ASTNode, b: ASTNode): boolean {
    if (a.type === b.type && this.calculateASTSimilarity(a, b) > 0.9) {
      return true;
    }

    for (const child of a.children) {
      if (this.containsStructure(child, b)) {
        return true;
      }
    }

    return false;
  }

  /**
   * Add relationship triple to store
   */
  private addRelationshipTriple(rel: PatternRelationship): void {
    const sourceUri = this.getPatternUri(rel.source);
    const targetUri = this.getPatternUri(rel.target);
    const predicateUri = `${NS.pattern}${rel.relation}`;

    this.store.addTriple({
      subject: sourceUri,
      predicate: predicateUri,
      object: targetUri,
    });

    // Add confidence as annotation
    this.store.addTriple({
      subject: `${sourceUri}_${rel.relation}_${targetUri}`,
      predicate: `${NS.pattern}confidence`,
      object: String(rel.confidence),
    });
  }

  /**
   * Apply inference rules
   */
  private applyInference(): InferenceStats {
    // Get all triples
    const results = this.store.query({});
    const triples: Triple[] = results.map(r => ({
      subject: r.subject,
      predicate: r.predicate,
      object: r.object,
    }));

    // Apply rules
    const { triples: inferred, stats } = this.ruleEngine.applyRules(triples);

    // Add new triples
    for (const triple of inferred) {
      if (!this.store.has(triple)) {
        this.store.addTriple(triple);
      }
    }

    return stats;
  }

  /**
   * Query patterns by criteria
   */
  queryPatterns(criteria: {
    language?: string;
    astType?: string;
    minFrequency?: number;
    hasRelation?: PatternRelation;
    relatedTo?: string;
  }): PatternQueryResult {
    const results: Pattern[] = [];
    const relationships: PatternRelationship[] = [];

    // Build query pattern
    const patterns: string[] = [];

    if (criteria.language) {
      const langResults = this.store.query({
        predicate: `${NS.pattern}language`,
        object: criteria.language,
      });
      patterns.push(...langResults.map(r => r.subject));
    }

    if (criteria.astType) {
      const typeResults = this.store.query({
        predicate: `${NS.pattern}astType`,
        object: criteria.astType,
      });
      patterns.push(...typeResults.map(r => r.subject));
    }

    // Get unique pattern URIs
    const patternUris = patterns.length > 0
      ? [...new Set(patterns)]
      : this.store.getSubjectsOfType(`${NS.pattern}Pattern`);

    // Retrieve patterns from cache
    for (const uri of patternUris) {
      const id = this.getPatternIdFromUri(uri);
      const pattern = this.patternCache.get(id);

      if (pattern) {
        // Apply frequency filter
        if (criteria.minFrequency && pattern.frequency < criteria.minFrequency) {
          continue;
        }
        results.push(pattern);
      }
    }

    // Get relationships if requested
    if (criteria.hasRelation && criteria.relatedTo) {
      const relResults = this.store.query({
        predicate: `${NS.pattern}${criteria.hasRelation}`,
        object: this.getPatternUri(criteria.relatedTo),
      });

      for (const r of relResults) {
        relationships.push({
          source: this.getPatternIdFromUri(r.subject),
          target: criteria.relatedTo,
          relation: criteria.hasRelation,
          confidence: 1.0,
        });
      }
    }

    return { patterns: results, relationships };
  }

  /**
   * Find related patterns
   */
  findRelatedPatterns(patternId: string, relation?: PatternRelation): PatternRelationship[] {
    const patternUri = this.getPatternUri(patternId);
    const relationships: PatternRelationship[] = [];

    const relations: PatternRelation[] = relation
      ? [relation]
      : ['subsumes', 'specializes', 'similarTo', 'composedOf', 'usedWith', 'derivedFrom'];

    for (const rel of relations) {
      // Outgoing relationships
      const outgoing = this.store.query({
        subject: patternUri,
        predicate: `${NS.pattern}${rel}`,
      });

      for (const r of outgoing) {
        relationships.push({
          source: patternId,
          target: this.getPatternIdFromUri(r.object),
          relation: rel,
          confidence: 1.0,
        });
      }

      // Incoming relationships
      const incoming = this.store.query({
        predicate: `${NS.pattern}${rel}`,
        object: patternUri,
      });

      for (const r of incoming) {
        relationships.push({
          source: this.getPatternIdFromUri(r.subject),
          target: patternId,
          relation: rel,
          confidence: 1.0,
        });
      }
    }

    return relationships;
  }

  /**
   * Get pattern URI
   */
  private getPatternUri(id: string): string {
    return `${NS.pattern}${id}`;
  }

  /**
   * Extract pattern ID from URI
   */
  private getPatternIdFromUri(uri: string): string {
    return uri.replace(NS.pattern, '');
  }

  /**
   * Classify AST structure
   */
  private classifyASTStructure(ast: ASTNode): string {
    const type = ast.type.toLowerCase();

    if (type.includes('function') || type.includes('method')) {
      return 'function-like';
    }
    if (type.includes('class') || type.includes('interface')) {
      return 'type-definition';
    }
    if (type.includes('if') || type.includes('switch') || type.includes('conditional')) {
      return 'conditional';
    }
    if (type.includes('for') || type.includes('while') || type.includes('loop')) {
      return 'loop';
    }
    if (type.includes('try') || type.includes('catch')) {
      return 'error-handling';
    }
    if (type.includes('import') || type.includes('export')) {
      return 'module';
    }

    return 'other';
  }

  /**
   * Calculate AST complexity
   */
  private calculateComplexity(ast: ASTNode): number {
    let complexity = 1;

    for (const child of ast.children) {
      complexity += this.calculateComplexity(child);
    }

    // Bonus for certain node types
    if (ast.type.includes('If') || ast.type.includes('Loop') || ast.type.includes('Try')) {
      complexity += 1;
    }

    return complexity;
  }

  /**
   * Export pattern graph as Turtle
   */
  async exportAsTurtle(): Promise<string> {
    return this.store.exportTurtle({
      pattern: NS.pattern,
      sdd: NS.sdd,
      rdf: NS.rdf,
      rdfs: NS.rdfs,
      owl: NS.owl,
    });
  }

  /**
   * Get statistics
   */
  getStats(): {
    patternCount: number;
    tripleCount: number;
    relationshipCount: number;
  } {
    const patterns = this.store.getSubjectsOfType(`${NS.pattern}Pattern`);
    
    let relationshipCount = 0;
    const relations: PatternRelation[] = ['subsumes', 'specializes', 'similarTo', 'composedOf', 'usedWith', 'derivedFrom'];
    for (const rel of relations) {
      relationshipCount += this.store.query({ predicate: `${NS.pattern}${rel}` }).length;
    }

    return {
      patternCount: patterns.length,
      tripleCount: this.store.size,
      relationshipCount,
    };
  }
}
