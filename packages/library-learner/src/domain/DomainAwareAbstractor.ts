/**
 * DomainAwareAbstractor - Domain-Aware Pattern Abstraction
 * @module @nahisaho/musubix-library-learner
 * @see TSK-LL-106
 * @see DES-LL-106
 * @see REQ-LL-106 Domain-aware pattern abstraction
 */

import type { LearnedPattern } from '../types.js';

// ============================================================================
// Types
// ============================================================================

/**
 * DomainAwareAbstractor configuration
 */
export interface DomainAwareAbstractorConfig {
  /** Strict mode - require ontology for abstraction */
  strictMode: boolean;
  /** Maximum abstraction depth */
  maxAbstractionDepth: number;
  /** Minimum confidence for domain matching */
  minMatchConfidence: number;
}

/**
 * Domain ontology definition
 */
export interface DomainOntology {
  /** Ontology name */
  name: string;
  /** Version */
  version: string;
  /** Domain concepts */
  concepts: DomainConcept[];
  /** Domain constraints */
  constraints: DomainConstraint[];
}

/**
 * Domain concept
 */
export interface DomainConcept {
  /** Unique identifier */
  id: string;
  /** Concept name */
  name: string;
  /** Description */
  description: string;
  /** Properties of this concept */
  properties: string[];
  /** Relations to other concepts */
  relations: ConceptRelation[];
}

/**
 * Relation between concepts
 */
export interface ConceptRelation {
  /** Relation type */
  type: 'hasMany' | 'hasOne' | 'belongsTo' | 'extends' | 'implements';
  /** Target concept ID */
  target: string;
}

/**
 * Domain constraint
 */
export interface DomainConstraint {
  /** Constraint type */
  type: 'required' | 'unique' | 'positive' | 'range' | 'format' | 'custom';
  /** Target concept */
  concept: string;
  /** Target property */
  property: string;
  /** Constraint parameters */
  params?: Record<string, unknown>;
}

/**
 * Abstraction result with domain context
 */
export interface DomainAbstractionResult {
  /** Original pattern */
  pattern: LearnedPattern;
  /** Identified domain concepts */
  domainConcepts: string[];
  /** Applied constraints */
  constraints: DomainConstraint[];
  /** Confidence score */
  confidence: number;
  /** Abstraction suggestions */
  suggestions: string[];
}

/**
 * Concept hierarchy
 */
export interface ConceptHierarchy {
  /** Root concept */
  concept: DomainConcept;
  /** Related concepts */
  related: DomainConcept[];
  /** Depth in hierarchy */
  depth: number;
}

/**
 * Ontology load result
 */
export interface OntologyLoadResult {
  /** Success flag */
  success: boolean;
  /** Error message if failed */
  error?: string;
  /** Validation warnings */
  warnings: string[];
}

/**
 * Abstraction statistics
 */
export interface AbstractionStatistics {
  /** Total abstractions performed */
  totalAbstractions: number;
  /** Ontologies loaded count */
  ontologiesLoaded: number;
  /** Average match confidence */
  averageConfidence: number;
}

/**
 * DomainAwareAbstractor interface
 */
export interface DomainAwareAbstractor {
  /**
   * Load domain ontology
   */
  loadOntology(ontology: DomainOntology): OntologyLoadResult;

  /**
   * Get loaded ontology
   */
  getLoadedOntology(): DomainOntology | undefined;

  /**
   * Abstract pattern with domain context
   */
  abstractWithDomain(pattern: LearnedPattern): Promise<DomainAbstractionResult>;

  /**
   * Abstract multiple patterns
   */
  abstractBatch(patterns: LearnedPattern[]): Promise<DomainAbstractionResult[]>;

  /**
   * Find related domain concepts
   */
  findRelatedConcepts(term: string): DomainConcept[];

  /**
   * Get concept hierarchy
   */
  getConceptHierarchy(conceptId: string): ConceptHierarchy;

  /**
   * Get statistics
   */
  getStatistics(): AbstractionStatistics;

  /**
   * Reset statistics
   */
  resetStatistics(): void;

  /**
   * Serialize to JSON
   */
  toJSON(): string;

  /**
   * Deserialize from JSON
   */
  fromJSON(json: string): void;
}

// ============================================================================
// Default Implementation
// ============================================================================

/**
 * Default DomainAwareAbstractor implementation
 */
export class DefaultDomainAwareAbstractor implements DomainAwareAbstractor {
  private config: DomainAwareAbstractorConfig;
  private ontology: DomainOntology | undefined;
  private statistics: AbstractionStatistics;

  constructor(config?: Partial<DomainAwareAbstractorConfig>) {
    this.config = {
      strictMode: config?.strictMode ?? false,
      maxAbstractionDepth: config?.maxAbstractionDepth ?? 3,
      minMatchConfidence: config?.minMatchConfidence ?? 0.5,
    };

    this.statistics = {
      totalAbstractions: 0,
      ontologiesLoaded: 0,
      averageConfidence: 0,
    };
  }

  /**
   * Load domain ontology
   */
  loadOntology(ontology: DomainOntology): OntologyLoadResult {
    const warnings: string[] = [];

    // Validate ontology structure
    if (!ontology.name) {
      warnings.push('Ontology name is empty');
    }

    if (!ontology.concepts || ontology.concepts.length === 0) {
      warnings.push('Ontology has no concepts');
    }

    // Store ontology
    this.ontology = ontology;
    this.statistics.ontologiesLoaded++;

    return {
      success: true,
      warnings,
    };
  }

  /**
   * Get loaded ontology
   */
  getLoadedOntology(): DomainOntology | undefined {
    return this.ontology;
  }

  /**
   * Abstract pattern with domain context
   */
  async abstractWithDomain(
    pattern: LearnedPattern
  ): Promise<DomainAbstractionResult> {
    const domainConcepts: string[] = [];
    const constraints: DomainConstraint[] = [];
    const suggestions: string[] = [];
    let confidence = 0;

    if (this.ontology) {
      // Find matching concepts based on pattern name
      const matchedConcepts = this.matchPatternToConcepts(pattern);
      domainConcepts.push(...matchedConcepts.map((c) => c.id));

      // Find applicable constraints
      for (const concept of matchedConcepts) {
        const conceptConstraints = this.ontology.constraints.filter(
          (c) => c.concept === concept.id
        );
        constraints.push(...conceptConstraints);
      }

      // Calculate confidence
      confidence = matchedConcepts.length > 0 ? 0.8 : 0;

      // Generate suggestions
      if (matchedConcepts.length > 0) {
        suggestions.push(
          `Consider using domain terminology: ${matchedConcepts.map((c) => c.name).join(', ')}`
        );
      }
    }

    // Update statistics
    this.updateStatistics(confidence);

    return {
      pattern,
      domainConcepts,
      constraints,
      confidence,
      suggestions,
    };
  }

  /**
   * Abstract multiple patterns
   */
  async abstractBatch(
    patterns: LearnedPattern[]
  ): Promise<DomainAbstractionResult[]> {
    return Promise.all(
      patterns.map((pattern) => this.abstractWithDomain(pattern))
    );
  }

  /**
   * Match pattern to domain concepts
   */
  private matchPatternToConcepts(pattern: LearnedPattern): DomainConcept[] {
    if (!this.ontology) return [];

    const patternName = pattern.name.toLowerCase();
    const matched: DomainConcept[] = [];

    for (const concept of this.ontology.concepts) {
      // Check if pattern name contains concept name
      const conceptName = concept.name.toLowerCase();
      if (patternName.includes(conceptName)) {
        matched.push(concept);
        continue;
      }

      // Check if pattern name contains any property
      for (const prop of concept.properties) {
        if (patternName.includes(prop.toLowerCase())) {
          matched.push(concept);
          break;
        }
      }
    }

    return matched;
  }

  /**
   * Find related domain concepts
   */
  findRelatedConcepts(term: string): DomainConcept[] {
    if (!this.ontology) return [];

    const termLower = term.toLowerCase();
    const related: DomainConcept[] = [];

    for (const concept of this.ontology.concepts) {
      // Match by name
      if (concept.name.toLowerCase().includes(termLower)) {
        related.push(concept);
        continue;
      }

      // Match by property
      if (concept.properties.some((p) => p.toLowerCase().includes(termLower))) {
        related.push(concept);
      }
    }

    return related;
  }

  /**
   * Get concept hierarchy
   */
  getConceptHierarchy(conceptId: string): ConceptHierarchy {
    const concept = this.ontology?.concepts.find((c) => c.id === conceptId);

    if (!concept) {
      return {
        concept: {
          id: conceptId,
          name: 'Unknown',
          description: '',
          properties: [],
          relations: [],
        },
        related: [],
        depth: 0,
      };
    }

    // Find related concepts through relations
    const related: DomainConcept[] = [];
    for (const relation of concept.relations) {
      const relatedConcept = this.ontology?.concepts.find(
        (c) => c.id === relation.target
      );
      if (relatedConcept) {
        related.push(relatedConcept);
      }
    }

    return {
      concept,
      related,
      depth: 1,
    };
  }

  /**
   * Update statistics
   */
  private updateStatistics(confidence: number): void {
    const prevTotal = this.statistics.totalAbstractions;
    const prevAvg = this.statistics.averageConfidence;

    this.statistics.totalAbstractions++;
    this.statistics.averageConfidence =
      (prevAvg * prevTotal + confidence) / (prevTotal + 1);
  }

  /**
   * Get statistics
   */
  getStatistics(): AbstractionStatistics {
    return { ...this.statistics };
  }

  /**
   * Reset statistics
   */
  resetStatistics(): void {
    this.statistics = {
      totalAbstractions: 0,
      ontologiesLoaded: this.statistics.ontologiesLoaded,
      averageConfidence: 0,
    };
  }

  /**
   * Serialize to JSON
   */
  toJSON(): string {
    return JSON.stringify({
      config: this.config,
      ontology: this.ontology,
      statistics: this.statistics,
    });
  }

  /**
   * Deserialize from JSON
   */
  fromJSON(json: string): void {
    const data = JSON.parse(json);

    if (data.config) {
      this.config = { ...this.config, ...data.config };
    }

    if (data.ontology) {
      this.ontology = data.ontology;
    }

    if (data.statistics) {
      this.statistics = { ...this.statistics, ...data.statistics };
    }
  }
}

// ============================================================================
// Factory Function
// ============================================================================

/**
 * Create a DomainAwareAbstractor instance
 * @param config - Optional configuration
 * @returns DomainAwareAbstractor instance
 */
export function createDomainAwareAbstractor(
  config?: Partial<DomainAwareAbstractorConfig>
): DomainAwareAbstractor {
  return new DefaultDomainAwareAbstractor(config);
}
