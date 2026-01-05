/**
 * Context Analyzer - Related Entity Finder
 *
 * Analyzes context to find related entities with relevance scoring
 *
 * @module learning/inference/context-analyzer
 *
 * @see REQ-REC-001
 * @see TSK-REC-001
 */

import { EventEmitter } from 'events';

// ============================================================================
// Types
// ============================================================================

/**
 * Entity to analyze
 */
export interface AnalyzableEntity {
  /** Entity name */
  name: string;
  /** Entity type (class, function, interface, etc.) */
  type: string;
  /** Namespace */
  namespace: string;
  /** File path */
  filePath?: string;
  /** Tags/keywords */
  tags?: string[];
  /** Description */
  description?: string;
  /** Associated patterns */
  patterns?: string[];
  /** Metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Related entity with relevance score
 */
export interface RelatedEntity {
  /** Entity */
  entity: AnalyzableEntity;
  /** Relevance score (0-1) */
  relevanceScore: number;
  /** Score breakdown */
  scoreBreakdown: RelevanceScoreBreakdown;
  /** Relationship type */
  relationshipType: RelationshipType;
  /** Reason for relation */
  reason: string;
}

/**
 * Score breakdown by factor
 */
export interface RelevanceScoreBreakdown {
  /** Name similarity score (0-1) */
  nameSimilarity: number;
  /** Namespace affinity score (0-1) */
  namespaceAffinity: number;
  /** Type compatibility score (0-1) */
  typeCompatibility: number;
  /** Tag overlap score (0-1) */
  tagOverlap: number;
}

/**
 * Relationship type between entities
 */
export type RelationshipType =
  | 'same_namespace'
  | 'similar_name'
  | 'same_type'
  | 'shared_tags'
  | 'pattern_match'
  | 'dependency'
  | 'usage';

/**
 * Scoring weights configuration
 */
export interface ScoringWeights {
  /** Weight for name similarity (default: 0.3) */
  nameSimilarity: number;
  /** Weight for namespace affinity (default: 0.25) */
  namespaceAffinity: number;
  /** Weight for type compatibility (default: 0.25) */
  typeCompatibility: number;
  /** Weight for tag overlap (default: 0.2) */
  tagOverlap: number;
}

/**
 * Default scoring weights
 */
export const DEFAULT_SCORING_WEIGHTS: ScoringWeights = {
  nameSimilarity: 0.3,
  namespaceAffinity: 0.25,
  typeCompatibility: 0.25,
  tagOverlap: 0.2,
};

/**
 * Context analyzer options
 */
export interface ContextAnalyzerOptions {
  /** Scoring weights */
  weights?: Partial<ScoringWeights>;
  /** Minimum relevance score threshold (default: 0.1) */
  minScore?: number;
  /** Maximum results to return (default: 10) */
  maxResults?: number;
  /** Case-insensitive comparison (default: true) */
  caseInsensitive?: boolean;
}

/**
 * Entity repository interface
 */
export interface EntityRepository {
  /** Get all entities */
  getAllEntities(): Promise<AnalyzableEntity[]>;
  /** Get entities by namespace */
  getEntitiesByNamespace(namespace: string): Promise<AnalyzableEntity[]>;
  /** Get entities by type */
  getEntitiesByType(type: string): Promise<AnalyzableEntity[]>;
  /** Search entities by tags */
  searchByTags(tags: string[]): Promise<AnalyzableEntity[]>;
}

// ============================================================================
// Levenshtein Distance Implementation
// ============================================================================

/**
 * Calculate Levenshtein distance between two strings
 */
export function levenshteinDistance(a: string, b: string): number {
  if (a.length === 0) return b.length;
  if (b.length === 0) return a.length;

  const matrix: number[][] = [];

  // Initialize first column
  for (let i = 0; i <= b.length; i++) {
    matrix[i] = [i];
  }

  // Initialize first row
  for (let j = 0; j <= a.length; j++) {
    matrix[0][j] = j;
  }

  // Fill in the rest of the matrix
  for (let i = 1; i <= b.length; i++) {
    for (let j = 1; j <= a.length; j++) {
      if (b.charAt(i - 1) === a.charAt(j - 1)) {
        matrix[i][j] = matrix[i - 1][j - 1];
      } else {
        matrix[i][j] = Math.min(
          matrix[i - 1][j - 1] + 1, // substitution
          matrix[i][j - 1] + 1,     // insertion
          matrix[i - 1][j] + 1      // deletion
        );
      }
    }
  }

  return matrix[b.length][a.length];
}

/**
 * Calculate normalized Levenshtein similarity (0-1, higher is more similar)
 */
export function levenshteinSimilarity(a: string, b: string): number {
  if (a === b) return 1;
  if (a.length === 0 || b.length === 0) return 0;

  const distance = levenshteinDistance(a, b);
  const maxLength = Math.max(a.length, b.length);
  return 1 - distance / maxLength;
}

// ============================================================================
// Context Analyzer
// ============================================================================

/**
 * Context Analyzer events
 */
export interface ContextAnalyzerEvents {
  'analysis:started': { entity: AnalyzableEntity };
  'analysis:completed': { entity: AnalyzableEntity; resultsCount: number };
  'error': Error;
}

/**
 * Context Analyzer
 *
 * Finds related entities based on multiple relevance factors
 *
 * @example
 * ```typescript
 * const analyzer = new ContextAnalyzer({ repository });
 * const related = await analyzer.findRelatedEntities({
 *   name: 'UserService',
 *   type: 'class',
 *   namespace: 'services',
 * });
 * // Returns entities sorted by relevanceScore descending
 * ```
 */
export class ContextAnalyzer extends EventEmitter {
  private repository: EntityRepository | null = null;
  private entities: AnalyzableEntity[] = [];
  private weights: ScoringWeights;
  private minScore: number;
  private maxResults: number;
  private caseInsensitive: boolean;

  constructor(options: ContextAnalyzerOptions & { repository?: EntityRepository } = {}) {
    super();

    this.weights = { ...DEFAULT_SCORING_WEIGHTS, ...options.weights };
    this.minScore = options.minScore ?? 0.1;
    this.maxResults = options.maxResults ?? 10;
    this.caseInsensitive = options.caseInsensitive ?? true;
    this.repository = options.repository ?? null;
  }

  /**
   * Set entity repository
   */
  setRepository(repository: EntityRepository): void {
    this.repository = repository;
  }

  /**
   * Load entities from repository
   */
  async loadEntities(): Promise<void> {
    if (!this.repository) {
      throw new Error('Entity repository not set');
    }
    this.entities = await this.repository.getAllEntities();
  }

  /**
   * Add entities directly (for testing or in-memory use)
   */
  addEntities(entities: AnalyzableEntity[]): void {
    this.entities.push(...entities);
  }

  /**
   * Clear loaded entities
   */
  clearEntities(): void {
    this.entities = [];
  }

  /**
   * Get all loaded entities
   */
  getEntities(): AnalyzableEntity[] {
    return [...this.entities];
  }

  /**
   * Find related entities for a given entity
   */
  async findRelatedEntities(target: AnalyzableEntity): Promise<RelatedEntity[]> {
    this.emit('analysis:started', { entity: target });

    // Load entities if repository is set and entities are empty
    if (this.entities.length === 0 && this.repository) {
      await this.loadEntities();
    }

    const results: RelatedEntity[] = [];

    for (const entity of this.entities) {
      // Skip self
      if (this.isSameEntity(entity, target)) {
        continue;
      }

      const scoreBreakdown = this.calculateScoreBreakdown(target, entity);
      const relevanceScore = this.calculateWeightedScore(scoreBreakdown);

      // Skip if below threshold
      if (relevanceScore < this.minScore) {
        continue;
      }

      const relationshipType = this.determineRelationshipType(scoreBreakdown);
      const reason = this.generateReason(target, entity, scoreBreakdown, relationshipType);

      results.push({
        entity,
        relevanceScore,
        scoreBreakdown,
        relationshipType,
        reason,
      });
    }

    // Sort by relevance score descending
    results.sort((a, b) => b.relevanceScore - a.relevanceScore);

    // Limit results
    const limitedResults = results.slice(0, this.maxResults);

    this.emit('analysis:completed', { entity: target, resultsCount: limitedResults.length });

    return limitedResults;
  }

  /**
   * Find entities similar to a query string (name-based search)
   */
  async findSimilarByName(name: string, limit?: number): Promise<RelatedEntity[]> {
    const targetName = this.caseInsensitive ? name.toLowerCase() : name;

    const results: RelatedEntity[] = [];

    for (const entity of this.entities) {
      const entityName = this.caseInsensitive ? entity.name.toLowerCase() : entity.name;
      const nameSimilarity = levenshteinSimilarity(targetName, entityName);

      if (nameSimilarity < this.minScore) {
        continue;
      }

      results.push({
        entity,
        relevanceScore: nameSimilarity,
        scoreBreakdown: {
          nameSimilarity,
          namespaceAffinity: 0,
          typeCompatibility: 0,
          tagOverlap: 0,
        },
        relationshipType: 'similar_name',
        reason: `Name similarity: ${(nameSimilarity * 100).toFixed(1)}%`,
      });
    }

    results.sort((a, b) => b.relevanceScore - a.relevanceScore);
    return results.slice(0, limit ?? this.maxResults);
  }

  // ============================================================================
  // Scoring Methods
  // ============================================================================

  /**
   * Calculate score breakdown for all factors
   */
  private calculateScoreBreakdown(target: AnalyzableEntity, candidate: AnalyzableEntity): RelevanceScoreBreakdown {
    return {
      nameSimilarity: this.calculateNameSimilarity(target.name, candidate.name),
      namespaceAffinity: this.calculateNamespaceAffinity(target.namespace, candidate.namespace),
      typeCompatibility: this.calculateTypeCompatibility(target.type, candidate.type),
      tagOverlap: this.calculateTagOverlap(target.tags, candidate.tags),
    };
  }

  /**
   * Calculate weighted final score
   */
  private calculateWeightedScore(breakdown: RelevanceScoreBreakdown): number {
    return (
      breakdown.nameSimilarity * this.weights.nameSimilarity +
      breakdown.namespaceAffinity * this.weights.namespaceAffinity +
      breakdown.typeCompatibility * this.weights.typeCompatibility +
      breakdown.tagOverlap * this.weights.tagOverlap
    );
  }

  /**
   * Calculate name similarity using Levenshtein distance
   */
  private calculateNameSimilarity(name1: string, name2: string): number {
    const a = this.caseInsensitive ? name1.toLowerCase() : name1;
    const b = this.caseInsensitive ? name2.toLowerCase() : name2;
    return levenshteinSimilarity(a, b);
  }

  /**
   * Calculate namespace affinity
   * Same namespace = 1.0, parent/child = 0.7, sibling = 0.5, unrelated = 0
   */
  private calculateNamespaceAffinity(ns1: string, ns2: string): number {
    const a = this.caseInsensitive ? ns1.toLowerCase() : ns1;
    const b = this.caseInsensitive ? ns2.toLowerCase() : ns2;

    // Same namespace
    if (a === b) {
      return 1.0;
    }

    // Parent/child relationship
    if (a.startsWith(b + '.') || b.startsWith(a + '.')) {
      return 0.7;
    }

    // Sibling namespaces (share common parent)
    const aParts = a.split('.');
    const bParts = b.split('.');
    const minLength = Math.min(aParts.length, bParts.length);

    let commonPrefixLength = 0;
    for (let i = 0; i < minLength; i++) {
      if (aParts[i] === bParts[i]) {
        commonPrefixLength++;
      } else {
        break;
      }
    }

    if (commonPrefixLength > 0) {
      // Calculate affinity based on how much of the namespace is shared
      const totalParts = Math.max(aParts.length, bParts.length);
      return 0.5 * (commonPrefixLength / totalParts);
    }

    return 0;
  }

  /**
   * Calculate type compatibility
   * Same type = 1.0, related types = 0.5-0.8
   */
  private calculateTypeCompatibility(type1: string, type2: string): number {
    const a = this.caseInsensitive ? type1.toLowerCase() : type1;
    const b = this.caseInsensitive ? type2.toLowerCase() : type2;

    if (a === b) {
      return 1.0;
    }

    // Define related type groups
    const typeGroups: string[][] = [
      ['class', 'interface', 'type', 'abstract'],
      ['function', 'method', 'arrow', 'lambda'],
      ['const', 'let', 'var', 'property'],
      ['service', 'repository', 'controller', 'handler'],
      ['model', 'entity', 'dto', 'schema'],
      ['test', 'spec', 'mock', 'stub'],
    ];

    for (const group of typeGroups) {
      const aInGroup = group.includes(a);
      const bInGroup = group.includes(b);

      if (aInGroup && bInGroup) {
        return 0.7;
      }
    }

    return 0;
  }

  /**
   * Calculate tag overlap using Jaccard similarity
   */
  private calculateTagOverlap(tags1?: string[], tags2?: string[]): number {
    if (!tags1 || !tags2 || tags1.length === 0 || tags2.length === 0) {
      return 0;
    }

    const set1 = new Set(tags1.map((t) => (this.caseInsensitive ? t.toLowerCase() : t)));
    const set2 = new Set(tags2.map((t) => (this.caseInsensitive ? t.toLowerCase() : t)));

    const intersection = new Set([...set1].filter((x) => set2.has(x)));
    const union = new Set([...set1, ...set2]);

    return intersection.size / union.size;
  }

  // ============================================================================
  // Helper Methods
  // ============================================================================

  /**
   * Check if two entities are the same
   */
  private isSameEntity(a: AnalyzableEntity, b: AnalyzableEntity): boolean {
    return (
      a.name === b.name &&
      a.type === b.type &&
      a.namespace === b.namespace
    );
  }

  /**
   * Determine the primary relationship type based on score breakdown
   */
  private determineRelationshipType(breakdown: RelevanceScoreBreakdown): RelationshipType {
    const scores: Array<{ type: RelationshipType; score: number }> = [
      { type: 'same_namespace', score: breakdown.namespaceAffinity },
      { type: 'similar_name', score: breakdown.nameSimilarity },
      { type: 'same_type', score: breakdown.typeCompatibility },
      { type: 'shared_tags', score: breakdown.tagOverlap },
    ];

    scores.sort((a, b) => b.score - a.score);

    // Return the highest scoring relationship type (with threshold)
    const top = scores[0];
    if (top.score > 0.5) {
      return top.type;
    }

    return 'similar_name'; // Default
  }

  /**
   * Generate human-readable reason for the relationship
   */
  private generateReason(
    _target: AnalyzableEntity,
    candidate: AnalyzableEntity,
    breakdown: RelevanceScoreBreakdown,
    relationshipType: RelationshipType
  ): string {
    switch (relationshipType) {
      case 'same_namespace':
        return `In same namespace: ${candidate.namespace}`;
      case 'similar_name':
        return `Similar name: ${(breakdown.nameSimilarity * 100).toFixed(0)}% match`;
      case 'same_type':
        return `Same type: ${candidate.type}`;
      case 'shared_tags':
        return `Shared tags: ${(breakdown.tagOverlap * 100).toFixed(0)}% overlap`;
      default:
        return `Related by multiple factors`;
    }
  }

  /**
   * Update scoring weights
   */
  setWeights(weights: Partial<ScoringWeights>): void {
    this.weights = { ...this.weights, ...weights };
  }

  /**
   * Get current scoring weights
   */
  getWeights(): ScoringWeights {
    return { ...this.weights };
  }
}
