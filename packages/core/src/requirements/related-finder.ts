/**
 * Related Requirements Finder
 * 
 * Finds related requirements based on semantic similarity
 * 
 * @packageDocumentation
 * @module requirements/related-finder
 * 
 * @see REQ-RA-003 - Related Requirements Finding
 * @see Article III - Traceability
 */

/**
 * Similarity algorithm
 */
export type SimilarityAlgorithm = 'cosine' | 'jaccard' | 'levenshtein' | 'tfidf' | 'semantic';

/**
 * Relationship type
 */
export type RelationshipType = 
  | 'derives'      // A derives from B
  | 'refines'      // A refines B
  | 'conflicts'    // A conflicts with B
  | 'depends'      // A depends on B
  | 'similar'      // A is similar to B
  | 'parent'       // A is parent of B
  | 'child'        // A is child of B
  | 'implements'   // A implements B
  | 'verifies'     // A verifies B
  | 'traces';      // A traces to B

/**
 * Requirement for analysis
 */
export interface AnalyzableRequirement {
  /** Requirement ID */
  id: string;
  /** Title */
  title: string;
  /** Description/content */
  description: string;
  /** Type (functional, non-functional, etc.) */
  type?: string;
  /** Priority */
  priority?: string;
  /** Tags/keywords */
  tags?: string[];
  /** Category */
  category?: string;
  /** Parent requirement */
  parent?: string;
  /** Metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Related requirement result
 */
export interface RelatedRequirement {
  /** Requirement ID */
  id: string;
  /** Requirement title */
  title: string;
  /** Relationship type */
  relationshipType: RelationshipType;
  /** Similarity score (0-1) */
  similarity: number;
  /** Reason for relationship */
  reason: string;
  /** Shared terms */
  sharedTerms: string[];
  /** Confidence (0-1) */
  confidence: number;
}

/**
 * Search result
 */
export interface SearchResult {
  /** Source requirement ID */
  sourceId: string;
  /** Related requirements */
  related: RelatedRequirement[];
  /** Search time (ms) */
  searchTime: number;
  /** Algorithm used */
  algorithm: SimilarityAlgorithm;
  /** Total candidates analyzed */
  candidatesAnalyzed: number;
}

/**
 * Requirement cluster
 */
export interface RequirementCluster {
  /** Cluster ID */
  id: string;
  /** Cluster name/theme */
  name: string;
  /** Requirements in cluster */
  requirements: string[];
  /** Central requirement */
  centroid: string;
  /** Cohesion score */
  cohesion: number;
  /** Key terms */
  keyTerms: string[];
}

/**
 * Related finder config
 */
export interface RelatedFinderConfig {
  /** Default algorithm */
  algorithm: SimilarityAlgorithm;
  /** Minimum similarity threshold */
  minSimilarity: number;
  /** Maximum results */
  maxResults: number;
  /** Include relationship inference */
  inferRelationships: boolean;
  /** Stop words to ignore */
  stopWords: string[];
  /** Domain-specific synonyms */
  synonyms: Map<string, string[]>;
  /** Weight for title matching */
  titleWeight: number;
  /** Weight for description matching */
  descriptionWeight: number;
  /** Weight for tag matching */
  tagWeight: number;
}

/**
 * Default configuration
 */
export const DEFAULT_FINDER_CONFIG: RelatedFinderConfig = {
  algorithm: 'tfidf',
  minSimilarity: 0.3,
  maxResults: 10,
  inferRelationships: true,
  stopWords: [
    'the', 'a', 'an', 'and', 'or', 'but', 'in', 'on', 'at', 'to', 'for',
    'of', 'with', 'by', 'from', 'as', 'is', 'was', 'are', 'were', 'been',
    'be', 'have', 'has', 'had', 'do', 'does', 'did', 'will', 'would',
    'could', 'should', 'may', 'might', 'must', 'shall', 'can', 'need',
    'this', 'that', 'these', 'those', 'it', 'its', 'they', 'their',
    'when', 'where', 'which', 'who', 'what', 'how', 'why',
    'system', 'shall', 'must', 'should', 'requirement', 'requirements',
  ],
  synonyms: new Map([
    ['user', ['customer', 'client', 'end-user', 'operator']],
    ['display', ['show', 'present', 'render', 'visualize']],
    ['store', ['save', 'persist', 'record', 'keep']],
    ['retrieve', ['fetch', 'get', 'load', 'read']],
    ['authenticate', ['login', 'sign-in', 'verify-identity']],
    ['authorize', ['permit', 'allow', 'grant-access']],
    ['validate', ['verify', 'check', 'confirm']],
    ['error', ['failure', 'exception', 'fault']],
    ['performance', ['speed', 'efficiency', 'responsiveness']],
    ['security', ['protection', 'safety', 'secure']],
  ]),
  titleWeight: 2.0,
  descriptionWeight: 1.0,
  tagWeight: 1.5,
};

/**
 * Term frequency document
 */
interface TFDocument {
  id: string;
  terms: Map<string, number>;
  magnitude: number;
}

/**
 * Related Requirements Finder
 */
export class RelatedRequirementsFinder {
  private config: RelatedFinderConfig;
  private requirements: Map<string, AnalyzableRequirement>;
  private tfDocuments: Map<string, TFDocument>;
  private idfScores: Map<string, number>;
  private documentCount = 0;

  constructor(config?: Partial<RelatedFinderConfig>) {
    this.config = { ...DEFAULT_FINDER_CONFIG, ...config };
    this.requirements = new Map();
    this.tfDocuments = new Map();
    this.idfScores = new Map();
  }

  /**
   * Add requirements to the index
   */
  index(requirements: AnalyzableRequirement[]): void {
    for (const req of requirements) {
      this.requirements.set(req.id, req);
    }
    this.buildIndex();
  }

  /**
   * Add a single requirement
   */
  add(requirement: AnalyzableRequirement): void {
    this.requirements.set(requirement.id, requirement);
    this.buildIndex();
  }

  /**
   * Remove a requirement
   */
  remove(id: string): void {
    this.requirements.delete(id);
    this.tfDocuments.delete(id);
    this.buildIndex();
  }

  /**
   * Find related requirements
   */
  findRelated(
    requirementId: string,
    options?: {
      algorithm?: SimilarityAlgorithm;
      minSimilarity?: number;
      maxResults?: number;
      relationshipTypes?: RelationshipType[];
    }
  ): SearchResult {
    const startTime = Date.now();
    const source = this.requirements.get(requirementId);

    if (!source) {
      return {
        sourceId: requirementId,
        related: [],
        searchTime: Date.now() - startTime,
        algorithm: options?.algorithm ?? this.config.algorithm,
        candidatesAnalyzed: 0,
      };
    }

    const algorithm = options?.algorithm ?? this.config.algorithm;
    const minSimilarity = options?.minSimilarity ?? this.config.minSimilarity;
    const maxResults = options?.maxResults ?? this.config.maxResults;

    const candidates: RelatedRequirement[] = [];

    for (const [id, candidate] of this.requirements) {
      if (id === requirementId) continue;

      const similarity = this.calculateSimilarity(source, candidate, algorithm);
      
      if (similarity >= minSimilarity) {
        const relationship = this.inferRelationship(source, candidate, similarity);
        const sharedTerms = this.findSharedTerms(source, candidate);

        candidates.push({
          id: candidate.id,
          title: candidate.title,
          relationshipType: relationship.type,
          similarity,
          reason: relationship.reason,
          sharedTerms,
          confidence: relationship.confidence,
        });
      }
    }

    // Sort by similarity
    candidates.sort((a, b) => b.similarity - a.similarity);

    // Filter by relationship type if specified
    let results = candidates;
    if (options?.relationshipTypes?.length) {
      results = candidates.filter((r) =>
        options.relationshipTypes!.includes(r.relationshipType)
      );
    }

    return {
      sourceId: requirementId,
      related: results.slice(0, maxResults),
      searchTime: Date.now() - startTime,
      algorithm,
      candidatesAnalyzed: this.requirements.size - 1,
    };
  }

  /**
   * Find requirements similar to text
   */
  findByText(
    text: string,
    options?: {
      algorithm?: SimilarityAlgorithm;
      minSimilarity?: number;
      maxResults?: number;
    }
  ): RelatedRequirement[] {
    const virtualReq: AnalyzableRequirement = {
      id: '__search__',
      title: text,
      description: text,
    };

    const algorithm = options?.algorithm ?? this.config.algorithm;
    const minSimilarity = options?.minSimilarity ?? this.config.minSimilarity;
    const maxResults = options?.maxResults ?? this.config.maxResults;

    const results: RelatedRequirement[] = [];

    for (const [_id, candidate] of this.requirements) {
      const similarity = this.calculateSimilarity(virtualReq, candidate, algorithm);
      
      if (similarity >= minSimilarity) {
        const sharedTerms = this.findSharedTerms(virtualReq, candidate);

        results.push({
          id: candidate.id,
          title: candidate.title,
          relationshipType: 'similar',
          similarity,
          reason: `Matches search terms: ${sharedTerms.slice(0, 5).join(', ')}`,
          sharedTerms,
          confidence: similarity,
        });
      }
    }

    results.sort((a, b) => b.similarity - a.similarity);
    return results.slice(0, maxResults);
  }

  /**
   * Cluster requirements by similarity
   */
  cluster(options?: { threshold?: number; minClusterSize?: number }): RequirementCluster[] {
    const threshold = options?.threshold ?? 0.5;
    const minSize = options?.minClusterSize ?? 2;

    const clusters: RequirementCluster[] = [];
    const assigned = new Set<string>();
    let clusterId = 0;

    // Simple agglomerative clustering
    for (const [id, req] of this.requirements) {
      if (assigned.has(id)) continue;

      const clusterMembers = [id];
      assigned.add(id);

      // Find similar requirements
      for (const [otherId, otherReq] of this.requirements) {
        if (assigned.has(otherId)) continue;

        const similarity = this.calculateSimilarity(req, otherReq, this.config.algorithm);
        if (similarity >= threshold) {
          clusterMembers.push(otherId);
          assigned.add(otherId);
        }
      }

      if (clusterMembers.length >= minSize) {
        const keyTerms = this.extractClusterTerms(clusterMembers);
        const cohesion = this.calculateClusterCohesion(clusterMembers);

        clusters.push({
          id: `cluster-${++clusterId}`,
          name: keyTerms.slice(0, 3).join(', '),
          requirements: clusterMembers,
          centroid: clusterMembers[0],
          cohesion,
          keyTerms,
        });
      }
    }

    return clusters;
  }

  /**
   * Find gaps in requirement coverage
   */
  findGaps(): {
    orphanRequirements: string[];
    weaklyConnected: string[];
    missingRelationships: Array<{ from: string; to: string; suggestedType: RelationshipType }>;
  } {
    const connectionCounts = new Map<string, number>();
    const missingRelationships: Array<{ from: string; to: string; suggestedType: RelationshipType }> = [];

    // Count connections for each requirement
    for (const [id] of this.requirements) {
      const related = this.findRelated(id, { minSimilarity: 0.4, maxResults: 20 });
      connectionCounts.set(id, related.related.length);

      // Find potential missing relationships
      for (const rel of related.related) {
        if (rel.similarity >= 0.7 && rel.confidence >= 0.8) {
          if (!this.hasExplicitRelationship(id, rel.id)) {
            missingRelationships.push({
              from: id,
              to: rel.id,
              suggestedType: rel.relationshipType,
            });
          }
        }
      }
    }

    const orphans: string[] = [];
    const weaklyConnected: string[] = [];

    for (const [id, count] of connectionCounts) {
      if (count === 0) {
        orphans.push(id);
      } else if (count <= 2) {
        weaklyConnected.push(id);
      }
    }

    return {
      orphanRequirements: orphans,
      weaklyConnected,
      missingRelationships,
    };
  }

  /**
   * Get requirement by ID
   */
  get(id: string): AnalyzableRequirement | undefined {
    return this.requirements.get(id);
  }

  /**
   * Get all requirements
   */
  getAll(): AnalyzableRequirement[] {
    return [...this.requirements.values()];
  }

  /**
   * Get statistics
   */
  getStatistics(): {
    totalRequirements: number;
    avgSimilarity: number;
    termCount: number;
    clusterCount: number;
  } {
    const clusters = this.cluster();
    
    let totalSimilarity = 0;
    let pairCount = 0;

    const reqs = [...this.requirements.values()];
    for (let i = 0; i < reqs.length; i++) {
      for (let j = i + 1; j < reqs.length; j++) {
        totalSimilarity += this.calculateSimilarity(
          reqs[i], reqs[j], this.config.algorithm
        );
        pairCount++;
      }
    }

    return {
      totalRequirements: this.requirements.size,
      avgSimilarity: pairCount > 0 ? totalSimilarity / pairCount : 0,
      termCount: this.idfScores.size,
      clusterCount: clusters.length,
    };
  }

  /**
   * Build TF-IDF index
   */
  private buildIndex(): void {
    this.tfDocuments.clear();
    this.idfScores.clear();
    this.documentCount = this.requirements.size;

    const documentFrequency = new Map<string, number>();

    // Calculate term frequencies
    for (const [id, req] of this.requirements) {
      const terms = this.tokenize(req);
      const termFreq = new Map<string, number>();

      for (const term of terms) {
        termFreq.set(term, (termFreq.get(term) ?? 0) + 1);
      }

      // Calculate magnitude for cosine similarity
      let magnitude = 0;
      for (const freq of termFreq.values()) {
        magnitude += freq * freq;
      }

      this.tfDocuments.set(id, {
        id,
        terms: termFreq,
        magnitude: Math.sqrt(magnitude),
      });

      // Update document frequency
      for (const term of termFreq.keys()) {
        documentFrequency.set(term, (documentFrequency.get(term) ?? 0) + 1);
      }
    }

    // Calculate IDF scores
    for (const [term, df] of documentFrequency) {
      this.idfScores.set(term, Math.log(this.documentCount / df));
    }
  }

  /**
   * Tokenize a requirement
   */
  private tokenize(req: AnalyzableRequirement): string[] {
    const text = [
      ...Array(Math.ceil(this.config.titleWeight)).fill(req.title),
      ...Array(Math.ceil(this.config.descriptionWeight)).fill(req.description),
      ...(req.tags ?? []).flatMap((t) =>
        Array(Math.ceil(this.config.tagWeight)).fill(t)
      ),
    ].join(' ');

    // Tokenize and normalize
    const tokens = text
      .toLowerCase()
      .replace(/[^a-z0-9\s-]/g, ' ')
      .split(/\s+/)
      .filter((t) => t.length > 2)
      .filter((t) => !this.config.stopWords.includes(t));

    // Expand synonyms
    const expanded: string[] = [];
    for (const token of tokens) {
      expanded.push(token);
      for (const [key, synonyms] of this.config.synonyms) {
        if (token === key || synonyms.includes(token)) {
          expanded.push(key);
        }
      }
    }

    return expanded;
  }

  /**
   * Calculate similarity between two requirements
   */
  private calculateSimilarity(
    a: AnalyzableRequirement,
    b: AnalyzableRequirement,
    algorithm: SimilarityAlgorithm
  ): number {
    switch (algorithm) {
      case 'cosine':
        return this.cosineSimilarity(a, b);
      case 'jaccard':
        return this.jaccardSimilarity(a, b);
      case 'levenshtein':
        return this.levenshteinSimilarity(a, b);
      case 'tfidf':
        return this.tfidfSimilarity(a, b);
      case 'semantic':
        // Fall back to TF-IDF for now (would use embeddings in production)
        return this.tfidfSimilarity(a, b);
      default:
        return this.tfidfSimilarity(a, b);
    }
  }

  /**
   * Cosine similarity
   */
  private cosineSimilarity(a: AnalyzableRequirement, b: AnalyzableRequirement): number {
    const docA = this.tfDocuments.get(a.id);
    const docB = this.tfDocuments.get(b.id);

    if (!docA || !docB) {
      // Calculate on the fly for virtual documents
      const termsA = this.tokenize(a);
      const termsB = this.tokenize(b);
      return this.calculateCosineDirect(termsA, termsB);
    }

    let dotProduct = 0;
    for (const [term, freqA] of docA.terms) {
      const freqB = docB.terms.get(term);
      if (freqB) {
        dotProduct += freqA * freqB;
      }
    }

    if (docA.magnitude === 0 || docB.magnitude === 0) return 0;
    return dotProduct / (docA.magnitude * docB.magnitude);
  }

  /**
   * Calculate cosine similarity directly from terms
   */
  private calculateCosineDirect(termsA: string[], termsB: string[]): number {
    const freqA = new Map<string, number>();
    const freqB = new Map<string, number>();

    for (const t of termsA) freqA.set(t, (freqA.get(t) ?? 0) + 1);
    for (const t of termsB) freqB.set(t, (freqB.get(t) ?? 0) + 1);

    let dotProduct = 0;
    let magA = 0;
    let magB = 0;

    for (const [term, freq] of freqA) {
      magA += freq * freq;
      const fb = freqB.get(term);
      if (fb) dotProduct += freq * fb;
    }
    for (const freq of freqB.values()) {
      magB += freq * freq;
    }

    if (magA === 0 || magB === 0) return 0;
    return dotProduct / (Math.sqrt(magA) * Math.sqrt(magB));
  }

  /**
   * Jaccard similarity
   */
  private jaccardSimilarity(a: AnalyzableRequirement, b: AnalyzableRequirement): number {
    const termsA = new Set(this.tokenize(a));
    const termsB = new Set(this.tokenize(b));

    const intersection = new Set([...termsA].filter((t) => termsB.has(t)));
    const union = new Set([...termsA, ...termsB]);

    if (union.size === 0) return 0;
    return intersection.size / union.size;
  }

  /**
   * Levenshtein similarity
   */
  private levenshteinSimilarity(a: AnalyzableRequirement, b: AnalyzableRequirement): number {
    const textA = `${a.title} ${a.description}`.toLowerCase();
    const textB = `${b.title} ${b.description}`.toLowerCase();

    const distance = this.levenshteinDistance(textA, textB);
    const maxLen = Math.max(textA.length, textB.length);

    if (maxLen === 0) return 1;
    return 1 - distance / maxLen;
  }

  /**
   * Calculate Levenshtein distance
   */
  private levenshteinDistance(a: string, b: string): number {
    if (a.length === 0) return b.length;
    if (b.length === 0) return a.length;

    // Limit for performance
    if (a.length > 500 || b.length > 500) {
      return Math.abs(a.length - b.length);
    }

    const matrix: number[][] = [];

    for (let i = 0; i <= b.length; i++) {
      matrix[i] = [i];
    }
    for (let j = 0; j <= a.length; j++) {
      matrix[0][j] = j;
    }

    for (let i = 1; i <= b.length; i++) {
      for (let j = 1; j <= a.length; j++) {
        if (b.charAt(i - 1) === a.charAt(j - 1)) {
          matrix[i][j] = matrix[i - 1][j - 1];
        } else {
          matrix[i][j] = Math.min(
            matrix[i - 1][j - 1] + 1,
            matrix[i][j - 1] + 1,
            matrix[i - 1][j] + 1
          );
        }
      }
    }

    return matrix[b.length][a.length];
  }

  /**
   * TF-IDF similarity
   */
  private tfidfSimilarity(a: AnalyzableRequirement, b: AnalyzableRequirement): number {
    const termsA = this.tokenize(a);
    const termsB = this.tokenize(b);

    const tfidfA = this.calculateTFIDF(termsA);
    const tfidfB = this.calculateTFIDF(termsB);

    let dotProduct = 0;
    let magA = 0;
    let magB = 0;

    for (const [term, scoreA] of tfidfA) {
      magA += scoreA * scoreA;
      const scoreB = tfidfB.get(term);
      if (scoreB) dotProduct += scoreA * scoreB;
    }
    for (const scoreB of tfidfB.values()) {
      magB += scoreB * scoreB;
    }

    if (magA === 0 || magB === 0) return 0;
    return dotProduct / (Math.sqrt(magA) * Math.sqrt(magB));
  }

  /**
   * Calculate TF-IDF scores for terms
   */
  private calculateTFIDF(terms: string[]): Map<string, number> {
    const tf = new Map<string, number>();
    for (const term of terms) {
      tf.set(term, (tf.get(term) ?? 0) + 1);
    }

    const tfidf = new Map<string, number>();
    for (const [term, freq] of tf) {
      const idf = this.idfScores.get(term) ?? Math.log(this.documentCount + 1);
      tfidf.set(term, freq * idf);
    }

    return tfidf;
  }

  /**
   * Infer relationship between requirements
   */
  private inferRelationship(
    source: AnalyzableRequirement,
    target: AnalyzableRequirement,
    similarity: number
  ): { type: RelationshipType; reason: string; confidence: number } {
    if (!this.config.inferRelationships) {
      return { type: 'similar', reason: 'Similarity match', confidence: similarity };
    }

    // Check for parent-child relationship
    if (target.parent === source.id) {
      return { type: 'parent', reason: 'Explicit parent relationship', confidence: 1 };
    }
    if (source.parent === target.id) {
      return { type: 'child', reason: 'Explicit child relationship', confidence: 1 };
    }

    // Check for derives/refines based on content
    const sourceLower = source.description.toLowerCase();

    if (sourceLower.includes('derived from') || sourceLower.includes('based on')) {
      if (similarity > 0.5) {
        return { type: 'derives', reason: 'Content indicates derivation', confidence: 0.8 };
      }
    }

    if (sourceLower.includes('refines') || sourceLower.includes('elaborates')) {
      if (similarity > 0.6) {
        return { type: 'refines', reason: 'Content indicates refinement', confidence: 0.8 };
      }
    }

    // Check for conflicts
    const conflictIndicators = ['instead of', 'rather than', 'not', 'unlike', 'contrary'];
    for (const indicator of conflictIndicators) {
      if (sourceLower.includes(indicator) && similarity > 0.4) {
        return { type: 'conflicts', reason: `Potential conflict: "${indicator}"`, confidence: 0.6 };
      }
    }

    // Check for dependencies
    const dependencyIndicators = ['requires', 'depends on', 'needs', 'prerequisite'];
    for (const indicator of dependencyIndicators) {
      if (sourceLower.includes(indicator)) {
        return { type: 'depends', reason: `Dependency indicator: "${indicator}"`, confidence: 0.7 };
      }
    }

    // Check for implementation relationship
    if (source.type === 'design' && target.type === 'functional') {
      return { type: 'implements', reason: 'Design implements functional requirement', confidence: 0.7 };
    }

    // Check for verification relationship
    if (source.type === 'test' || source.category === 'verification') {
      return { type: 'verifies', reason: 'Test/verification requirement', confidence: 0.8 };
    }

    // Default to similar
    return { type: 'similar', reason: 'Content similarity', confidence: similarity };
  }

  /**
   * Find shared terms between requirements
   */
  private findSharedTerms(a: AnalyzableRequirement, b: AnalyzableRequirement): string[] {
    const termsA = new Set(this.tokenize(a));
    const termsB = new Set(this.tokenize(b));

    const shared = [...termsA].filter((t) => termsB.has(t));
    
    // Sort by IDF (more important terms first)
    shared.sort((x, y) => {
      const idfX = this.idfScores.get(x) ?? 0;
      const idfY = this.idfScores.get(y) ?? 0;
      return idfY - idfX;
    });

    return shared.slice(0, 10);
  }

  /**
   * Check if explicit relationship exists
   */
  private hasExplicitRelationship(_sourceId: string, _targetId: string): boolean {
    // Would check against explicit relationship data
    return false;
  }

  /**
   * Extract key terms from cluster
   */
  private extractClusterTerms(memberIds: string[]): string[] {
    const termCounts = new Map<string, number>();

    for (const id of memberIds) {
      const req = this.requirements.get(id);
      if (!req) continue;

      const terms = this.tokenize(req);
      for (const term of new Set(terms)) {
        termCounts.set(term, (termCounts.get(term) ?? 0) + 1);
      }
    }

    // Sort by frequency * IDF
    const scored = [...termCounts.entries()].map(([term, count]) => ({
      term,
      score: count * (this.idfScores.get(term) ?? 1),
    }));

    scored.sort((a, b) => b.score - a.score);
    return scored.slice(0, 10).map((s) => s.term);
  }

  /**
   * Calculate cluster cohesion
   */
  private calculateClusterCohesion(memberIds: string[]): number {
    if (memberIds.length <= 1) return 1;

    let totalSimilarity = 0;
    let pairCount = 0;

    for (let i = 0; i < memberIds.length; i++) {
      const reqA = this.requirements.get(memberIds[i]);
      if (!reqA) continue;

      for (let j = i + 1; j < memberIds.length; j++) {
        const reqB = this.requirements.get(memberIds[j]);
        if (!reqB) continue;

        totalSimilarity += this.calculateSimilarity(reqA, reqB, this.config.algorithm);
        pairCount++;
      }
    }

    return pairCount > 0 ? totalSimilarity / pairCount : 0;
  }
}

/**
 * Create related requirements finder instance
 */
export function createRelatedRequirementsFinder(
  config?: Partial<RelatedFinderConfig>
): RelatedRequirementsFinder {
  return new RelatedRequirementsFinder(config);
}
