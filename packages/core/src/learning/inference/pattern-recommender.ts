/**
 * Pattern Recommender - Context-based Pattern Recommendation
 *
 * Recommends patterns based on context with feedback learning
 *
 * @module learning/inference/pattern-recommender
 *
 * @see REQ-REC-002
 * @see TSK-REC-002
 */

import { EventEmitter } from 'events';
import type { AnalyzableEntity } from './context-analyzer.js';

// ============================================================================
// Types
// ============================================================================

/**
 * Pattern definition
 */
export interface RecommendablePattern {
  /** Pattern ID */
  id: string;
  /** Pattern name */
  name: string;
  /** Description */
  description: string;
  /** Pattern category */
  category: PatternCategory;
  /** Code template */
  template: string;
  /** Tags/keywords */
  tags: string[];
  /** Applicable entity types */
  applicableTypes: string[];
  /** Applicable namespaces (patterns) */
  applicableNamespaces?: string[];
  /** Base confidence (0-1) */
  baseConfidence: number;
  /** Usage count */
  usageCount: number;
  /** Positive feedback count */
  positiveCount: number;
  /** Negative feedback count */
  negativeCount: number;
  /** Last used timestamp */
  lastUsed?: Date;
  /** Created timestamp */
  createdAt: Date;
  /** Metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Pattern category
 */
export type PatternCategory =
  | 'architecture'
  | 'design-pattern'
  | 'testing'
  | 'error-handling'
  | 'validation'
  | 'logging'
  | 'caching'
  | 'async'
  | 'configuration'
  | 'api-design'
  | 'data-access'
  | 'security';

/**
 * Recommendation context
 */
export interface RecommendationContext {
  /** Current entity being worked on */
  currentEntity?: AnalyzableEntity;
  /** File path context */
  filePath?: string;
  /** Code snippet context */
  codeSnippet?: string;
  /** Task description */
  taskDescription?: string;
  /** Tags/keywords */
  tags?: string[];
  /** Previous recommendations (to avoid duplication) */
  previousRecommendations?: string[];
  /** User preferences */
  preferences?: {
    preferredCategories?: PatternCategory[];
    excludedCategories?: PatternCategory[];
    minConfidence?: number;
  };
}

/**
 * Pattern recommendation
 */
export interface PatternRecommendation {
  /** Pattern */
  pattern: RecommendablePattern;
  /** Confidence score (0-1) */
  confidence: number;
  /** Reason for recommendation */
  reason: string;
  /** Match factors */
  matchFactors: MatchFactor[];
}

/**
 * Match factor explaining why a pattern was recommended
 */
export interface MatchFactor {
  /** Factor name */
  factor: string;
  /** Factor score (0-1) */
  score: number;
  /** Description */
  description: string;
}

/**
 * Feedback type
 */
export type FeedbackType = 'accepted' | 'rejected' | 'modified' | 'ignored';

/**
 * Feedback record
 */
export interface PatternFeedback {
  /** Feedback ID */
  id: string;
  /** Pattern ID */
  patternId: string;
  /** Feedback type */
  type: FeedbackType;
  /** Context when feedback was given */
  context?: RecommendationContext;
  /** User comment */
  comment?: string;
  /** Timestamp */
  timestamp: Date;
}

/**
 * Pattern recommender options
 */
export interface PatternRecommenderOptions {
  /** Maximum recommendations to return (default: 5) */
  maxRecommendations?: number;
  /** Minimum confidence threshold (default: 0.3) */
  minConfidence?: number;
  /** Learning rate for feedback (default: 0.1) */
  learningRate?: number;
  /** Decay factor for unused patterns (default: 0.99) */
  decayFactor?: number;
}

/**
 * Pattern repository interface
 */
export interface PatternRepository {
  /** Get all patterns */
  getAllPatterns(): Promise<RecommendablePattern[]>;
  /** Get pattern by ID */
  getPattern(id: string): Promise<RecommendablePattern | null>;
  /** Update pattern */
  updatePattern(pattern: RecommendablePattern): Promise<void>;
  /** Record feedback */
  recordFeedback(feedback: PatternFeedback): Promise<void>;
}

// ============================================================================
// Pattern Recommender
// ============================================================================

/**
 * Pattern recommender events
 */
export interface PatternRecommenderEvents {
  'recommendation:generated': { context: RecommendationContext; count: number };
  'feedback:recorded': { feedback: PatternFeedback };
  'pattern:updated': { patternId: string };
  'error': Error;
}

/**
 * Pattern Recommender
 *
 * Recommends patterns based on context with feedback learning
 *
 * @example
 * ```typescript
 * const recommender = new PatternRecommender();
 * recommender.addPatterns([...patterns]);
 *
 * const recommendations = await recommender.recommend({
 *   currentEntity: { name: 'UserService', type: 'class', namespace: 'services' },
 * });
 * // Returns up to 5 recommendations sorted by confidence descending
 *
 * await recommender.recordFeedback('pattern-1', 'accepted', context);
 * ```
 */
export class PatternRecommender extends EventEmitter {
  private patterns: Map<string, RecommendablePattern> = new Map();
  private feedbackHistory: PatternFeedback[] = [];
  private repository: PatternRepository | null = null;

  private maxRecommendations: number;
  private minConfidence: number;
  private learningRate: number;
  private decayFactor: number;
  private feedbackIdCounter = 0;

  constructor(options: PatternRecommenderOptions = {}) {
    super();

    this.maxRecommendations = options.maxRecommendations ?? 5;
    this.minConfidence = options.minConfidence ?? 0.3;
    this.learningRate = options.learningRate ?? 0.1;
    this.decayFactor = options.decayFactor ?? 0.99;
  }

  /**
   * Set pattern repository
   */
  setRepository(repository: PatternRepository): void {
    this.repository = repository;
  }

  /**
   * Load patterns from repository
   */
  async loadPatterns(): Promise<void> {
    if (!this.repository) {
      throw new Error('Pattern repository not set');
    }
    const patterns = await this.repository.getAllPatterns();
    this.patterns.clear();
    for (const pattern of patterns) {
      this.patterns.set(pattern.id, pattern);
    }
  }

  /**
   * Add patterns directly (for testing or in-memory use)
   */
  addPatterns(patterns: RecommendablePattern[]): void {
    for (const pattern of patterns) {
      this.patterns.set(pattern.id, pattern);
    }
  }

  /**
   * Clear all patterns
   */
  clearPatterns(): void {
    this.patterns.clear();
  }

  /**
   * Get all patterns
   */
  getPatterns(): RecommendablePattern[] {
    return Array.from(this.patterns.values());
  }

  /**
   * Get pattern by ID
   */
  getPattern(id: string): RecommendablePattern | undefined {
    return this.patterns.get(id);
  }

  // ============================================================================
  // Recommendation
  // ============================================================================

  /**
   * Recommend patterns based on context
   */
  async recommend(context: RecommendationContext): Promise<PatternRecommendation[]> {
    // Load from repository if needed
    if (this.patterns.size === 0 && this.repository) {
      await this.loadPatterns();
    }

    const recommendations: PatternRecommendation[] = [];
    const minConfidence = context.preferences?.minConfidence ?? this.minConfidence;
    const excludedPatterns = new Set(context.previousRecommendations ?? []);

    for (const pattern of this.patterns.values()) {
      // Skip previously recommended patterns
      if (excludedPatterns.has(pattern.id)) {
        continue;
      }

      // Skip excluded categories
      if (context.preferences?.excludedCategories?.includes(pattern.category)) {
        continue;
      }

      // Calculate confidence
      const { confidence, matchFactors } = this.calculateConfidence(pattern, context);

      // Skip if below threshold
      if (confidence < minConfidence) {
        continue;
      }

      recommendations.push({
        pattern,
        confidence,
        reason: this.generateReason(matchFactors),
        matchFactors,
      });
    }

    // Sort by confidence descending
    recommendations.sort((a, b) => b.confidence - a.confidence);

    // Limit results
    const limitedResults = recommendations.slice(0, this.maxRecommendations);

    this.emit('recommendation:generated', { context, count: limitedResults.length });

    return limitedResults;
  }

  /**
   * Calculate confidence score for a pattern
   */
  private calculateConfidence(
    pattern: RecommendablePattern,
    context: RecommendationContext
  ): { confidence: number; matchFactors: MatchFactor[] } {
    const matchFactors: MatchFactor[] = [];
    let totalScore = 0;
    let totalWeight = 0;

    // Factor 1: Entity type match (weight: 0.25)
    if (context.currentEntity) {
      const typeMatch = this.calculateTypeMatch(pattern, context.currentEntity.type);
      matchFactors.push({
        factor: 'entityType',
        score: typeMatch,
        description: typeMatch > 0.5 
          ? `Applicable to ${context.currentEntity.type}` 
          : 'Type mismatch',
      });
      totalScore += typeMatch * 0.25;
      totalWeight += 0.25;
    }

    // Factor 2: Tag overlap (weight: 0.25)
    const tagOverlap = this.calculateTagOverlap(pattern.tags, context.tags);
    if (context.tags && context.tags.length > 0) {
      matchFactors.push({
        factor: 'tagOverlap',
        score: tagOverlap,
        description: tagOverlap > 0.5 
          ? `Matching tags` 
          : 'Few matching tags',
      });
      totalScore += tagOverlap * 0.25;
      totalWeight += 0.25;
    }

    // Factor 3: Category preference (weight: 0.15)
    const categoryBonus = context.preferences?.preferredCategories?.includes(pattern.category) ? 1 : 0;
    if (categoryBonus > 0) {
      matchFactors.push({
        factor: 'categoryPreference',
        score: categoryBonus,
        description: 'Preferred category',
      });
    }
    totalScore += categoryBonus * 0.15;
    totalWeight += 0.15;

    // Factor 4: Feedback-adjusted base confidence (weight: 0.35)
    const adjustedConfidence = this.calculateFeedbackAdjustedConfidence(pattern);
    matchFactors.push({
      factor: 'baseConfidence',
      score: adjustedConfidence,
      description: `Base confidence: ${(adjustedConfidence * 100).toFixed(0)}%`,
    });
    totalScore += adjustedConfidence * 0.35;
    totalWeight += 0.35;

    // Normalize score
    const confidence = totalWeight > 0 ? totalScore / totalWeight : pattern.baseConfidence;

    return { confidence: Math.min(1, Math.max(0, confidence)), matchFactors };
  }

  /**
   * Calculate type match score
   */
  private calculateTypeMatch(pattern: RecommendablePattern, entityType: string): number {
    if (pattern.applicableTypes.length === 0) {
      return 0.5; // No type restrictions
    }

    const normalizedType = entityType.toLowerCase();
    for (const applicableType of pattern.applicableTypes) {
      if (applicableType.toLowerCase() === normalizedType) {
        return 1.0;
      }
    }

    // Check for partial matches (e.g., 'class' matches 'service-class')
    for (const applicableType of pattern.applicableTypes) {
      if (normalizedType.includes(applicableType.toLowerCase()) ||
          applicableType.toLowerCase().includes(normalizedType)) {
        return 0.5;
      }
    }

    return 0;
  }

  /**
   * Calculate tag overlap using Jaccard similarity
   */
  private calculateTagOverlap(patternTags: string[], contextTags?: string[]): number {
    if (!contextTags || contextTags.length === 0 || patternTags.length === 0) {
      return 0;
    }

    const set1 = new Set(patternTags.map((t) => t.toLowerCase()));
    const set2 = new Set(contextTags.map((t) => t.toLowerCase()));

    const intersection = new Set([...set1].filter((x) => set2.has(x)));
    const union = new Set([...set1, ...set2]);

    return intersection.size / union.size;
  }

  /**
   * Calculate feedback-adjusted confidence
   */
  private calculateFeedbackAdjustedConfidence(pattern: RecommendablePattern): number {
    const totalFeedback = pattern.positiveCount + pattern.negativeCount;

    if (totalFeedback === 0) {
      return pattern.baseConfidence;
    }

    // Wilson score interval for confidence
    const positiveRatio = pattern.positiveCount / totalFeedback;
    const z = 1.96; // 95% confidence
    const n = totalFeedback;

    // Wilson score lower bound
    const wilsonScore = (positiveRatio + (z * z) / (2 * n) - 
      z * Math.sqrt((positiveRatio * (1 - positiveRatio) + (z * z) / (4 * n)) / n)) /
      (1 + (z * z) / n);

    // Blend base confidence with feedback-adjusted score
    const feedbackWeight = Math.min(1, totalFeedback / 10); // More feedback = more weight
    return pattern.baseConfidence * (1 - feedbackWeight) + wilsonScore * feedbackWeight;
  }

  /**
   * Generate human-readable reason from match factors
   */
  private generateReason(matchFactors: MatchFactor[]): string {
    const significantFactors = matchFactors
      .filter((f) => f.score > 0.5)
      .sort((a, b) => b.score - a.score)
      .slice(0, 2);

    if (significantFactors.length === 0) {
      return 'General recommendation';
    }

    return significantFactors.map((f) => f.description).join('; ');
  }

  // ============================================================================
  // Feedback Learning
  // ============================================================================

  /**
   * Record feedback for a pattern
   */
  async recordFeedback(
    patternId: string,
    type: FeedbackType,
    context?: RecommendationContext,
    comment?: string
  ): Promise<void> {
    const pattern = this.patterns.get(patternId);
    if (!pattern) {
      throw new Error(`Pattern not found: ${patternId}`);
    }

    const feedback: PatternFeedback = {
      id: `FB-${++this.feedbackIdCounter}`,
      patternId,
      type,
      context,
      comment,
      timestamp: new Date(),
    };

    this.feedbackHistory.push(feedback);

    // Update pattern statistics
    this.updatePatternFromFeedback(pattern, type);

    // Persist to repository if available
    if (this.repository) {
      await this.repository.recordFeedback(feedback);
      await this.repository.updatePattern(pattern);
    }

    this.emit('feedback:recorded', { feedback });
    this.emit('pattern:updated', { patternId });
  }

  /**
   * Update pattern statistics based on feedback
   */
  private updatePatternFromFeedback(pattern: RecommendablePattern, type: FeedbackType): void {
    pattern.usageCount++;
    pattern.lastUsed = new Date();

    switch (type) {
      case 'accepted':
        pattern.positiveCount++;
        // Slightly increase base confidence
        pattern.baseConfidence = Math.min(1, pattern.baseConfidence + this.learningRate * 0.5);
        break;
      case 'rejected':
        pattern.negativeCount++;
        // Slightly decrease base confidence
        pattern.baseConfidence = Math.max(0.1, pattern.baseConfidence - this.learningRate * 0.3);
        break;
      case 'modified':
        pattern.positiveCount += 0.5; // Partial positive
        break;
      case 'ignored':
        // No change to confidence
        break;
    }
  }

  /**
   * Get feedback history
   */
  getFeedbackHistory(): PatternFeedback[] {
    return [...this.feedbackHistory];
  }

  /**
   * Get feedback history for a specific pattern
   */
  getPatternFeedback(patternId: string): PatternFeedback[] {
    return this.feedbackHistory.filter((f) => f.patternId === patternId);
  }

  /**
   * Clear feedback history
   */
  clearFeedbackHistory(): void {
    this.feedbackHistory = [];
  }

  // ============================================================================
  // Pattern Decay
  // ============================================================================

  /**
   * Decay unused patterns to reduce their confidence over time
   */
  decayUnusedPatterns(cutoffDate: Date): number {
    let decayedCount = 0;

    for (const pattern of this.patterns.values()) {
      if (!pattern.lastUsed || pattern.lastUsed < cutoffDate) {
        const oldConfidence = pattern.baseConfidence;
        pattern.baseConfidence = Math.max(0.1, pattern.baseConfidence * this.decayFactor);

        if (pattern.baseConfidence !== oldConfidence) {
          decayedCount++;
          this.emit('pattern:updated', { patternId: pattern.id });
        }
      }
    }

    return decayedCount;
  }
}
