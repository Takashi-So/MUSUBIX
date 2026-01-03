/**
 * Learning Engine
 *
 * Main orchestrator for the self-learning system
 *
 * @see REQ-LEARN-003 - Adaptive Reasoning
 * @module @musubix/core/learning
 */

import { FeedbackCollector, type FeedbackInput, type FeedbackQuery } from './feedback-collector.js';
import { PatternExtractor } from './pattern-extractor.js';
import type {
  Feedback,
  LearnedPattern,
  PatternMatch,
  LearningStats,
  LearningConfig,
  PatternCategory,
} from './types.js';

/**
 * Inference context for pattern matching
 */
export interface InferenceContext {
  artifactType: 'requirement' | 'design' | 'code' | 'test';
  language?: string;
  framework?: string;
  tags?: string[];
}

/**
 * Learning Engine class
 *
 * Orchestrates feedback collection, pattern extraction, and adaptive reasoning
 *
 * @see REQ-LEARN-001 - Feedback Collection
 * @see REQ-LEARN-002 - Pattern Extraction
 * @see REQ-LEARN-003 - Adaptive Reasoning
 */
export class LearningEngine {
  private feedbackCollector: FeedbackCollector;
  private patternExtractor: PatternExtractor;
  private config: LearningConfig;

  constructor(config: Partial<LearningConfig> = {}) {
    this.config = {
      patternThreshold: config.patternThreshold || 3,
      decayDays: config.decayDays || 30,
      decayRate: config.decayRate || 0.1,
      minConfidence: config.minConfidence || 0.1,
      storagePath: config.storagePath || 'storage/learning',
    };
    this.feedbackCollector = new FeedbackCollector(this.config);
    this.patternExtractor = new PatternExtractor(this.config);
  }

  // ==========================================================================
  // Feedback Management
  // ==========================================================================

  /**
   * Record feedback for an artifact
   *
   * @see REQ-LEARN-001 - Feedback Collection
   */
  async recordFeedback(input: FeedbackInput): Promise<Feedback> {
    const feedback = await this.feedbackCollector.recordFeedback(input);

    // Trigger pattern extraction after recording
    await this.tryExtractPatterns();

    return feedback;
  }

  /**
   * Record acceptance of an artifact
   */
  async acceptArtifact(
    artifactId: string,
    artifactType: FeedbackInput['artifactType'],
    context?: Partial<FeedbackInput['context']>,
    reason?: string
  ): Promise<Feedback> {
    return this.recordFeedback({
      type: 'accept',
      artifactType,
      artifactId,
      context,
      reason,
    });
  }

  /**
   * Record rejection of an artifact
   */
  async rejectArtifact(
    artifactId: string,
    artifactType: FeedbackInput['artifactType'],
    context?: Partial<FeedbackInput['context']>,
    reason?: string
  ): Promise<Feedback> {
    return this.recordFeedback({
      type: 'reject',
      artifactType,
      artifactId,
      context,
      reason,
    });
  }

  /**
   * Record modification of an artifact
   */
  async modifyArtifact(
    artifactId: string,
    artifactType: FeedbackInput['artifactType'],
    original: string,
    modified: string,
    context?: Partial<FeedbackInput['context']>,
    reason?: string
  ): Promise<Feedback> {
    return this.recordFeedback({
      type: 'modify',
      artifactType,
      artifactId,
      context,
      reason,
      original,
      modified,
    });
  }

  /**
   * Query feedback
   */
  async queryFeedback(query: FeedbackQuery = {}): Promise<Feedback[]> {
    return this.feedbackCollector.queryFeedback(query);
  }

  // ==========================================================================
  // Pattern Management
  // ==========================================================================

  /**
   * Get all learned patterns
   */
  async getPatterns(): Promise<LearnedPattern[]> {
    return this.patternExtractor.getPatterns();
  }

  /**
   * Get patterns by category
   */
  async getPatternsByCategory(
    category: PatternCategory
  ): Promise<LearnedPattern[]> {
    return this.patternExtractor.getPatternsByCategory(category);
  }

  /**
   * Add a manual pattern
   */
  async addPattern(
    name: string,
    category: PatternCategory,
    trigger: LearnedPattern['trigger'],
    action: LearnedPattern['action'],
    confidence: number = 0.5
  ): Promise<LearnedPattern> {
    return this.patternExtractor.addPattern(
      name,
      category,
      trigger,
      action,
      confidence
    );
  }

  /**
   * Remove a pattern
   */
  async removePattern(id: string): Promise<boolean> {
    return this.patternExtractor.removePattern(id);
  }

  /**
   * Apply decay to unused patterns
   *
   * @see REQ-LEARN-004 - Pattern Decay
   */
  async applyDecay(): Promise<{ decayed: number; archived: number }> {
    return this.patternExtractor.applyDecay(
      this.config.decayDays,
      this.config.decayRate,
      this.config.minConfidence
    );
  }

  // ==========================================================================
  // Adaptive Reasoning
  // ==========================================================================

  /**
   * Find matching patterns for inference context
   *
   * @see REQ-LEARN-003 - Adaptive Reasoning
   * @param context - Current inference context
   * @returns Matching patterns sorted by relevance
   */
  async findMatchingPatterns(context: InferenceContext): Promise<PatternMatch[]> {
    const patterns = await this.patternExtractor.getPatterns();
    const matches: PatternMatch[] = [];

    for (const pattern of patterns) {
      // Check category match
      if (pattern.category !== context.artifactType) continue;

      // Calculate match score
      const { score, matchedKeys } = this.calculateMatchScore(pattern, context);

      if (score > 0) {
        matches.push({
          pattern,
          matchScore: score * pattern.confidence,
          matchedKeys,
        });
      }
    }

    // Sort by combined score (match score * confidence)
    matches.sort((a, b) => b.matchScore - a.matchScore);

    return matches;
  }

  /**
   * Get recommendations for current context
   *
   * @see REQ-LEARN-003 - Adaptive Reasoning
   */
  async getRecommendations(
    context: InferenceContext,
    limit: number = 5
  ): Promise<{
    prefer: LearnedPattern[];
    avoid: LearnedPattern[];
    suggest: LearnedPattern[];
  }> {
    const matches = await this.findMatchingPatterns(context);
    const recommendations = {
      prefer: [] as LearnedPattern[],
      avoid: [] as LearnedPattern[],
      suggest: [] as LearnedPattern[],
    };

    for (const match of matches.slice(0, limit * 3)) {
      const actionType = match.pattern.action.type;
      if (recommendations[actionType].length < limit) {
        recommendations[actionType].push(match.pattern);
      }
    }

    return recommendations;
  }

  /**
   * Apply pattern to adjust inference
   */
  async applyPattern(
    patternId: string,
    success: boolean
  ): Promise<LearnedPattern | undefined> {
    return this.patternExtractor.updatePatternUsage(patternId, success);
  }

  // ==========================================================================
  // Statistics & Export
  // ==========================================================================

  /**
   * Get learning statistics
   *
   * @see REQ-LEARN-005 - Learning Visualization
   */
  async getStats(): Promise<LearningStats> {
    const feedbackStats = await this.feedbackCollector.getStats();
    const patterns = await this.patternExtractor.getPatterns();

    const patternsByCategory: Record<PatternCategory, number> = {
      code: 0,
      design: 0,
      requirement: 0,
      test: 0,
    };

    let totalConfidence = 0;
    for (const pattern of patterns) {
      patternsByCategory[pattern.category]++;
      totalConfidence += pattern.confidence;
    }

    return {
      totalFeedback: feedbackStats.total,
      feedbackByType: feedbackStats.byType,
      totalPatterns: patterns.length,
      patternsByCategory,
      averageConfidence: patterns.length > 0 ? totalConfidence / patterns.length : 0,
      lastUpdate: new Date(),
    };
  }

  /**
   * Export all learning data
   */
  async export(): Promise<{
    feedback: Feedback[];
    patterns: LearnedPattern[];
    stats: LearningStats;
  }> {
    return {
      feedback: await this.feedbackCollector.export(),
      patterns: await this.patternExtractor.export(),
      stats: await this.getStats(),
    };
  }

  /**
   * Import learning data
   */
  async import(data: {
    feedback?: Feedback[];
    patterns?: LearnedPattern[];
  }): Promise<{ feedbackImported: number; patternsImported: number }> {
    let feedbackImported = 0;
    let patternsImported = 0;

    if (data.feedback) {
      feedbackImported = await this.feedbackCollector.import(data.feedback);
    }
    if (data.patterns) {
      patternsImported = await this.patternExtractor.import(data.patterns);
    }

    return { feedbackImported, patternsImported };
  }

  /**
   * Generate status report
   */
  async generateStatusReport(): Promise<string> {
    const stats = await this.getStats();
    const highConfPatterns = await this.patternExtractor.getHighConfidencePatterns(0.7);

    const lines = [
      '# MUSUBIX Learning Status Report',
      '',
      `**Generated**: ${new Date().toISOString()}`,
      '',
      '## Summary',
      '',
      `- Total Feedback: ${stats.totalFeedback}`,
      `- Total Patterns: ${stats.totalPatterns}`,
      `- Average Confidence: ${(stats.averageConfidence * 100).toFixed(1)}%`,
      '',
      '## Feedback by Type',
      '',
      `- Accept: ${stats.feedbackByType.accept}`,
      `- Reject: ${stats.feedbackByType.reject}`,
      `- Modify: ${stats.feedbackByType.modify}`,
      '',
      '## Patterns by Category',
      '',
      `- Code: ${stats.patternsByCategory.code}`,
      `- Design: ${stats.patternsByCategory.design}`,
      `- Requirement: ${stats.patternsByCategory.requirement}`,
      `- Test: ${stats.patternsByCategory.test}`,
      '',
      '## High Confidence Patterns (≥70%)',
      '',
    ];

    if (highConfPatterns.length === 0) {
      lines.push('_No high confidence patterns yet._');
    } else {
      for (const pattern of highConfPatterns) {
        lines.push(`### ${pattern.name}`);
        lines.push('');
        lines.push(`- **ID**: ${pattern.id}`);
        lines.push(`- **Category**: ${pattern.category}`);
        lines.push(`- **Action**: ${pattern.action.type}`);
        lines.push(`- **Confidence**: ${(pattern.confidence * 100).toFixed(1)}%`);
        lines.push(`- **Occurrences**: ${pattern.occurrences}`);
        lines.push('');
      }
    }

    return lines.join('\n');
  }

  // ==========================================================================
  // Private Methods
  // ==========================================================================

  /**
   * Calculate match score between pattern and context
   */
  private calculateMatchScore(
    pattern: LearnedPattern,
    context: InferenceContext
  ): { score: number; matchedKeys: string[] } {
    const matchedKeys: string[] = [];
    let matchCount = 0;
    let totalKeys = 0;

    const triggerContext = pattern.trigger.context;

    // Check language match
    if (triggerContext.language) {
      totalKeys++;
      if (context.language === triggerContext.language) {
        matchCount++;
        matchedKeys.push('language');
      }
    }

    // Check framework match
    if (triggerContext.framework) {
      totalKeys++;
      if (context.framework === triggerContext.framework) {
        matchCount++;
        matchedKeys.push('framework');
      }
    }

    // If no specific context required, it's a general match
    if (totalKeys === 0) {
      return { score: 0.5, matchedKeys: ['general'] };
    }

    return {
      score: matchCount / totalKeys,
      matchedKeys,
    };
  }

  /**
   * Try to extract patterns from recent feedback
   */
  private async tryExtractPatterns(): Promise<void> {
    const recentFeedback = await this.feedbackCollector.queryFeedback({
      limit: 100,
    });

    if (recentFeedback.length >= this.config.patternThreshold) {
      await this.patternExtractor.extractPatterns(recentFeedback);
    }
  }
}
