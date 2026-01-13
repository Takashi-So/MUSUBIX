/**
 * Pattern Recommender
 *
 * Recommends design patterns based on context, domain, and code analysis.
 *
 * @packageDocumentation
 * @module learning/pattern-recommender
 *
 * @see BP-DESIGN-001〜007 - 学習済みパターン
 * @see TSK-LRN-001 - パターン推薦タスク
 */

/**
 * Design Pattern - Best practice pattern definition
 * Re-exported for use without depending on pattern-mcp
 */
export interface DesignPattern {
  /** Unique pattern ID (e.g., PAT-CONC-001, PAT-TIME-001) */
  id: string;
  /** Human-readable name */
  name: string;
  /** Pattern category (concurrency, temporal, etc.) */
  category: string;
  /** Applicable domains */
  domain: string[];
  /** Brief description */
  description: string;
  /** Problem this pattern solves */
  problem: string;
  /** Solution approach */
  solution: string;
  /** When to apply this pattern */
  applicability: string[];
  /** Trade-offs */
  consequences: {
    positive: string[];
    negative: string[];
  };
  /** TypeScript implementation example */
  implementation: string;
  /** Related pattern IDs */
  relatedPatterns?: string[];
  /** Confidence score (0-1) */
  confidence: number;
}

/**
 * Context for pattern recommendation
 */
export interface RecommendationContext {
  /** Source code to analyze */
  code?: string;
  /** Domain (e.g., 'ecommerce', 'fitness') */
  domain?: string;
  /** Keywords from requirements or description */
  keywords?: string[];
  /** Existing patterns in use */
  existingPatterns?: string[];
  /** Problem description */
  problemDescription?: string;
}

/**
 * Pattern recommendation result
 */
export interface PatternRecommendation {
  /** Recommended pattern */
  pattern: DesignPattern;
  /** Confidence score (0-1) */
  score: number;
  /** Reason for recommendation */
  reason: string;
  /** Priority (1=highest) */
  priority: number;
}

/**
 * Recommender options
 */
export interface PatternRecommenderOptions {
  /** Minimum score threshold */
  minScore?: number;
  /** Maximum recommendations */
  maxRecommendations?: number;
  /** Include related patterns */
  includeRelated?: boolean;
}

const DEFAULT_OPTIONS: Required<PatternRecommenderOptions> = {
  minScore: 0.25,
  maxRecommendations: 5,
  includeRelated: true,
};

/**
 * Keyword to pattern mapping
 */
const KEYWORD_PATTERN_MAP: Record<string, string[]> = {
  // Concurrency patterns
  concurrent: ['PAT-CONC-001', 'PAT-CONC-002'],
  lock: ['PAT-CONC-001', 'PAT-CONC-002'],
  optimistic: ['PAT-CONC-001'],
  pessimistic: ['PAT-CONC-002'],
  retry: ['PAT-CONC-003'],
  idempotent: ['PAT-CONC-004'],
  版本: ['PAT-CONC-001'], // Japanese for version
  排他: ['PAT-CONC-002'], // Japanese for exclusive
  
  // Time patterns
  expire: ['PAT-TIME-001'],
  expiry: ['PAT-TIME-001'],
  有効期限: ['PAT-TIME-001'],
  schedule: ['PAT-TIME-002'],
  予約: ['PAT-TIME-002'],
  スケジュール: ['PAT-TIME-002'],
  interval: ['PAT-TIME-003'],
  recurring: ['PAT-TIME-003'],
  定期: ['PAT-TIME-003'],
  streak: ['PAT-TIME-004'],
  連続: ['PAT-TIME-004'],
  cooldown: ['PAT-TIME-005'],
  ratelimit: ['PAT-TIME-005'],
  クールダウン: ['PAT-TIME-005'],
};

/**
 * Domain to pattern mapping
 */
const DOMAIN_PATTERN_MAP: Record<string, string[]> = {
  ecommerce: ['PAT-CONC-001', 'PAT-TIME-001', 'PAT-CONC-004'],
  fitness: ['PAT-TIME-004', 'PAT-TIME-003'],
  gaming: ['PAT-TIME-004', 'PAT-TIME-005'],
  education: ['PAT-TIME-004', 'PAT-TIME-003'],
  healthcare: ['PAT-TIME-002', 'PAT-CONC-002'],
  finance: ['PAT-CONC-001', 'PAT-CONC-002', 'PAT-CONC-004'],
  inventory: ['PAT-CONC-001', 'PAT-CONC-002'],
  booking: ['PAT-CONC-002', 'PAT-TIME-002'],
};

/**
 * Pattern Recommender
 *
 * Analyzes context and recommends applicable design patterns.
 */
export class PatternRecommender {
  private options: Required<PatternRecommenderOptions>;
  private patternRegistry: Map<string, DesignPattern> = new Map();

  constructor(options?: PatternRecommenderOptions) {
    this.options = { ...DEFAULT_OPTIONS, ...options };
  }

  /**
   * Register patterns for recommendation
   */
  registerPatterns(patterns: DesignPattern[]): void {
    for (const pattern of patterns) {
      this.patternRegistry.set(pattern.id, pattern);
    }
  }

  /**
   * Get all registered patterns
   */
  getRegisteredPatterns(): DesignPattern[] {
    return Array.from(this.patternRegistry.values());
  }

  /**
   * Recommend patterns based on context
   */
  recommend(context: RecommendationContext): PatternRecommendation[] {
    const scores = new Map<string, { score: number; reasons: string[] }>();

    // Score by keywords
    this.scoreByKeywords(context, scores);

    // Score by domain
    this.scoreByDomain(context, scores);

    // Score by code analysis
    this.scoreByCode(context, scores);

    // Score by problem description
    this.scoreByProblem(context, scores);

    // Exclude existing patterns
    if (context.existingPatterns) {
      for (const existing of context.existingPatterns) {
        scores.delete(existing);
      }
    }

    // Build recommendations
    const recommendations: PatternRecommendation[] = [];
    for (const [patternId, data] of scores) {
      if (data.score < this.options.minScore) continue;

      const pattern = this.patternRegistry.get(patternId);
      if (!pattern) continue;

      recommendations.push({
        pattern,
        score: Math.min(data.score, 1.0),
        reason: data.reasons.join('; '),
        priority: 0, // Will be set after sorting
      });
    }

    // Sort by score and assign priorities
    recommendations.sort((a, b) => b.score - a.score);
    recommendations.forEach((r, i) => (r.priority = i + 1));

    // Add related patterns if enabled
    if (this.options.includeRelated) {
      this.addRelatedPatterns(recommendations);
    }

    return recommendations.slice(0, this.options.maxRecommendations);
  }

  /**
   * Score patterns based on keywords
   */
  private scoreByKeywords(
    context: RecommendationContext,
    scores: Map<string, { score: number; reasons: string[] }>
  ): void {
    if (!context.keywords?.length) return;

    for (const keyword of context.keywords) {
      const lowerKeyword = keyword.toLowerCase();
      const patternIds = KEYWORD_PATTERN_MAP[lowerKeyword];
      if (!patternIds) continue;

      for (const patternId of patternIds) {
        const existing = scores.get(patternId) || { score: 0, reasons: [] };
        existing.score += 0.3;
        existing.reasons.push(`Keyword match: "${keyword}"`);
        scores.set(patternId, existing);
      }
    }
  }

  /**
   * Score patterns based on domain
   */
  private scoreByDomain(
    context: RecommendationContext,
    scores: Map<string, { score: number; reasons: string[] }>
  ): void {
    if (!context.domain) return;

    const domainLower = context.domain.toLowerCase();
    const patternIds = DOMAIN_PATTERN_MAP[domainLower];
    if (!patternIds) return;

    for (const patternId of patternIds) {
      const existing = scores.get(patternId) || { score: 0, reasons: [] };
      existing.score += 0.25;
      existing.reasons.push(`Domain match: ${context.domain}`);
      scores.set(patternId, existing);
    }
  }

  /**
   * Score patterns based on code analysis
   */
  private scoreByCode(
    context: RecommendationContext,
    scores: Map<string, { score: number; reasons: string[] }>
  ): void {
    if (!context.code) return;

    const codeLower = context.code.toLowerCase();

    // Detect patterns from code
    const codePatterns: Array<{ pattern: RegExp; id: string; reason: string }> =
      [
        {
          pattern: /version|@version|optimisticlocking/i,
          id: 'PAT-CONC-001',
          reason: 'Version field detected in code',
        },
        {
          pattern: /lock|mutex|synchronized|acquire.*release/i,
          id: 'PAT-CONC-002',
          reason: 'Lock mechanism detected in code',
        },
        {
          pattern: /retry|attempts|backoff|exponential/i,
          id: 'PAT-CONC-003',
          reason: 'Retry logic detected in code',
        },
        {
          pattern: /idempotency|idempotentkey|requestid/i,
          id: 'PAT-CONC-004',
          reason: 'Idempotency handling detected',
        },
        {
          pattern: /expir(e|y|ation)|validuntil|expiresAt/i,
          id: 'PAT-TIME-001',
          reason: 'Expiration logic detected',
        },
        {
          pattern: /schedule|scheduled(at|time)|appointmentat/i,
          id: 'PAT-TIME-002',
          reason: 'Scheduling logic detected',
        },
        {
          pattern: /interval|cron|recurring|periodic/i,
          id: 'PAT-TIME-003',
          reason: 'Interval/recurring logic detected',
        },
        {
          pattern: /streak|consecutive|continuousdays/i,
          id: 'PAT-TIME-004',
          reason: 'Streak tracking detected',
        },
        {
          pattern: /cooldown|ratelimit|throttle/i,
          id: 'PAT-TIME-005',
          reason: 'Rate limiting detected',
        },
      ];

    for (const { pattern, id, reason } of codePatterns) {
      if (pattern.test(codeLower)) {
        const existing = scores.get(id) || { score: 0, reasons: [] };
        existing.score += 0.35;
        existing.reasons.push(reason);
        scores.set(id, existing);
      }
    }
  }

  /**
   * Score patterns based on problem description
   */
  private scoreByProblem(
    context: RecommendationContext,
    scores: Map<string, { score: number; reasons: string[] }>
  ): void {
    if (!context.problemDescription) return;

    const desc = context.problemDescription.toLowerCase();

    // Problem patterns
    const problemPatterns: Array<{
      keywords: string[];
      id: string;
      reason: string;
    }> = [
      {
        keywords: ['conflict', '競合', 'simultaneous edit', '同時編集'],
        id: 'PAT-CONC-001',
        reason: 'Problem mentions conflict resolution',
      },
      {
        keywords: ['exclusive', '排他', 'only one', '一人だけ'],
        id: 'PAT-CONC-002',
        reason: 'Problem requires exclusive access',
      },
      {
        keywords: ['fail', 'retry', '失敗', 'リトライ', 'transient'],
        id: 'PAT-CONC-003',
        reason: 'Problem involves transient failures',
      },
      {
        keywords: ['duplicate', '重複', 'same request', '二重'],
        id: 'PAT-CONC-004',
        reason: 'Problem involves duplicate prevention',
      },
      {
        keywords: ['expire', 'valid until', '有効期限', '期限切れ'],
        id: 'PAT-TIME-001',
        reason: 'Problem involves expiration',
      },
      {
        keywords: ['schedule', 'appointment', '予約', '予定'],
        id: 'PAT-TIME-002',
        reason: 'Problem involves scheduling',
      },
      {
        keywords: ['recurring', 'periodic', '定期', '繰り返し'],
        id: 'PAT-TIME-003',
        reason: 'Problem involves recurring events',
      },
      {
        keywords: ['streak', 'consecutive', '連続', '毎日'],
        id: 'PAT-TIME-004',
        reason: 'Problem involves streak tracking',
      },
      {
        keywords: ['rate limit', 'too fast', '連打', '制限'],
        id: 'PAT-TIME-005',
        reason: 'Problem involves rate limiting',
      },
    ];

    for (const { keywords, id, reason } of problemPatterns) {
      if (keywords.some((kw) => desc.includes(kw))) {
        const existing = scores.get(id) || { score: 0, reasons: [] };
        existing.score += 0.4;
        existing.reasons.push(reason);
        scores.set(id, existing);
      }
    }
  }

  /**
   * Add related patterns to recommendations
   */
  private addRelatedPatterns(recommendations: PatternRecommendation[]): void {
    const existingIds = new Set(recommendations.map((r) => r.pattern.id));

    for (const rec of [...recommendations]) {
      if (!rec.pattern.relatedPatterns) continue;

      for (const relatedId of rec.pattern.relatedPatterns) {
        if (existingIds.has(relatedId)) continue;

        const relatedPattern = this.patternRegistry.get(relatedId);
        if (!relatedPattern) continue;

        // Add with reduced score
        recommendations.push({
          pattern: relatedPattern,
          score: rec.score * 0.6,
          reason: `Related to ${rec.pattern.name}`,
          priority: recommendations.length + 1,
        });
        existingIds.add(relatedId);
      }
    }
  }

  /**
   * Get recommendation explanation
   */
  explain(recommendation: PatternRecommendation): string {
    const { pattern, score, reason, priority } = recommendation;
    return [
      `## ${pattern.name} (${pattern.id})`,
      '',
      `**優先度**: ${priority}`,
      `**スコア**: ${(score * 100).toFixed(0)}%`,
      `**理由**: ${reason}`,
      '',
      `### 問題`,
      pattern.problem,
      '',
      `### 解決策`,
      pattern.solution,
      '',
      `### 適用例`,
      pattern.applicability.map((a) => `- ${a}`).join('\n'),
    ].join('\n');
  }
}

/**
 * Create a pattern recommender with default patterns
 */
export function createPatternRecommender(
  options?: PatternRecommenderOptions
): PatternRecommender {
  return new PatternRecommender(options);
}
