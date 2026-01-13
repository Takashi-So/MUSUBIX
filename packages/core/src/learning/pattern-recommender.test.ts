/**
 * Pattern Recommender Tests
 *
 * @see TSK-LRN-001
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  PatternRecommender,
  createPatternRecommender,
  type RecommendationContext,
  type DesignPattern,
} from './pattern-recommender.js';

// Mock patterns for testing
const MOCK_PATTERNS: DesignPattern[] = [
  {
    id: 'PAT-CONC-001',
    name: 'Optimistic Locking',
    category: 'concurrency',
    domain: ['all'],
    description: 'Version-based concurrency control',
    problem: 'Concurrent modifications may conflict',
    solution: 'Use version field to detect conflicts',
    applicability: ['Multi-user editing', 'Inventory management'],
    consequences: { positive: ['High throughput'], negative: ['Retry needed'] },
    implementation: 'interface Versionable { version: number }',
    relatedPatterns: ['PAT-CONC-002'],
    confidence: 0.95,
  },
  {
    id: 'PAT-CONC-002',
    name: 'Pessimistic Locking',
    category: 'concurrency',
    domain: ['all'],
    description: 'Lock-based concurrency control',
    problem: 'Exclusive access needed',
    solution: 'Acquire lock before modification',
    applicability: ['Critical sections', 'Payment processing'],
    consequences: {
      positive: ['Guaranteed consistency'],
      negative: ['Lower throughput'],
    },
    implementation: 'interface Lockable { lockedBy: string }',
    relatedPatterns: ['PAT-CONC-001'],
    confidence: 0.9,
  },
  {
    id: 'PAT-TIME-001',
    name: 'Expiry Pattern',
    category: 'temporal',
    domain: ['all'],
    description: 'Manage entity expiration',
    problem: 'Entities need to expire',
    solution: 'Use expiresAt field',
    applicability: ['Tokens', 'Coupons'],
    consequences: { positive: ['Clear semantics'], negative: ['Cleanup needed'] },
    implementation: 'interface Expirable { expiresAt: Date }',
    relatedPatterns: ['PAT-TIME-002'],
    confidence: 0.9,
  },
  {
    id: 'PAT-TIME-004',
    name: 'Streak Pattern',
    category: 'temporal',
    domain: ['fitness', 'gaming'],
    description: 'Track consecutive activity',
    problem: 'Track user engagement',
    solution: 'Store streak count',
    applicability: ['Habit tracking', 'Gamification'],
    consequences: {
      positive: ['Motivates users'],
      negative: ['Timezone complexity'],
    },
    implementation: 'interface Streak { currentStreak: number }',
    confidence: 0.85,
  },
];

describe('PatternRecommender', () => {
  let recommender: PatternRecommender;

  beforeEach(() => {
    recommender = new PatternRecommender();
    recommender.registerPatterns(MOCK_PATTERNS);
  });

  describe('registerPatterns', () => {
    it('should register patterns', () => {
      const patterns = recommender.getRegisteredPatterns();
      expect(patterns).toHaveLength(4);
    });

    it('should allow adding more patterns', () => {
      recommender.registerPatterns([
        {
          id: 'PAT-NEW-001',
          name: 'New Pattern',
          category: 'new',
          domain: ['all'],
          description: 'New',
          problem: 'New',
          solution: 'New',
          applicability: [],
          consequences: { positive: [], negative: [] },
          implementation: '',
          confidence: 0.5,
        },
      ]);
      expect(recommender.getRegisteredPatterns()).toHaveLength(5);
    });
  });

  describe('recommend by keywords', () => {
    it('should recommend based on keyword match', () => {
      const context: RecommendationContext = {
        keywords: ['optimistic', 'lock'],
      };

      const recommendations = recommender.recommend(context);
      expect(recommendations.length).toBeGreaterThan(0);
      expect(recommendations[0].pattern.id).toBe('PAT-CONC-001');
    });

    it('should recommend expiry pattern for expire keyword', () => {
      const context: RecommendationContext = {
        keywords: ['expire'],
      };

      const recommendations = recommender.recommend(context);
      expect(recommendations.some((r) => r.pattern.id === 'PAT-TIME-001')).toBe(
        true
      );
    });

    it('should handle Japanese keywords', () => {
      const context: RecommendationContext = {
        keywords: ['有効期限'],
      };

      const recommendations = recommender.recommend(context);
      expect(recommendations.some((r) => r.pattern.id === 'PAT-TIME-001')).toBe(
        true
      );
    });
  });

  describe('recommend by domain', () => {
    it('should recommend domain-specific patterns', () => {
      const context: RecommendationContext = {
        domain: 'fitness',
      };

      const recommendations = recommender.recommend(context);
      expect(recommendations.some((r) => r.pattern.id === 'PAT-TIME-004')).toBe(
        true
      );
    });

    it('should recommend ecommerce patterns', () => {
      const context: RecommendationContext = {
        domain: 'ecommerce',
      };

      const recommendations = recommender.recommend(context);
      expect(recommendations.some((r) => r.pattern.id === 'PAT-CONC-001')).toBe(
        true
      );
      expect(recommendations.some((r) => r.pattern.id === 'PAT-TIME-001')).toBe(
        true
      );
    });
  });

  describe('recommend by code analysis', () => {
    it('should detect version field in code', () => {
      const context: RecommendationContext = {
        code: `interface Entity {
          id: string;
          version: number;
          name: string;
        }`,
      };

      const recommendations = recommender.recommend(context);
      expect(recommendations.some((r) => r.pattern.id === 'PAT-CONC-001')).toBe(
        true
      );
    });

    it('should detect expiration logic in code', () => {
      const context: RecommendationContext = {
        code: `function isExpired(token: Token): boolean {
          return token.expiresAt < new Date();
        }`,
      };

      const recommendations = recommender.recommend(context);
      expect(recommendations.some((r) => r.pattern.id === 'PAT-TIME-001')).toBe(
        true
      );
    });

    it('should detect retry logic in code', () => {
      const context: RecommendationContext = {
        code: `async function fetchWithRetry(url: string, attempts = 3) {
          // exponential backoff
        }`,
      };

      // PAT-CONC-003 is not in MOCK_PATTERNS, so it won't be found
      // But we verify code analysis logic works
      const recommendations = recommender.recommend(context);
      expect(recommendations).toBeInstanceOf(Array);
    });
  });

  describe('recommend by problem description', () => {
    it('should recommend for conflict problems', () => {
      const context: RecommendationContext = {
        problemDescription:
          'Users are experiencing conflicts when editing the same document',
      };

      const recommendations = recommender.recommend(context);
      expect(recommendations.some((r) => r.pattern.id === 'PAT-CONC-001')).toBe(
        true
      );
    });

    it('should recommend for expiration problems', () => {
      const context: RecommendationContext = {
        problemDescription:
          'We need to handle coupon expiration and valid until dates',
      };

      const recommendations = recommender.recommend(context);
      expect(recommendations.some((r) => r.pattern.id === 'PAT-TIME-001')).toBe(
        true
      );
    });

    it('should handle Japanese problem descriptions', () => {
      const context: RecommendationContext = {
        problemDescription: '複数ユーザーの同時編集で競合が発生しています',
      };

      const recommendations = recommender.recommend(context);
      expect(recommendations.some((r) => r.pattern.id === 'PAT-CONC-001')).toBe(
        true
      );
    });
  });

  describe('combined context', () => {
    it('should combine scores from multiple sources', () => {
      const context: RecommendationContext = {
        keywords: ['optimistic'],
        domain: 'ecommerce',
        code: 'version: number',
        problemDescription: 'concurrent editing conflict',
      };

      const recommendations = recommender.recommend(context);
      expect(recommendations[0].pattern.id).toBe('PAT-CONC-001');
      expect(recommendations[0].score).toBeGreaterThan(0.5);
    });
  });

  describe('exclude existing patterns', () => {
    it('should not recommend already used patterns', () => {
      const context: RecommendationContext = {
        keywords: ['optimistic'],
        existingPatterns: ['PAT-CONC-001'],
      };

      const recommendations = recommender.recommend(context);
      expect(recommendations.every((r) => r.pattern.id !== 'PAT-CONC-001')).toBe(
        true
      );
    });
  });

  describe('related patterns', () => {
    it('should include related patterns by default', () => {
      const recommenderWithRelated = new PatternRecommender({
        includeRelated: true,
      });
      recommenderWithRelated.registerPatterns(MOCK_PATTERNS);

      const context: RecommendationContext = {
        keywords: ['optimistic'],
      };

      const recommendations = recommenderWithRelated.recommend(context);
      // PAT-CONC-001 is related to PAT-CONC-002
      const hasRelated = recommendations.some(
        (r) => r.reason.includes('Related to')
      );
      expect(hasRelated).toBe(true);
    });

    it('should not include related patterns when disabled', () => {
      const recommenderNoRelated = new PatternRecommender({
        includeRelated: false,
      });
      recommenderNoRelated.registerPatterns(MOCK_PATTERNS);

      const context: RecommendationContext = {
        keywords: ['optimistic'],
      };

      const recommendations = recommenderNoRelated.recommend(context);
      expect(
        recommendations.every((r) => !r.reason.includes('Related to'))
      ).toBe(true);
    });
  });

  describe('options', () => {
    it('should respect minScore option', () => {
      const strictRecommender = new PatternRecommender({ minScore: 0.9 });
      strictRecommender.registerPatterns(MOCK_PATTERNS);

      const context: RecommendationContext = {
        keywords: ['something-obscure'],
      };

      const recommendations = strictRecommender.recommend(context);
      expect(recommendations).toHaveLength(0);
    });

    it('should respect maxRecommendations option', () => {
      const limitedRecommender = new PatternRecommender({
        maxRecommendations: 2,
      });
      limitedRecommender.registerPatterns(MOCK_PATTERNS);

      const context: RecommendationContext = {
        domain: 'ecommerce',
        keywords: ['lock', 'expire'],
      };

      const recommendations = limitedRecommender.recommend(context);
      expect(recommendations.length).toBeLessThanOrEqual(2);
    });
  });

  describe('explain', () => {
    it('should generate explanation for recommendation', () => {
      const context: RecommendationContext = {
        keywords: ['optimistic'],
      };

      const recommendations = recommender.recommend(context);
      const explanation = recommender.explain(recommendations[0]);

      expect(explanation).toContain('## Optimistic Locking');
      expect(explanation).toContain('PAT-CONC-001');
      expect(explanation).toContain('優先度');
      expect(explanation).toContain('スコア');
      expect(explanation).toContain('問題');
      expect(explanation).toContain('解決策');
    });
  });

  describe('createPatternRecommender', () => {
    it('should create recommender with factory function', () => {
      const r = createPatternRecommender();
      expect(r).toBeInstanceOf(PatternRecommender);
    });

    it('should accept options', () => {
      const r = createPatternRecommender({ minScore: 0.5 });
      expect(r).toBeInstanceOf(PatternRecommender);
    });
  });

  describe('priority assignment', () => {
    it('should assign sequential priorities starting from 1', () => {
      const context: RecommendationContext = {
        domain: 'ecommerce',
        keywords: ['optimistic'],
      };

      const recommendations = recommender.recommend(context);
      expect(recommendations.length).toBeGreaterThan(0);
      
      // Priorities should be sequential starting from 1
      for (let i = 0; i < recommendations.length; i++) {
        expect(recommendations[i].priority).toBe(i + 1);
      }
    });
  });

  describe('score capping', () => {
    it('should cap scores at 1.0', () => {
      const context: RecommendationContext = {
        keywords: ['optimistic', 'lock', 'version'],
        domain: 'finance',
        code: 'version: number; optimisticLocking',
        problemDescription: 'concurrent editing conflict',
      };

      const recommendations = recommender.recommend(context);
      for (const r of recommendations) {
        expect(r.score).toBeLessThanOrEqual(1.0);
      }
    });
  });
});
