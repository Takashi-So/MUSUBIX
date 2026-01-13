/**
 * Domain Pattern Classifier Tests
 *
 * @see TSK-LRN-002
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  DomainPatternClassifier,
  createDomainPatternClassifier,
  BUILT_IN_DOMAINS,
  type DomainDefinition,
} from './domain-pattern-classifier.js';

describe('DomainPatternClassifier', () => {
  let classifier: DomainPatternClassifier;

  beforeEach(() => {
    classifier = new DomainPatternClassifier();
  });

  describe('BUILT_IN_DOMAINS', () => {
    it('should have at least 10 domains', () => {
      expect(BUILT_IN_DOMAINS.length).toBeGreaterThanOrEqual(10);
    });

    it('should have unique IDs', () => {
      const ids = BUILT_IN_DOMAINS.map((d) => d.id);
      expect(new Set(ids).size).toBe(ids.length);
    });

    it('should have required fields for each domain', () => {
      for (const domain of BUILT_IN_DOMAINS) {
        expect(domain.id).toBeTruthy();
        expect(domain.name).toBeTruthy();
        expect(domain.keywords.length).toBeGreaterThan(0);
        expect(domain.entities.length).toBeGreaterThan(0);
        expect(domain.typicalPatterns.length).toBeGreaterThan(0);
      }
    });
  });

  describe('getDomains', () => {
    it('should return all registered domains', () => {
      const domains = classifier.getDomains();
      expect(domains.length).toBe(BUILT_IN_DOMAINS.length);
    });
  });

  describe('registerDomain', () => {
    it('should register custom domains', () => {
      const customDomain: DomainDefinition = {
        id: 'custom',
        name: 'Custom Domain',
        aliases: [],
        keywords: ['custom', 'special'],
        keywordsJa: ['カスタム'],
        entities: ['CustomEntity'],
        typicalPatterns: ['PAT-CUSTOM-001'],
        description: 'A custom domain',
      };

      classifier.registerDomain(customDomain);
      expect(classifier.getDomains().length).toBe(BUILT_IN_DOMAINS.length + 1);
    });
  });

  describe('classify', () => {
    it('should classify ecommerce content', () => {
      const content = `
        interface Product {
          id: string;
          name: string;
          price: number;
        }
        
        interface Cart {
          items: CartItem[];
          checkout(): void;
        }
      `;

      const results = classifier.classify(content);
      expect(results.length).toBeGreaterThan(0);
      expect(results[0].domain.id).toBe('ecommerce');
    });

    it('should classify fitness content', () => {
      const content = `
        interface Workout {
          exercises: Exercise[];
          duration: number;
        }
        
        function startTraining(user: User, goal: Goal): void {
          // Track progress
        }
      `;

      const results = classifier.classify(content);
      expect(results.some((r) => r.domain.id === 'fitness')).toBe(true);
    });

    it('should classify healthcare content', () => {
      const content = `
        interface Patient {
          id: string;
          name: string;
        }
        
        interface Appointment {
          doctor: Doctor;
          scheduledAt: Date;
        }
        
        function bookAppointment(patient: Patient): void {
          // Diagnosis and treatment
        }
      `;

      const results = classifier.classify(content);
      expect(results.some((r) => r.domain.id === 'healthcare')).toBe(true);
    });

    it('should handle Japanese content', () => {
      const content = `
        // カート機能
        // 商品を追加して購入できる
        // クーポン適用も可能
      `;

      const results = classifier.classify(content);
      expect(results.some((r) => r.domain.id === 'ecommerce')).toBe(true);
    });

    it('should return matched keywords and entities', () => {
      const content = 'Product catalog and Cart management for checkout';

      const results = classifier.classify(content);
      const ecommerce = results.find((r) => r.domain.id === 'ecommerce');
      expect(ecommerce?.matchedKeywords.length).toBeGreaterThan(0);
    });

    it('should return empty for unrecognized content', () => {
      const content = 'xyz abc def ghi jkl mno';

      const results = classifier.classify(content);
      expect(results).toHaveLength(0);
    });
  });

  describe('getPrimaryDomain', () => {
    it('should return the highest confidence domain', () => {
      const content = 'Product Cart checkout Order';

      const domain = classifier.getPrimaryDomain(content);
      expect(domain?.id).toBe('ecommerce');
    });

    it('should return null for unrecognized content', () => {
      const domain = classifier.getPrimaryDomain('xyz');
      expect(domain).toBeNull();
    });
  });

  describe('recordPatternUsage', () => {
    it('should record positive usage', () => {
      classifier.recordPatternUsage('ecommerce', 'PAT-CONC-001', true);
      
      const records = classifier.getTopPatternsForDomain('ecommerce');
      expect(records.length).toBe(1);
      expect(records[0].positiveCount).toBe(1);
    });

    it('should record negative usage', () => {
      classifier.recordPatternUsage('ecommerce', 'PAT-CONC-001', false);
      
      const records = classifier.getTopPatternsForDomain('ecommerce');
      expect(records[0].negativeCount).toBe(1);
    });

    it('should accumulate usage counts', () => {
      classifier.recordPatternUsage('ecommerce', 'PAT-CONC-001', true);
      classifier.recordPatternUsage('ecommerce', 'PAT-CONC-001', true);
      classifier.recordPatternUsage('ecommerce', 'PAT-CONC-001', false);
      
      const records = classifier.getTopPatternsForDomain('ecommerce');
      expect(records[0].usageCount).toBe(3);
      expect(records[0].positiveCount).toBe(2);
      expect(records[0].negativeCount).toBe(1);
    });

    it('should calculate score with Laplace smoothing', () => {
      classifier.recordPatternUsage('ecommerce', 'PAT-CONC-001', true);
      
      const records = classifier.getTopPatternsForDomain('ecommerce');
      // (1 + 1) / (1 + 2) = 2/3 ≈ 0.67
      expect(records[0].score).toBeCloseTo(0.67, 1);
    });
  });

  describe('getTopPatternsForDomain', () => {
    it('should return patterns sorted by score', () => {
      classifier.recordPatternUsage('ecommerce', 'PAT-A', true);
      classifier.recordPatternUsage('ecommerce', 'PAT-A', true);
      classifier.recordPatternUsage('ecommerce', 'PAT-B', true);
      classifier.recordPatternUsage('ecommerce', 'PAT-B', false);
      classifier.recordPatternUsage('ecommerce', 'PAT-C', false);
      
      const records = classifier.getTopPatternsForDomain('ecommerce');
      
      expect(records[0].patternId).toBe('PAT-A');
      expect(records[1].patternId).toBe('PAT-B');
      expect(records[2].patternId).toBe('PAT-C');
    });

    it('should respect limit parameter', () => {
      classifier.recordPatternUsage('ecommerce', 'PAT-A', true);
      classifier.recordPatternUsage('ecommerce', 'PAT-B', true);
      classifier.recordPatternUsage('ecommerce', 'PAT-C', true);
      
      const records = classifier.getTopPatternsForDomain('ecommerce', 2);
      expect(records.length).toBe(2);
    });
  });

  describe('getRecommendedPatterns', () => {
    it('should include built-in typical patterns', () => {
      const patterns = classifier.getRecommendedPatterns('ecommerce');
      expect(patterns).toContain('PAT-CONC-001');
      expect(patterns).toContain('PAT-TIME-001');
    });

    it('should include learned patterns with high scores', () => {
      // Record many positive uses
      for (let i = 0; i < 10; i++) {
        classifier.recordPatternUsage('ecommerce', 'PAT-LEARNED', true);
      }
      
      const patterns = classifier.getRecommendedPatterns('ecommerce');
      expect(patterns).toContain('PAT-LEARNED');
    });

    it('should not include low-score learned patterns', () => {
      classifier.recordPatternUsage('ecommerce', 'PAT-LOW', false);
      classifier.recordPatternUsage('ecommerce', 'PAT-LOW', false);
      
      const patterns = classifier.getRecommendedPatterns('ecommerce');
      expect(patterns).not.toContain('PAT-LOW');
    });

    it('should return empty for unknown domain', () => {
      const patterns = classifier.getRecommendedPatterns('unknown');
      expect(patterns).toHaveLength(0);
    });
  });

  describe('exportLearningData / importLearningData', () => {
    it('should export learning data', () => {
      classifier.recordPatternUsage('ecommerce', 'PAT-A', true);
      classifier.recordPatternUsage('fitness', 'PAT-B', false);
      
      const data = classifier.exportLearningData();
      expect(data.length).toBe(2);
    });

    it('should import learning data', () => {
      const data = [
        {
          domainId: 'ecommerce',
          patternId: 'PAT-IMPORTED',
          usageCount: 5,
          positiveCount: 4,
          negativeCount: 1,
          score: 0.8,
        },
      ];
      
      classifier.importLearningData(data);
      const records = classifier.getTopPatternsForDomain('ecommerce');
      expect(records.some((r) => r.patternId === 'PAT-IMPORTED')).toBe(true);
    });
  });

  describe('getAffinityMatrix', () => {
    it('should return matrix with built-in affinities', () => {
      const matrix = classifier.getAffinityMatrix();
      
      expect(matrix.has('ecommerce')).toBe(true);
      expect(matrix.get('ecommerce')?.has('PAT-CONC-001')).toBe(true);
    });

    it('should overlay learned scores', () => {
      // Record high usage
      for (let i = 0; i < 10; i++) {
        classifier.recordPatternUsage('ecommerce', 'PAT-CONC-001', true);
      }
      
      const matrix = classifier.getAffinityMatrix();
      const ecommercePatterns = matrix.get('ecommerce');
      
      // Learned score should be higher than base 0.5
      expect(ecommercePatterns?.get('PAT-CONC-001')).toBeGreaterThan(0.5);
    });
  });

  describe('createDomainPatternClassifier', () => {
    it('should create classifier with factory function', () => {
      const c = createDomainPatternClassifier();
      expect(c).toBeInstanceOf(DomainPatternClassifier);
    });

    it('should accept options', () => {
      const c = createDomainPatternClassifier({ minConfidence: 0.5 });
      expect(c).toBeInstanceOf(DomainPatternClassifier);
    });
  });

  describe('minConfidence option', () => {
    it('should filter results below minConfidence', () => {
      const strictClassifier = new DomainPatternClassifier({ minConfidence: 0.8 });
      
      // Single keyword match shouldn't be enough
      const results = strictClassifier.classify('cart');
      
      // With high threshold, may return empty or fewer results
      expect(results.every((r) => r.confidence >= 0.8)).toBe(true);
    });
  });
});
