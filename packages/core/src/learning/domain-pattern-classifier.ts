/**
 * Domain Pattern Classifier
 *
 * Classifies patterns into domain-specific categories and learns
 * domain-specific pattern preferences from feedback.
 *
 * @packageDocumentation
 * @module learning/domain-pattern-classifier
 *
 * @see BP-DESIGN-001〜007 - 学習済みパターン
 * @see TSK-LRN-002 - ドメイン固有パターンタスク
 */

// DesignPattern type imported for documentation purposes
// eslint-disable-next-line @typescript-eslint/no-unused-vars
import type { DesignPattern as _DesignPattern } from './pattern-recommender.js';

/**
 * Domain definition with keywords and typical patterns
 */
export interface DomainDefinition {
  /** Domain identifier */
  id: string;
  /** Domain display name */
  name: string;
  /** Alternative names */
  aliases: string[];
  /** Keywords that indicate this domain */
  keywords: string[];
  /** Japanese keywords */
  keywordsJa: string[];
  /** Typical entity types */
  entities: string[];
  /** Pattern IDs commonly used in this domain */
  typicalPatterns: string[];
  /** Description */
  description: string;
}

/**
 * Classification result
 */
export interface ClassificationResult {
  /** Detected domain */
  domain: DomainDefinition;
  /** Confidence score (0-1) */
  confidence: number;
  /** Matched keywords */
  matchedKeywords: string[];
  /** Matched entities */
  matchedEntities: string[];
}

/**
 * Domain learning record
 */
export interface DomainPatternRecord {
  /** Domain ID */
  domainId: string;
  /** Pattern ID */
  patternId: string;
  /** Usage count */
  usageCount: number;
  /** Positive feedback count */
  positiveCount: number;
  /** Negative feedback count */
  negativeCount: number;
  /** Computed score */
  score: number;
}

/**
 * Classifier options
 */
export interface ClassifierOptions {
  /** Minimum confidence for classification */
  minConfidence?: number;
  /** Include sub-domains */
  includeSubDomains?: boolean;
}

const DEFAULT_OPTIONS: Required<ClassifierOptions> = {
  minConfidence: 0.3,
  includeSubDomains: true,
};

/**
 * Built-in domain definitions
 */
export const BUILT_IN_DOMAINS: DomainDefinition[] = [
  {
    id: 'ecommerce',
    name: 'E-Commerce',
    aliases: ['online-store', 'shop', 'retail'],
    keywords: ['cart', 'checkout', 'product', 'order', 'payment', 'shipping', 'inventory', 'catalog', 'discount', 'coupon'],
    keywordsJa: ['カート', '購入', '商品', '注文', '決済', '配送', '在庫', 'クーポン'],
    entities: ['Product', 'Order', 'Cart', 'Customer', 'Payment', 'Shipment'],
    typicalPatterns: ['PAT-CONC-001', 'PAT-TIME-001', 'PAT-CONC-004'],
    description: 'Online shopping and retail systems',
  },
  {
    id: 'fitness',
    name: 'Fitness & Health',
    aliases: ['health', 'workout', 'exercise', 'gym'],
    keywords: ['workout', 'exercise', 'training', 'muscle', 'cardio', 'weight', 'rep', 'set', 'goal', 'progress'],
    keywordsJa: ['トレーニング', '運動', '筋トレ', 'ワークアウト', '目標', '進捗'],
    entities: ['Workout', 'Exercise', 'Goal', 'Progress', 'User', 'Plan'],
    typicalPatterns: ['PAT-TIME-004', 'PAT-TIME-003'],
    description: 'Fitness tracking and health management',
  },
  {
    id: 'healthcare',
    name: 'Healthcare',
    aliases: ['medical', 'clinic', 'hospital'],
    keywords: ['patient', 'doctor', 'appointment', 'prescription', 'diagnosis', 'treatment', 'medical', 'health'],
    keywordsJa: ['患者', '医師', '予約', '処方', '診断', '治療', '医療'],
    entities: ['Patient', 'Doctor', 'Appointment', 'Prescription', 'Diagnosis'],
    typicalPatterns: ['PAT-TIME-002', 'PAT-CONC-002'],
    description: 'Medical and healthcare systems',
  },
  {
    id: 'finance',
    name: 'Finance & Banking',
    aliases: ['banking', 'payment', 'fintech'],
    keywords: ['account', 'transaction', 'balance', 'transfer', 'payment', 'credit', 'debit', 'loan', 'interest'],
    keywordsJa: ['口座', '取引', '残高', '振込', '決済', 'クレジット', 'ローン'],
    entities: ['Account', 'Transaction', 'Transfer', 'Balance', 'Loan'],
    typicalPatterns: ['PAT-CONC-001', 'PAT-CONC-002', 'PAT-CONC-004'],
    description: 'Financial and banking systems',
  },
  {
    id: 'education',
    name: 'Education',
    aliases: ['learning', 'school', 'training'],
    keywords: ['course', 'lesson', 'student', 'teacher', 'grade', 'assignment', 'exam', 'enrollment'],
    keywordsJa: ['コース', 'レッスン', '学生', '教師', '成績', '課題', '試験', '入学'],
    entities: ['Course', 'Lesson', 'Student', 'Teacher', 'Assignment', 'Grade'],
    typicalPatterns: ['PAT-TIME-004', 'PAT-TIME-003', 'PAT-TIME-002'],
    description: 'Education and learning management',
  },
  {
    id: 'booking',
    name: 'Booking & Reservations',
    aliases: ['reservation', 'appointment', 'scheduling'],
    keywords: ['booking', 'reservation', 'appointment', 'slot', 'availability', 'schedule', 'cancel', 'reschedule'],
    keywordsJa: ['予約', 'スロット', '空き', 'スケジュール', 'キャンセル'],
    entities: ['Booking', 'Reservation', 'Slot', 'Resource', 'Schedule'],
    typicalPatterns: ['PAT-CONC-002', 'PAT-TIME-002', 'PAT-CONC-001'],
    description: 'Booking and reservation systems',
  },
  {
    id: 'gaming',
    name: 'Gaming',
    aliases: ['game', 'entertainment'],
    keywords: ['player', 'score', 'level', 'achievement', 'leaderboard', 'game', 'quest', 'reward', 'points'],
    keywordsJa: ['プレイヤー', 'スコア', 'レベル', '実績', 'ゲーム', 'クエスト', '報酬', 'ポイント'],
    entities: ['Player', 'Game', 'Score', 'Achievement', 'Level', 'Reward'],
    typicalPatterns: ['PAT-TIME-004', 'PAT-TIME-005', 'PAT-TIME-001'],
    description: 'Gaming and gamification systems',
  },
  {
    id: 'inventory',
    name: 'Inventory Management',
    aliases: ['warehouse', 'stock', 'supply-chain'],
    keywords: ['inventory', 'stock', 'warehouse', 'item', 'quantity', 'sku', 'reorder', 'shipment'],
    keywordsJa: ['在庫', '倉庫', 'アイテム', '数量', '入荷', '出荷'],
    entities: ['Item', 'Stock', 'Warehouse', 'Shipment', 'Order'],
    typicalPatterns: ['PAT-CONC-001', 'PAT-CONC-002'],
    description: 'Inventory and warehouse management',
  },
  {
    id: 'membership',
    name: 'Membership & Subscription',
    aliases: ['subscription', 'loyalty'],
    keywords: ['member', 'subscription', 'plan', 'tier', 'renewal', 'billing', 'loyalty', 'points'],
    keywordsJa: ['会員', 'サブスクリプション', 'プラン', '更新', '課金', 'ロイヤリティ', 'ポイント'],
    entities: ['Member', 'Subscription', 'Plan', 'Tier', 'Billing'],
    typicalPatterns: ['PAT-TIME-001', 'PAT-TIME-003', 'PAT-CONC-004'],
    description: 'Membership and subscription systems',
  },
  {
    id: 'messaging',
    name: 'Messaging & Communication',
    aliases: ['chat', 'notification', 'communication'],
    keywords: ['message', 'chat', 'notification', 'conversation', 'channel', 'inbox', 'send', 'receive'],
    keywordsJa: ['メッセージ', 'チャット', '通知', '会話', 'チャンネル', '受信箱', '送信'],
    entities: ['Message', 'Conversation', 'Channel', 'Notification', 'User'],
    typicalPatterns: ['PAT-CONC-004', 'PAT-TIME-005'],
    description: 'Messaging and communication systems',
  },
];

/**
 * Domain Pattern Classifier
 *
 * Classifies content into domains and tracks pattern usage per domain.
 */
export class DomainPatternClassifier {
  private options: Required<ClassifierOptions>;
  private domains: Map<string, DomainDefinition> = new Map();
  private patternRecords: Map<string, DomainPatternRecord> = new Map();

  constructor(options?: ClassifierOptions) {
    this.options = { ...DEFAULT_OPTIONS, ...options };
    
    // Register built-in domains
    for (const domain of BUILT_IN_DOMAINS) {
      this.domains.set(domain.id, domain);
    }
  }

  /**
   * Register additional domains
   */
  registerDomain(domain: DomainDefinition): void {
    this.domains.set(domain.id, domain);
  }

  /**
   * Get all registered domains
   */
  getDomains(): DomainDefinition[] {
    return Array.from(this.domains.values());
  }

  /**
   * Classify content into a domain
   */
  classify(content: string): ClassificationResult[] {
    const contentLower = content.toLowerCase();
    const results: ClassificationResult[] = [];

    for (const domain of this.domains.values()) {
      const matchedKeywords: string[] = [];
      const matchedEntities: string[] = [];

      // Check keywords (English)
      for (const keyword of domain.keywords) {
        if (contentLower.includes(keyword.toLowerCase())) {
          matchedKeywords.push(keyword);
        }
      }

      // Check keywords (Japanese)
      for (const keyword of domain.keywordsJa) {
        if (content.includes(keyword)) {
          matchedKeywords.push(keyword);
        }
      }

      // Check entity names (PascalCase in code)
      for (const entity of domain.entities) {
        const entityPattern = new RegExp(`\\b${entity}\\b`, 'i');
        if (entityPattern.test(content)) {
          matchedEntities.push(entity);
        }
      }

      // Calculate confidence - use log-scaled keyword matching for better sensitivity
      // With many keywords, even 2-3 matches should give meaningful confidence
      const keywordCount = matchedKeywords.length;
      const entityCount = matchedEntities.length;
      
      // Logarithmic scaling: 1 match = 0.3, 2 = 0.45, 3 = 0.55, 5 = 0.7, 10 = 0.85
      const keywordScore = keywordCount > 0 
        ? Math.min(0.3 + 0.15 * Math.log2(keywordCount + 1), 1.0)
        : 0;
      const entityScore = entityCount > 0
        ? Math.min(0.3 + 0.2 * Math.log2(entityCount + 1), 1.0)
        : 0;
        
      const confidence = keywordScore * 0.5 + entityScore * 0.5;

      if (confidence >= this.options.minConfidence) {
        results.push({
          domain,
          confidence,
          matchedKeywords,
          matchedEntities,
        });
      }
    }

    // Sort by confidence
    return results.sort((a, b) => b.confidence - a.confidence);
  }

  /**
   * Get the primary domain for content
   */
  getPrimaryDomain(content: string): DomainDefinition | null {
    const results = this.classify(content);
    return results.length > 0 ? results[0].domain : null;
  }

  /**
   * Record pattern usage in a domain
   */
  recordPatternUsage(domainId: string, patternId: string, positive: boolean): void {
    const key = `${domainId}:${patternId}`;
    const existing = this.patternRecords.get(key) || {
      domainId,
      patternId,
      usageCount: 0,
      positiveCount: 0,
      negativeCount: 0,
      score: 0,
    };

    existing.usageCount++;
    if (positive) {
      existing.positiveCount++;
    } else {
      existing.negativeCount++;
    }

    // Calculate score (positive ratio with Laplace smoothing)
    existing.score = (existing.positiveCount + 1) / (existing.usageCount + 2);

    this.patternRecords.set(key, existing);
  }

  /**
   * Get top patterns for a domain based on recorded usage
   */
  getTopPatternsForDomain(domainId: string, limit = 5): DomainPatternRecord[] {
    const records = Array.from(this.patternRecords.values())
      .filter((r) => r.domainId === domainId)
      .sort((a, b) => b.score - a.score);

    return records.slice(0, limit);
  }

  /**
   * Get recommended patterns for a domain (combining built-in and learned)
   */
  getRecommendedPatterns(domainId: string): string[] {
    const domain = this.domains.get(domainId);
    if (!domain) return [];

    // Start with built-in typical patterns
    const patterns = new Set(domain.typicalPatterns);

    // Add learned patterns with high scores
    const learned = this.getTopPatternsForDomain(domainId);
    for (const record of learned) {
      if (record.score > 0.6) {
        patterns.add(record.patternId);
      }
    }

    return Array.from(patterns);
  }

  /**
   * Export learning data
   */
  exportLearningData(): DomainPatternRecord[] {
    return Array.from(this.patternRecords.values());
  }

  /**
   * Import learning data
   */
  importLearningData(records: DomainPatternRecord[]): void {
    for (const record of records) {
      const key = `${record.domainId}:${record.patternId}`;
      this.patternRecords.set(key, record);
    }
  }

  /**
   * Get domain-pattern affinity matrix
   */
  getAffinityMatrix(): Map<string, Map<string, number>> {
    const matrix = new Map<string, Map<string, number>>();

    // Initialize with built-in affinities
    for (const domain of this.domains.values()) {
      const patternScores = new Map<string, number>();
      for (const patternId of domain.typicalPatterns) {
        patternScores.set(patternId, 0.5); // Base score
      }
      matrix.set(domain.id, patternScores);
    }

    // Overlay learned scores
    for (const record of this.patternRecords.values()) {
      const domainScores = matrix.get(record.domainId);
      if (domainScores) {
        domainScores.set(record.patternId, record.score);
      }
    }

    return matrix;
  }
}

/**
 * Create a domain pattern classifier
 */
export function createDomainPatternClassifier(
  options?: ClassifierOptions
): DomainPatternClassifier {
  return new DomainPatternClassifier(options);
}
