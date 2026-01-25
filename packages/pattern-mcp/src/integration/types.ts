/**
 * @fileoverview Skill-Pattern Bridge Types
 * Integrates learning-hooks skill with pattern-mcp
 * 
 * @traceability TSK-INT-002, DES-v3.7.0 Section 9.4
 */

import type { Pattern } from '../types.js';

/**
 * Learned pattern from learning-hooks skill
 */
export interface LearnedPattern {
  /** Unique identifier */
  id: string;
  /** Descriptive name */
  name: string;
  /** Pattern category */
  category: LearnedPatternCategory;
  /** When this pattern was extracted */
  extractedAt: string;
  /** Context where this pattern applies */
  context: string;
  /** Problem this pattern solves */
  problem: string;
  /** Solution/technique */
  solution: string;
  /** Code example if applicable */
  example?: string;
  /** Trigger conditions for using this pattern */
  triggerConditions: string[];
  /** Source session ID */
  sourceSession?: string;
  /** Confidence score (0-1) */
  confidence: number;
  /** Usage count */
  usageCount: number;
}

/**
 * Categories for learned patterns
 */
export type LearnedPatternCategory =
  | 'error_resolution'
  | 'user_corrections'
  | 'workarounds'
  | 'debugging_techniques'
  | 'project_specific'
  | 'performance_optimization'
  | 'refactoring';

/**
 * Configuration for pattern bridge
 */
export interface SkillPatternBridgeConfig {
  /** Storage path for learned patterns */
  storagePath: string;
  /** Minimum confidence to store */
  minConfidence: number;
  /** Maximum patterns to keep */
  maxPatterns: number;
  /** Enable privacy filtering */
  enablePrivacyFilter: boolean;
  /** Auto-consolidate similar patterns */
  autoConsolidate: boolean;
  /** Consolidation similarity threshold */
  consolidationThreshold: number;
}

/**
 * Default configuration
 */
export const DEFAULT_SKILL_PATTERN_BRIDGE_CONFIG: SkillPatternBridgeConfig = {
  storagePath: '~/.musubix/skills/learned',
  minConfidence: 0.6,
  maxPatterns: 500,
  enablePrivacyFilter: true,
  autoConsolidate: true,
  consolidationThreshold: 0.8,
};

/**
 * Pattern query context for retrieving relevant patterns
 */
export interface PatternQueryContext {
  /** Current error message if any */
  errorMessage?: string;
  /** Current file path */
  filePath?: string;
  /** Current language */
  language?: string;
  /** Keywords from user query */
  keywords?: string[];
  /** Maximum results to return */
  maxResults?: number;
}

/**
 * Pattern match result
 */
export interface PatternMatchResult {
  /** Matched pattern */
  pattern: LearnedPattern;
  /** Relevance score (0-1) */
  relevance: number;
  /** Match reason */
  matchReason: string;
}

/**
 * Pattern storage result
 */
export interface PatternStorageResult {
  /** Success flag */
  success: boolean;
  /** Stored pattern ID */
  patternId?: string;
  /** Was consolidated with existing */
  consolidated: boolean;
  /** Consolidated with pattern ID */
  consolidatedWith?: string;
  /** Error message if failed */
  error?: string;
}

/**
 * Interface for Skill-Pattern Bridge
 */
export interface SkillPatternBridge {
  /**
   * Store a learned pattern from learning-hooks
   */
  storeLearnedPattern(pattern: LearnedPattern): Promise<PatternStorageResult>;
  
  /**
   * Query patterns relevant to the given context
   */
  queryPatterns(context: PatternQueryContext): Promise<PatternMatchResult[]>;
  
  /**
   * Convert learned pattern to pattern-mcp format
   */
  convertToPattern(learned: LearnedPattern): Pattern;
  
  /**
   * Convert pattern-mcp format to learned pattern
   */
  convertFromPattern(pattern: Pattern): LearnedPattern;
  
  /**
   * Get pattern statistics
   */
  getStatistics(): Promise<PatternStatistics>;
  
  /**
   * Consolidate similar patterns
   */
  consolidatePatterns(): Promise<ConsolidationResult>;
}

/**
 * Pattern statistics
 */
export interface PatternStatistics {
  /** Total pattern count */
  totalPatterns: number;
  /** Patterns by category */
  byCategory: Record<LearnedPatternCategory, number>;
  /** Average confidence */
  averageConfidence: number;
  /** Total usage count */
  totalUsageCount: number;
  /** Most used pattern */
  mostUsed?: LearnedPattern;
  /** Recently added count (last 7 days) */
  recentlyAdded: number;
}

/**
 * Consolidation result
 */
export interface ConsolidationResult {
  /** Patterns merged */
  mergedCount: number;
  /** Patterns remaining */
  remainingCount: number;
  /** Merge details */
  merges: Array<{
    sourceId: string;
    targetId: string;
    similarity: number;
  }>;
}
