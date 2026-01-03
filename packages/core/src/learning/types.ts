/**
 * Learning Module Types
 *
 * Type definitions for the self-learning system
 *
 * @see REQ-LEARN-001 - Feedback Collection
 * @see REQ-LEARN-002 - Pattern Extraction
 * @module @musubix/core/learning
 */

/**
 * Feedback type indicating user response to generated artifacts
 */
export type FeedbackType = 'accept' | 'reject' | 'modify';

/**
 * Artifact types that can receive feedback
 */
export type ArtifactType = 'requirement' | 'design' | 'code' | 'test';

/**
 * Pattern categories for classification
 */
export type PatternCategory = 'code' | 'design' | 'requirement' | 'test';

/**
 * Pattern action types
 */
export type PatternActionType = 'prefer' | 'avoid' | 'suggest';

/**
 * Pattern source indicating how the pattern was created
 */
export type PatternSource = 'auto' | 'manual';

/**
 * Context information for feedback
 * @see REQ-LEARN-001 - Context attachment
 */
export interface FeedbackContext {
  /** Project name or identifier */
  project: string;
  /** Programming language (if applicable) */
  language?: string;
  /** Framework being used (if applicable) */
  framework?: string;
  /** Additional tags for categorization */
  tags: string[];
}

/**
 * User feedback on generated artifacts
 * @see REQ-LEARN-001 - Feedback Collection
 */
export interface Feedback {
  /** Unique identifier */
  id: string;
  /** Timestamp of feedback */
  timestamp: Date;
  /** Type of feedback */
  type: FeedbackType;
  /** Type of artifact receiving feedback */
  artifactType: ArtifactType;
  /** ID of the artifact */
  artifactId: string;
  /** Context information */
  context: FeedbackContext;
  /** Optional reason for the feedback */
  reason?: string;
  /** Original content (for modify type) */
  original?: string;
  /** Modified content (for modify type) */
  modified?: string;
}

/**
 * Pattern trigger conditions
 */
export interface PatternTrigger {
  /** Context matching conditions */
  context: Record<string, string>;
  /** Additional conditions as expressions */
  conditions: string[];
}

/**
 * Pattern action to take when triggered
 */
export interface PatternAction {
  /** Type of action */
  type: PatternActionType;
  /** Action content/template */
  content: string;
}

/**
 * Learned pattern from feedback analysis
 * @see REQ-LEARN-002 - Pattern Extraction
 */
export interface LearnedPattern {
  /** Unique identifier */
  id: string;
  /** Human-readable pattern name */
  name: string;
  /** Category of the pattern */
  category: PatternCategory;
  /** Trigger conditions */
  trigger: PatternTrigger;
  /** Action to take */
  action: PatternAction;
  /** Confidence score (0.0 - 1.0) */
  confidence: number;
  /** Number of times this pattern was observed */
  occurrences: number;
  /** Last time the pattern was used */
  lastUsed: Date;
  /** Creation timestamp */
  createdAt: Date;
  /** How the pattern was created */
  source: PatternSource;
}

/**
 * Learning statistics
 */
export interface LearningStats {
  /** Total feedback count */
  totalFeedback: number;
  /** Feedback by type */
  feedbackByType: Record<FeedbackType, number>;
  /** Total pattern count */
  totalPatterns: number;
  /** Patterns by category */
  patternsByCategory: Record<PatternCategory, number>;
  /** Average confidence score */
  averageConfidence: number;
  /** Last learning update */
  lastUpdate: Date;
}

/**
 * Pattern match result
 */
export interface PatternMatch {
  /** Matched pattern */
  pattern: LearnedPattern;
  /** Match score (0.0 - 1.0) */
  matchScore: number;
  /** Matched context keys */
  matchedKeys: string[];
}

/**
 * Learning engine configuration
 */
export interface LearningConfig {
  /** Minimum occurrences to create pattern (default: 3) */
  patternThreshold: number;
  /** Days before decay starts (default: 30) */
  decayDays: number;
  /** Decay rate per period (default: 0.1) */
  decayRate: number;
  /** Minimum confidence to keep pattern (default: 0.1) */
  minConfidence: number;
  /** Storage path for learning data */
  storagePath: string;
}

/**
 * Default learning configuration
 */
export const DEFAULT_LEARNING_CONFIG: LearningConfig = {
  patternThreshold: 3,
  decayDays: 30,
  decayRate: 0.1,
  minConfidence: 0.1,
  storagePath: 'storage/learning',
};
