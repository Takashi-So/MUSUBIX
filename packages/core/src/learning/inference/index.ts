/**
 * Advanced Inference Module
 *
 * @module learning/inference
 * @description OWL 2 RL推論、Datalog統合、説明生成
 * @requirements REQ-ONTO-010, REQ-ONTO-011, REQ-ONTO-012, REQ-ONTO-013, REQ-ONTO-014
 */

// Types
export type {
  OWL2RLRuleType,
  Triple,
  OWL2RLRule,
  DatalogAtom,
  DatalogRule,
  DatalogTerm,
  AppliedRule,
  InferenceResult,
  InferenceExplanation,
  InferenceProgress,
  InferenceStats,
  IReasoner,
  IExplainer,
  IProgressReporter,
  ProgressCallback,
} from './types.js';

export { NAMESPACES } from './types.js';

// OWL 2 RL Reasoner
export { OWL2RLReasoner, OWL2RL_RULES } from './owl2rl-reasoner.js';

// Datalog Engine
export { DatalogEngine } from './datalog-engine.js';

// Inference Explainer
export { InferenceExplainer } from './inference-explainer.js';

// Progress Reporter
export {
  ProgressReporter,
  ConsoleProgressReporter,
  SilentProgressReporter,
} from './progress-reporter.js';
export type { ProgressPhase, ProgressReporterOptions } from './progress-reporter.js';

// Context Analyzer (REQ-REC-001)
export {
  ContextAnalyzer,
  levenshteinDistance,
  levenshteinSimilarity,
  DEFAULT_SCORING_WEIGHTS,
} from './context-analyzer.js';
export type {
  AnalyzableEntity,
  RelatedEntity,
  RelevanceScoreBreakdown,
  RelationshipType,
  ScoringWeights,
  ContextAnalyzerOptions,
  EntityRepository,
  ContextAnalyzerEvents,
} from './context-analyzer.js';

// Pattern Recommender (REQ-REC-002)
export { PatternRecommender } from './pattern-recommender.js';
export type {
  RecommendablePattern,
  PatternCategory,
  RecommendationContext,
  PatternRecommendation,
  MatchFactor,
  FeedbackType,
  PatternFeedback,
  PatternRecommenderOptions,
  PatternRepository,
  PatternRecommenderEvents,
} from './pattern-recommender.js';
