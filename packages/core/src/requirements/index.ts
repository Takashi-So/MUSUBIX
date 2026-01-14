/**
 * Requirements Module
 *
 * Provides tools for requirements gathering, analysis, and clarification.
 *
 * @module requirements
 */

// Context clarification
export * from './clarifying-questions.js';
export * from './context-analyzer.js';

// Requirements decomposition
export * from './decomposer.js';

// Related requirements finder
// Note: RelationshipType is also exported from types/index.js
// We use selective re-exports to avoid conflicts
export {
  RelatedRequirementsFinder,
  createRelatedRequirementsFinder,
  type AnalyzableRequirement,
  type RelatedRequirement,
  type SearchResult,
  type RequirementCluster,
  type RelatedFinderConfig,
  type SimilarityAlgorithm,
  DEFAULT_FINDER_CONFIG,
  // Rename to avoid conflict with types/index.js
  type RelationshipType as RequirementRelationshipType,
} from './related-finder.js';
