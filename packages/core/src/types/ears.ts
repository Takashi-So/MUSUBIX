/**
 * EARS (Easy Approach to Requirements Syntax) Type Definitions
 * 
 * @packageDocumentation
 * @module types/ears
 * 
 * @see REQ-RA-001 - EARS Validation
 * @see DES-MUSUBIX-001 Section 5.1 - EARSValidator
 */

import type { ID, Timestamp, Priority, Confidence, Violation } from './common.js';

// ============================================================================
// EARS Requirement Types
// ============================================================================

/**
 * EARS requirement pattern types
 */
export type EARSPattern = 
  | 'ubiquitous'
  | 'event-driven'
  | 'state-driven'
  | 'unwanted'
  | 'optional';

/**
 * EARS requirement structure
 */
export interface EARSRequirement {
  /** Requirement identifier */
  id: ID;
  /** EARS pattern type */
  pattern: EARSPattern;
  /** Requirement text */
  text: string;
  /** Parsed components */
  components: EARSComponents;
  /** Priority */
  priority: Priority;
  /** Source document */
  source?: string;
  /** Related requirements */
  relatedTo?: ID[];
  /** Metadata */
  metadata?: EARSMetadata;
}

/**
 * EARS components based on pattern
 */
export interface EARSComponents {
  /** Trigger condition (for event-driven) */
  trigger?: string;
  /** Precondition/state (for state-driven) */
  precondition?: string;
  /** System name */
  system: string;
  /** Action/behavior */
  action: string;
  /** Optional feature flag (for optional) */
  feature?: string;
  /** Unwanted behavior (for unwanted) */
  unwanted?: string;
  /** Response to unwanted */
  response?: string;
}

/**
 * EARS metadata
 */
export interface EARSMetadata {
  /** Creation timestamp */
  createdAt: Timestamp;
  /** Last update timestamp */
  updatedAt: Timestamp;
  /** Author */
  author?: string;
  /** Version */
  version?: string;
  /** Tags */
  tags?: string[];
}

// ============================================================================
// EARS Validation Types
// ============================================================================

/**
 * EARS validation result
 */
export interface EARSValidationResult {
  /** Whether requirement is valid */
  valid: boolean;
  /** Detected pattern */
  pattern?: EARSPattern;
  /** Parsed components */
  components?: EARSComponents;
  /** Validation violations */
  violations: EARSViolation[];
  /** Validation confidence */
  confidence: Confidence;
  /** Suggestions for improvement */
  suggestions: string[];
}

/**
 * EARS-specific violation
 */
export interface EARSViolation extends Violation {
  /** EARS-specific violation type */
  earsType: EARSViolationType;
  /** Expected pattern */
  expectedPattern?: EARSPattern;
  /** Missing component */
  missingComponent?: keyof EARSComponents;
}

/**
 * EARS violation types
 */
export type EARSViolationType =
  | 'missing-pattern'
  | 'incomplete-syntax'
  | 'ambiguous-requirement'
  | 'missing-actor'
  | 'missing-action'
  | 'invalid-trigger'
  | 'invalid-precondition';

// ============================================================================
// EARS Pattern Templates
// ============================================================================

/**
 * EARS pattern templates for generation
 */
export const EARS_TEMPLATES: Record<EARSPattern, string> = {
  ubiquitous: 'The [system] shall [action].',
  'event-driven': 'WHEN [trigger], the [system] shall [action].',
  'state-driven': 'WHILE [precondition], the [system] shall [action].',
  unwanted: 'IF [unwanted behavior], THEN the [system] shall [response].',
  optional: 'WHERE [feature is supported], the [system] shall [action].',
} as const;

/**
 * EARS pattern keywords for detection
 */
export const EARS_KEYWORDS: Record<EARSPattern, string[]> = {
  ubiquitous: ['shall'],
  'event-driven': ['when', 'upon', 'after', 'as soon as'],
  'state-driven': ['while', 'during', 'if', 'unless'],
  unwanted: ['if', 'then', 'shall not', 'must not'],
  optional: ['where', 'when configured', 'when enabled'],
} as const;

// ============================================================================
// Ontology Mapping Types
// ============================================================================

/**
 * Ontology mapping for requirements
 * @see REQ-RA-002
 */
export interface OntologyMapping {
  /** Requirement ID */
  requirementId: ID;
  /** Mapped concepts */
  concepts: OntologyConcept[];
  /** Relationships */
  relationships: OntologyRelationship[];
  /** Mapping confidence */
  confidence: Confidence;
}

/**
 * Ontology concept
 */
export interface OntologyConcept {
  /** Concept identifier */
  id: ID;
  /** Concept name */
  name: string;
  /** Concept type */
  type: ConceptType;
  /** Properties */
  properties: Record<string, unknown>;
}

/**
 * Concept types
 */
export type ConceptType =
  | 'actor'
  | 'system'
  | 'action'
  | 'constraint'
  | 'quality'
  | 'data';

/**
 * Ontology relationship
 */
export interface OntologyRelationship {
  /** Source concept ID */
  sourceId: ID;
  /** Target concept ID */
  targetId: ID;
  /** Relationship type */
  type: RelationshipType;
  /** Relationship properties */
  properties?: Record<string, unknown>;
}

/**
 * Relationship types
 */
export type RelationshipType =
  | 'performs'
  | 'uses'
  | 'constrains'
  | 'produces'
  | 'consumes'
  | 'depends-on'
  | 'part-of';
