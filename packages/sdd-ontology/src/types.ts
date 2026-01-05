/**
 * @fileoverview SDD Ontology type definitions
 * @traceability REQ-SDD-ONTO-001
 */

/**
 * Ontology module metadata
 */
export interface OntologyModule {
  id: string;
  name: string;
  namespace: string;
  version: string;
  description: string;
  dependencies: string[];
  filePath: string;
}

/**
 * EARS requirement types
 */
export type EarsPatternType =
  | 'ubiquitous'
  | 'event-driven'
  | 'state-driven'
  | 'unwanted'
  | 'optional';

/**
 * EARS requirement structure
 */
export interface EarsRequirement {
  id: string;
  pattern: EarsPatternType;
  trigger?: string;
  condition?: string;
  system: string;
  response: string;
  priority: 'P0' | 'P1' | 'P2';
}

/**
 * C4 diagram level
 */
export type C4Level = 'context' | 'container' | 'component' | 'code';

/**
 * C4 element structure
 */
export interface C4Element {
  id: string;
  level: C4Level;
  name: string;
  type: string;
  description: string;
  technology?: string;
  parent?: string;
  relationships: C4Relationship[];
}

/**
 * C4 relationship
 */
export interface C4Relationship {
  target: string;
  description: string;
  technology?: string;
}

/**
 * Traceability link types
 */
export type TraceLinkType =
  | 'satisfies'
  | 'implements'
  | 'tests'
  | 'derives-from'
  | 'refines';

/**
 * Traceability link
 */
export interface TraceLink {
  source: string;
  target: string;
  type: TraceLinkType;
  rationale?: string;
}

/**
 * Validation result
 */
export interface ValidationResult {
  valid: boolean;
  errors: ValidationError[];
  warnings: ValidationWarning[];
}

/**
 * Validation error
 */
export interface ValidationError {
  code: string;
  message: string;
  location?: string;
}

/**
 * Validation warning
 */
export interface ValidationWarning {
  code: string;
  message: string;
  suggestion?: string;
}

/**
 * Supported languages for i18n
 */
export type SupportedLanguage = 'en' | 'ja';

/**
 * Localized string
 */
export interface LocalizedString {
  en: string;
  ja?: string;
}
